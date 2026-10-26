"""C3 rule family: cache reuse, scan count, UI-refresh work.

Each rule answers its proposition with a deterministic operation count on a fixed
model input - never with elapsed time:

  * INVARIANT_DERIVED_SET_RECOMPUTED_PER_CALL
        rebuilds of a process-invariant derived set per target-method call
        (1 per call when re-derived locally, 0 after warm-up when lazily cached).
  * VISITOR_PER_NODE_FULLTEXT_RESCAN
        full-text scan passes per document (one per visited Text node vs one per
        document), evaluated on a fixed synthetic document.
  * BATCH_RENDER_PER_ITEM_UI_REFRESH
        UI refresh callbacks per search result set (per rendered card vs constant).

verify(rule_id, source_inputs, target_binding, rule_config) -> observation dict.
Checkers never receive reference states, fix diffs or expected answers.
"""
import json
import re
import time

import helpers_c3 as h3
from javaparse import facts_for
from rules_webview import _invocations, _iter_nodes, _obs

RULE_VERSION = 'v5.rule.c3.1'
LOOPS = {'FOR_LOOP', 'ENHANCED_FOR_LOOP', 'WHILE_LOOP', 'DO_WHILE_LOOP'}


# --------------------------------------------------------------------------- #
# shared Java-AST utilities
# --------------------------------------------------------------------------- #
def _walk_depth(node, depth=0):
    """Yield (node, enclosing_loop_depth) for every AST dict node."""
    if isinstance(node, dict):
        yield node, depth
        d = depth + 1 if node.get('kind') in LOOPS else depth
        for k, v in node.items():
            if k in ('kind', 'text', 'value', 'name', 'type', 'start_line', 'end_line'):
                continue
            yield from _walk_depth(v, d)
    elif isinstance(node, list):
        for v in node:
            yield from _walk_depth(v, depth)


def _identifiers(node):
    out = set()
    for n, _ in _walk_depth(node):
        k = n.get('kind')
        if k == 'IDENTIFIER' and n.get('name'):
            out.add(n['name'])
        elif k == 'VARIABLE' and n.get('name'):
            out.add(n['name'])
        elif k == 'ASSIGNMENT':
            v = n.get('variable') or {}
            if v.get('name'):
                out.add(v['name'])
    return out


def _accessor_name(symbol):
    return 'get' + symbol[0].upper() + symbol[1:]


def _find_method(facts, name, symbols=()):
    """Overloads by name; disambiguate on the symbol (or its accessor) reference."""
    cands = [m for m in facts['methods'] if m['name'] == name and m.get('has_body')]
    if len(cands) <= 1 or not symbols:
        return cands
    hit = [m for m in cands if _identifiers(m['body']) & set(symbols)]
    return hit if hit else cands


def _call_name(call):
    return (call.get('select') or {}).get('name') or ''


def _call_receiver(call):
    return (call.get('select') or {}).get('receiver') or {}


def _var_inits(method):
    out = {}
    for n, _ in _walk_depth(method['body']):
        if n.get('kind') == 'VARIABLE' and n.get('name'):
            out[n['name']] = json.dumps(n.get('init') or {})
    return out


# --------------------------------------------------------------------------- #
# C3-1  invariant derived set rebuilt on every call
# --------------------------------------------------------------------------- #
def check_invariant_set_recompute(inputs, binding, cfg):
    scope = 'derived-set rebuild count per call (cache reuse)'
    start = time.perf_counter()
    path = inputs['java_file']
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', scope, ev, 'JAVA_PARSE_FAILED', time.perf_counter() - start)

    symbol = binding['collection']
    factory = (binding.get('invariant_source') or {}).get('factory', 'getDefault')
    enumerate_name = (binding.get('invariant_source') or {}).get('enumerate', 'getCategories')
    lines = [(m['start_line'], m['end_line']) for m in facts['methods']]
    src = path.read_text(errors='replace')
    fields = h3.field_decls(h3.blank_comments_strings(src), lines)

    def derivation(m):
        """Per-method re-derivation facts for the target collection symbol."""
        b = m['body']
        decls = [n for n, _ in _walk_depth(b)
                 if n.get('kind') == 'VARIABLE' and n.get('name') == symbol]
        constructions = [d for d in decls if (d.get('init') or {}).get('kind') == 'NEW_CLASS']
        adds, reads, inv = [], [], []
        inits = _var_inits(m)
        for n, d in _walk_depth(b):
            if n.get('kind') == 'METHOD_INVOCATION':
                if _call_name(n) in ('add', 'addAll') and _call_receiver(n).get('name') == symbol:
                    adds.append({'call': _call_name(n), 'loop_depth': d})
                if symbol in json.dumps(n.get('args') or []):
                    reads.append({'call': _call_name(n), 'loop_depth': d})
            if n.get('kind') != 'ENHANCED_FOR_LOOP':
                continue
            expr = n.get('expr') or {}
            name = _call_name(expr) if expr.get('kind') == 'METHOD_INVOCATION' else ''
            recv = (_call_receiver(expr).get('name') or '') if expr else ''
            if name != enumerate_name or not recv:
                continue
            rooted = (factory in inits.get(recv, '')
                      or factory in (fields.get(recv) or {}).get('init', ''))
            inv.append({'receiver': recv, 'rooted_at_factory': rooted, 'factory': factory})
        return {'constructions': constructions, 'adds': adds, 'reads': reads, 'invariant_loops': inv}

    cands = _find_method(facts, binding['method'], [symbol, _accessor_name(symbol)])
    if len(cands) != 1:
        return _obs('UNKNOWN', scope, ev, f'TARGET_METHOD_MATCHES_{len(cands)}_OVERLOADS',
                    time.perf_counter() - start)
    method = cands[0]
    body = method['body']
    ev.append({'method': {'name': method['name'], 'owner': method.get('owner'),
                          'start_line': method.get('start_line'),
                          'end_line': method.get('end_line')}})

    d0 = derivation(method)
    rebuild = (bool(d0['constructions']) and bool(d0['adds'])
               and any(a['loop_depth'] >= 1 for a in d0['adds']))

    # lazy cache: field of the same name + null-guarded getter elsewhere in the file
    field = fields.get(symbol)
    getters = []
    for m in facts['methods']:
        if not m.get('has_body') or m is method:
            continue
        guarded = False
        for n, _ in _walk_depth(m['body']):
            if n.get('kind') != 'IF' or not n.get('then'):
                continue
            cond = n.get('cond') or {}
            text = (cond.get('text') or '') + ' ' + (cond.get('name') or '')
            kind = cond.get('kind', '')
            if symbol in text and 'null' in text and (
                    '==' in text or '!=' in text or kind.startswith(('EQUAL', 'NOT_EQUAL'))):
                if any(x.get('kind') == 'ASSIGNMENT' and (x.get('variable') or {}).get('name') == symbol
                       for x, _ in _walk_depth(n['then'])):
                    guarded = True
        returns_symbol = any(
            n.get('kind') == 'RETURN' and (n.get('expr') or {}).get('name') == symbol
            for n, _ in _walk_depth(m['body']))
        if guarded and returns_symbol:
            getters.append({'name': m['name'], 'start_line': m.get('start_line'),
                            'invariant_rooted': any(x['rooted_at_factory']
                                                    for x in derivation(m)['invariant_loops'])})
    called = {_call_name(c) for c in _invocations(body)}
    used_getters = [g for g in getters if g['name'] in called]
    cache_ok = (bool(used_getters) and not d0['constructions']
                and all(g['invariant_rooted'] for g in used_getters))

    model = dict(cfg.get('operation_model') or {})
    cats = int(model.get('categories', 16))
    types = int(model.get('types_per_category', 24))
    blank_src = h3.blank_comments_strings(src)
    m_lo, m_hi = method.get('start_line'), method.get('end_line')
    decl_line = h3.locate_line(blank_src, re.escape(symbol) + r'\s*=\s*new', m_lo, m_hi)
    add_line = (h3.locate_line(blank_src, r'\.add\s*\(', decl_line, m_hi)
                if (d0['adds'] and decl_line) else None)
    ev.append({
        'symbol': symbol,
        'local_construction': {
            'declarations': len(d0['constructions']),
            'element_adds': d0['adds'],
            'reads': d0['reads'],
            'decl_line': decl_line,
            'add_line': add_line,
            'method_span': [m_lo, m_hi]},
        'cached_field': field,
        'lazy_getters': getters,
        'target_calls_getter': [{'name': g['name']} for g in used_getters],
        'invariant_source_loops': d0['invariant_loops'],
    })

    if not d0['invariant_loops'] and not getters:
        return _obs('UNKNOWN', scope, ev, 'NO_INVARIANT_DERIVATION_OR_CACHE_PATH',
                    time.perf_counter() - start)

    elements = cats * types
    if rebuild:
        if not any(x['rooted_at_factory'] for x in d0['invariant_loops']):
            return _obs('UNKNOWN', scope, ev, 'DERIVATION_SOURCE_NOT_PROCESS_INVARIANT',
                        time.perf_counter() - start)
        ev.append({'operation_model': {
            'model_input': {'categories': cats, 'types_per_category': types},
            'rebuilds_per_call_steady_state': 0 if cache_ok else 1,
            'set_allocations_per_call': 0 if cache_ok else 1,
            'element_ops_per_call': 0 if cache_ok else elements,
            'note': 'fixed input sizes only; deterministic counts, not timing'}})
        reason = 'LOCAL_REBUILD_PER_CALL' + ('_PLUS_CACHE' if cache_ok else '')
        return _obs('PRESENT', scope, ev, reason, time.perf_counter() - start)
    if used_getters and not cache_ok:
        return _obs('UNKNOWN', scope, ev, 'CACHE_NOT_DERIVED_FROM_INVARIANT_SOURCE',
                    time.perf_counter() - start)
    if cache_ok:
        ev.append({'operation_model': {
            'model_input': {'categories': cats, 'types_per_category': types},
            'rebuilds_per_call_steady_state': 0,
            'set_allocations_per_call': 0,
            'element_ops_per_call': 0,
            'warmup_rebuilds_per_process': 1,
            'note': 'fixed input sizes only; deterministic counts, not timing'}})
        return _obs('ABSENT', scope, ev, 'DERIVED_SET_SERVED_FROM_LAZY_FIELD_CACHE',
                    time.perf_counter() - start)
    return _obs('UNKNOWN', scope, ev, 'DERIVATION_AND_CACHE_BOTH_ABSENT',
                time.perf_counter() - start)


# --------------------------------------------------------------------------- #
# C3-2  per-node full-text rescan in a document visitor
# --------------------------------------------------------------------------- #
def check_visitor_per_node_rescan(inputs, binding, cfg):
    scope = 'full-text scan passes per document (visitor dispatch granularity)'
    start = time.perf_counter()
    path = inputs['source_file']
    text = path.read_text(errors='replace')
    blank = h3.blank_comments_strings(text)
    idx = h3.LineIndex(blank)
    ev = [{'path': str(path), 'language': cfg.get('language', 'kotlin')}]
    if cfg.get('language', 'kotlin') == 'kotlin' and 'fun ' not in blank:
        return _obs('UNKNOWN', scope, ev, 'NOT_A_KOTLIN_SOURCE', time.perf_counter() - start)

    spans = h3.type_spans(blank)
    cls = next((s for s in spans if s['name'] == binding['class']), None)
    if cls is None:
        return _obs('UNKNOWN', scope, ev, 'VISITOR_CLASS_NOT_FOUND', time.perf_counter() - start)
    header = ' '.join(blank[cls['start']:cls['body_open']].split())
    ev.append({'visitor_class': {'name': cls['name'], 'line': idx.line_of(cls['start']),
                                 'header': header}})
    base = cfg.get('visitor_base')
    if base and base not in header:
        return _obs('UNKNOWN', scope, ev, 'CLASS_IS_NOT_A_VISITOR_SUBTYPE', time.perf_counter() - start)

    doc_types = {t.split('.')[-1] for t in cfg.get('document_types', ['Document'])}
    matcher_call = binding.get('matcher_call', 'matcher')
    matcher_symbol = cfg.get('matcher_symbol', '')
    accumulator = binding.get('accumulator', 'builder')

    callbacks = []
    for f in h3.find_functions(blank, cls['body_open'] + 1, cls['end']):
        if f['name'] != binding['method']:
            continue
        if h3.type_depth(blank, cls['body_open'], f['start']) != 0:
            continue
        ptype = (f['params'][0]['type'] if f['params'] else '')
        hits = []
        for c in h3.calls(blank, f['body_open'], f['end']):
            if c['name'] != matcher_call:
                continue
            if matcher_symbol and matcher_symbol not in c['receiver']:
                continue
            if not re.search(r'\b%s\s*\.\s*text\s*\(\s*\)' % re.escape(accumulator), c['args_raw']):
                continue
            hits.append({'line': idx.line_of(c['offset']), 'call': c['chain'],
                         'arg': c['args_raw']})
        if not hits:
            continue
        simple = ptype.split('<')[0].split('.')[-1]
        callbacks.append({'method': f['name'], 'param': (f['params'][0] if f['params'] else {}),
                          'param_type': simple, 'line': idx.line_of(f['start']),
                          'end_line': idx.line_of(f['end']),
                          'scan_sites': hits,
                          'dispatch_level': 'document' if simple in doc_types else 'node'})

    registrations = [{'line': idx.line_of(c['offset']), 'call': c['chain'], 'arg': c['args_raw']}
                     for c in h3.calls(blank, 0, len(blank))
                     if c['name'] == 'accept' and binding['class'] in c['args_raw']]
    ev.append({'scan_callbacks': callbacks, 'traversal_registrations': registrations})

    if not callbacks:
        return _obs('UNKNOWN', scope, ev, 'NO_FULLTEXT_SCAN_IN_VISITOR_CALLBACK',
                    time.perf_counter() - start)
    if cfg.get('require_registration', True) and not registrations:
        return _obs('UNKNOWN', scope, ev, 'VISITOR_NEVER_REGISTERED_IN_SOURCE',
                    time.perf_counter() - start)

    fixed = dict(cfg.get('fixed_input') or {})
    nodes_in = int(fixed.get('text_nodes', 40))
    chars = int(fixed.get('chars_per_node', 60))
    per_node = [c for c in callbacks if c['dispatch_level'] == 'node']
    doc_level = [c for c in callbacks if c['dispatch_level'] == 'document']
    if per_node:
        passes = nodes_in
        scanned = chars * nodes_in * (nodes_in + 1) // 2
        reason = 'SCAN_CALLBACK_DISPATCHED_PER_TEXT_NODE'
    else:
        passes = 1
        scanned = chars * nodes_in
        reason = 'SCAN_CALLBACK_DISPATCHED_ONCE_PER_DOCUMENT'
    single = chars * nodes_in
    ev.append({'operation_model': {
        'fixed_input': {'text_nodes': nodes_in, 'chars_per_node': chars},
        'scan_passes_per_document': passes,
        'chars_scanned_per_document': scanned,
        'single_pass_chars': single,
        'work_ratio_vs_single_pass': round(scanned / single, 2) if single else None,
        'note': 'deterministic pass/char counts on a fixed document model, not timing'}})
    return _obs('PRESENT' if per_node else 'ABSENT', scope, ev, reason,
                time.perf_counter() - start)


# --------------------------------------------------------------------------- #
# C3-3  per-item UI refresh driven by a batch render task
# --------------------------------------------------------------------------- #
def _methods_in_span(facts, line_lo, line_hi, name=None):
    out = []
    for m in facts['methods']:
        if m['start_line'] < line_lo or m['end_line'] > line_hi:
            continue
        if name is not None and m['name'] != name:
            continue
        out.append(m)
    return out


def _refresh_calls(method, names):
    return [c for c in _invocations(method['body']) if _call_name(c) in names]


def _refresh_count_resolved(method, facts, refresh_name, depth=1):
    """Refresh calls in `method` plus one level of same-file no-arg helper calls."""
    n = len([c for c in _invocations(method['body']) if _call_name(c) == refresh_name])
    if depth <= 0:
        return n
    for c in _invocations(method['body']):
        if c.get('args'):
            continue
        name = _call_name(c)
        for m in facts['methods']:
            if m['name'] == name and m.get('has_body') and m is not method:
                n += _refresh_count_resolved(m, facts, refresh_name, depth - 1)
                break
    return n


def check_batch_render_per_item_refresh(inputs, binding, cfg):
    scope = 'UI refresh callbacks per search result set (batch render)'
    start = time.perf_counter()
    ui, task = inputs['ui_file'], inputs['task_file']
    facts_ui, facts_task = facts_for(ui), facts_for(task)
    ev = [{'ui_file': str(ui), 'sha256': facts_ui.get('_source_sha256', ''),
           'parse_ok': facts_ui.get('parse_ok')},
          {'task_file': str(task), 'sha256': facts_task.get('_source_sha256', ''),
           'parse_ok': facts_task.get('parse_ok')}]
    if not facts_ui.get('parse_ok') or not facts_task.get('parse_ok'):
        return _obs('UNKNOWN', scope, ev, 'JAVA_PARSE_FAILED', time.perf_counter() - start)

    blank = h3.blank_comments_strings(ui.read_text(errors='replace'))
    idx = h3.LineIndex(blank)
    method_lines = [(m['start_line'], m['end_line']) for m in facts_ui['methods']]
    fields = h3.field_decls(blank, method_lines)
    refresh_name = binding.get('refresh_method', 'notifyDataSetChanged')

    hspan = h3.anonymous_span(blank, binding['handler_field'])
    if hspan is None:
        return _obs('UNKNOWN', scope, ev, 'HANDLER_FIELD_NOT_ANONYMOUS_LISTENER',
                    time.perf_counter() - start)
    lo, hi = idx.line_of(hspan['start']), idx.line_of(hspan['end'])
    cbs = _methods_in_span(facts_ui, lo, hi, binding['callback'])
    if len(cbs) != 1:
        return _obs('UNKNOWN', scope, ev, f'SEARCH_CALLBACK_MATCHES_{len(cbs)}',
                    time.perf_counter() - start)
    cb = cbs[0]
    ev.append({'search_complete_handler': {'field': binding['handler_field'],
                                           'type': hspan['type'], 'lines': [lo, hi],
                                           'callback': cb['name'],
                                           'callback_start_line': cb['start_line']}})

    launches = []
    launch_base = idx.offset_of(cb['start_line']) or 0
    launch_lines = [idx.line_of(launch_base + m.start()) for m in
                    re.finditer(r'\blaunchDeckTask\s*\(', blank[
                        launch_base:(idx.offset_of(cb['end_line'] + 1) or len(blank))])]
    launch_i = 0
    for c in _invocations(cb['body']):
        if _call_name(c) != 'launchDeckTask':
            continue
        args = c.get('args') or []
        if args and args[0].get('name') == binding['render_task_const']:
            launches.append({'listener': args[1].get('name') if len(args) > 1 else None,
                             'batch_expr': json.dumps(args[2]) if len(args) > 2 else None,
                             'line': launch_lines[launch_i] if launch_i < len(launch_lines) else None})
            launch_i += 1
    ev.append({'batch_task_launches_from_search_complete': launches})

    per_item = None
    if launches:
        listener = launches[0]['listener']
        lspan = h3.anonymous_span(blank, listener) if listener else None
        if lspan is None:
            return _obs('UNKNOWN', scope, ev, 'LISTENER_FIELD_NOT_ANONYMOUS',
                        time.perf_counter() - start)
        llo, lhi = idx.line_of(lspan['start']), idx.line_of(lspan['end'])
        prog = _methods_in_span(facts_ui, llo, lhi, binding.get('progress_callback', 'onProgressUpdate'))
        if len(prog) != 1:
            return _obs('UNKNOWN', scope, ev, f'PROGRESS_CALLBACK_MATCHES_{len(prog)}',
                        time.perf_counter() - start)
        refresh = _refresh_calls(prog[0], {refresh_name})
        per_item = {'listener': listener, 'progress_callback': prog[0]['name'],
                    'progress_line': prog[0]['start_line'],
                    'refresh_calls': len(refresh)}
    ev.append({'listener_progress_refresh': per_item})

    # per-item publishProgress in the render task body (drives onProgressUpdate)
    render_task = [m for m in facts_task['methods']
                   if m['name'] == binding.get('render_method', 'doInBackgroundRenderBrowserQA')
                   and m.get('has_body')]
    publish = []
    for m in render_task:
        for n, d in _walk_depth(m['body']):
            if n.get('kind') == 'METHOD_INVOCATION' and _call_name(n) == 'publishProgress':
                publish.append({'method': m['name'], 'loop_depth': d,
                                'start_line': m.get('start_line')})
    ev.append({'per_item_progress_publish': publish})

    inline = [m for m in facts_task['methods']
              if m['name'] == binding.get('inline_method', 'doInBackgroundSearchCards')
              and m.get('has_body')]
    inline_ev = []
    for m in inline:
        render_calls = [n for n, d in _walk_depth(m['body'])
                        if n.get('kind') == 'METHOD_INVOCATION'
                        and _call_name(n) == binding.get('inline_render_call', 'updateSearchItemQA')]
        inline_ev.append({'method': m['name'], 'line': m.get('start_line'),
                          'inline_render_calls': len(render_calls),
                          'refresh_calls': len(_refresh_calls(m, {refresh_name}))})
    ev.append({'inline_render_path': inline_ev})

    const = fields.get(binding.get('batch_bound_const', 'MIN_CARDS_TO_RENDER'))
    bound = None
    if const and re.fullmatch(r'-?\d+', const['init'] or ''):
        bound = int(const['init'])
    ev.append({'batch_bound_constant': const, 'batch_bound_value': bound})

    refresh_in_callback = _refresh_count_resolved(cb, facts_ui, refresh_name)
    model = dict(cfg.get('operation_model') or {})
    cards = int(model.get('cards', 1200))
    ev.append({'operation_model': {
        'fixed_input': {'search_result_cards': cards},
        'batch_bound': bound,
        'per_item_refresh_callbacks': (min(cards, bound) if (per_item and bound) else 0),
        'constant_refresh_in_callback_path': refresh_in_callback,
        'ui_refreshes_per_search': ((min(cards, bound) if (per_item and bound) else 0) * 1
                                    + refresh_in_callback),
        'scales_with_cards': bool(per_item),
        'note': 'deterministic callback counts on a fixed result-set size, not timing'}})

    chain_ok = bool(per_item and per_item['refresh_calls'] > 0
                    and any(p['loop_depth'] >= 1 for p in publish))
    if chain_ok:
        return _obs('PRESENT', scope, ev, 'PER_ITEM_UI_REFRESH_FROM_BATCH_RENDER_TASK',
                    time.perf_counter() - start)
    if launches:
        return _obs('ABSENT', scope, ev, 'BATCH_TASK_WITHOUT_PER_ITEM_UI_REFRESH',
                    time.perf_counter() - start)
    return _obs('ABSENT', scope, ev, 'NO_BATCH_RENDER_TASK_FROM_SEARCH_COMPLETE',
                time.perf_counter() - start)


CHECKERS = {
    'INVARIANT_DERIVED_SET_RECOMPUTED_PER_CALL': check_invariant_set_recompute,
    'VISITOR_PER_NODE_FULLTEXT_RESCAN': check_visitor_per_node_rescan,
    'BATCH_RENDER_PER_ITEM_UI_REFRESH': check_batch_render_per_item_refresh,
}


def verify(rule_id, source_inputs, target_binding, rule_config):
    return CHECKERS[rule_id](source_inputs, target_binding, rule_config)
