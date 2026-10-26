"""C2 rule family (FP-04/30/32/34).

SAF source-path gating, power-user battery-optimisation exemption, deprecated
lock-screen setting namespace, export directory + SQLite sidecar cleanup.

Every rule binds a concrete target object (method / compat implementation /
builder variable) and evaluates the proposition on the JDK AST
(javaparse.facts_for) or the Kotlin PSI facts (helpers_C2.kt_facts_for).
Regex/string search is only used to locate manifest permission lines and to
classify already-parsed argument text -- never to prove a control-flow claim.

verify(rule_id, source_inputs, target_binding, rule_config) -> observation dict.
"""
import re
import time

from helpers_C2 import (call_args, calls_in, functions_index, iter_nodes,
                        java_facts_for as facts_for, kt_facts_for,
                        resolve_function, walk_with_path)

CHECKER = 'rules_C2.verify'


def _obs(observation, scope, evidence, reason, start):
    return {'observation': observation, 'scope': scope, 'evidence': evidence,
            'reason': reason, 'duration_s': round(time.perf_counter() - start, 4)}


def _kt_functions(facts):
    out = []

    def walk(decls, cls):
        for d in decls:
            if d.get('kind') == 'FUN':
                out.append((cls, d))
            elif d.get('kind') in ('CLASS', 'OBJECT'):
                walk(d.get('members') or [], d.get('name') or '')

    walk(facts.get('declarations') or [], None)
    return out


def _manifest_permissions(path, wanted):
    """Return (declared_permissions, matched) from the manifest's uses-permission lines."""
    if path is None:
        return [], []
    p = path
    text = p.read_text(errors='replace') if hasattr(p, 'read_text') else ''
    declared = re.findall(r'<uses-permission[^>]*android:name="([^"]+)"', text)
    return declared, [w for w in wanted if w in declared]


# --------------------------------------------------------------- FP-04 SAF

def _saf_source_gate(rule_id, inputs, binding, cfg):
    start = time.perf_counter()
    files = inputs['kotlin_files']
    methods = list(binding['methods'])
    dialog = cfg['dialog_call']
    guarded_ops = set(cfg['guarded_ops'])
    src_pat = re.compile(cfg['source_arg_regex'])
    evidence = []
    facts = []
    for p in files:
        f = kt_facts_for(p)
        facts.append((p, f))
        evidence.append({'file': str(p), 'sha256': f.get('_source_sha256', ''),
                         'parse_ok': f.get('parse_ok')})
        if not f.get('parse_ok'):
            return _obs('UNKNOWN', rule_id, evidence, 'KOTLIN_PARSE_FAILED', start)

    declared, matched = _manifest_permissions(inputs.get('manifest'), cfg['read_permissions'])
    evidence.append({'manifest': str(inputs.get('manifest')), 'declared_permissions': declared,
                     'read_capable_permissions': matched})
    perm_ok = bool(matched)

    found = {}
    for p, f in facts:
        for cls, fn in _kt_functions(f):
            if fn['name'] in methods and fn['name'] not in found:
                found[fn['name']] = (str(p), cls, fn)

    hits, legacy, wrong_arg = [], [], []
    for name in methods:
        if name not in found:
            continue
        path, cls, fn = found[name]
        for call in calls_in(fn.get('body')):
            cname = call.get('name')
            if cname == cfg.get('legacy_dialog_call', 'handleSAFDialog'):
                legacy.append({'file': path, 'method': name, 'line': call.get('line'),
                               'args': call_args(call)})
            if cname != dialog:
                continue
            args = call_args(call)
            lam = call.get('lambda')
            ops = sorted({c['name'] for c in calls_in(lam)}) if lam else []
            gated = sorted(set(ops) & guarded_ops)
            rec = {'file': path, 'method': name, 'line': call.get('line'),
                   'dialog': cname, 'args': args, 'lambda_ops': ops,
                   'guarded_ops_in_lambda': gated}
            if not any(src_pat.match(a.strip()) for a in args):
                wrong_arg.append(rec)
                continue
            if not gated:
                continue
            hits.append(rec)

    evidence.append({'bound_methods_found': {k: {'file': v[0], 'class': v[1],
                                                 'line': v[2].get('line')}
                                             for k, v in found.items()},
                     'missing_bound_methods': [m for m in methods if m not in found],
                     'saf_gate_hits': hits,
                     'saf_calls_on_non_source_arg': wrong_arg,
                     'legacy_dialog_calls_ignored': legacy})
    scope = 'SAF SDK30 authorization gate applied to a source-path delete/move/copy operation'

    if hits and perm_ok:
        return _obs('PRESENT', scope, evidence,
                    'SOURCE_PATH_OPERATION_WRAPPED_IN_SAF_SDK30_DIALOG_WHILE_READ_PERMISSION_DECLARED',
                    start)
    if hits and not perm_ok:
        return _obs('UNKNOWN', scope, evidence,
                    'SAF_GATE_FOUND_BUT_READ_PERMISSION_NOT_DECLARED_PRECONDITION_UNMET', start)
    if not found:
        return _obs('UNKNOWN', scope, evidence, 'NO_BOUND_METHOD_FOUND', start)
    return _obs('ABSENT', scope, evidence,
                'NO_SAF_SDK30_GATE_ON_SOURCE_PATH_OPERATIONS', start)


# ------------------------------------------------- FP-30 battery optimisation

def _is_start_call(call, cfg):
    name = call.get('name')
    if name not in cfg['start_call_names']:
        return False
    if name == 'setState':
        return any(cfg['start_arg_marker'] in a for a in call_args(call))
    return True


def _is_battery_prompt(call, cfg):
    """A prompt must actually surface the exemption UI/intent, not merely query it."""
    name = call.get('name') or ''
    hay = ' '.join([call.get('receiver') or '', call.get('callee') or ''] + call_args(call))
    action = any(s in hay for s in cfg['intent_actions'])
    dialog = any(s in hay for s in cfg['prompt_classes'])
    return (name in cfg['prompt_calls'] and (action or dialog)) or (
        action and name in ('startActivity', 'show', 'createTransactionAndShow'))


def _dominating_nodes(node, path):
    """Nodes evaluated before `node` on every path reaching it (ancestor blocks'
    preceding statements + enclosing IF conditions). Sibling WHEN entries are not
    included: they are alternatives, not predecessors."""
    out = []
    for i, anc in enumerate(path):
        child = path[i + 1] if i + 1 < len(path) else node
        parent = path[i - 1] if i > 0 else None
        if isinstance(anc, list):
            if isinstance(parent, dict) and parent.get('kind') == 'WHEN':
                continue
            for s in anc:
                if s is child:
                    break
                if isinstance(s, dict):
                    out.append(s)
        elif isinstance(anc, dict) and anc.get('kind') == 'IF':
            out.append(anc.get('cond'))
    return out


def _collect_symbols(node, idx, cfg, depth, seen, found):
    for call in calls_in(node):
        name = call.get('name') or ''
        rec = {'name': name, 'receiver': call.get('receiver') or '',
               'args': call_args(call), 'line': call.get('line')}
        if name in cfg['battery_query_calls']:
            found['query'].append(rec)
        if _is_battery_prompt(call, cfg):
            found['prompt'].append(rec)
        if depth >= cfg['follow_depth']:
            continue
        fn = resolve_function(idx, name, call.get('receiver') or '')
        if fn is None:
            continue
        key = (id(fn), name)
        if key in seen:
            continue
        seen.add(key)
        _collect_symbols(fn.get('body'), idx, cfg, depth + 1, seen, found)


def _battery_exemption_gate(rule_id, inputs, binding, cfg):
    start = time.perf_counter()
    facts = []
    evidence = []
    for p in inputs['kotlin_files']:
        f = kt_facts_for(p)
        facts.append(f)
        evidence.append({'file': str(p), 'sha256': f.get('_source_sha256', ''),
                         'parse_ok': f.get('parse_ok')})
        if not f.get('parse_ok'):
            return _obs('UNKNOWN', rule_id, evidence, 'KOTLIN_PARSE_FAILED', start)
    idx = functions_index(facts)
    start_name = binding['start_method']
    cands = [fn for f in facts for _, fn in _kt_functions(f) if fn['name'] == start_name]
    if len(cands) != 1:
        return _obs('UNKNOWN', rule_id, evidence, 'START_METHOD_NOT_UNIQUE_OR_MISSING', start)
    body = cands[0].get('body')

    start_node, start_path = None, None
    for node, path in walk_with_path(body):
        if node.get('kind') == 'CALL' and _is_start_call(node, cfg):
            start_node, start_path = node, path
            break
    if start_node is None:
        return _obs('UNKNOWN', rule_id, evidence, 'NO_START_CALL_IN_BOUND_METHOD', start)

    found = {'query': [], 'prompt': []}
    seen = set()
    for n in _dominating_nodes(start_node, start_path):
        _collect_symbols(n, idx, cfg, 0, seen, found)

    anywhere = {'query': [], 'prompt': []}
    _collect_symbols(body, idx, cfg, 0, set(), anywhere)
    elsewhere = []
    for f in facts:
        for cls, fn in _kt_functions(f):
            if fn['name'] == start_name:
                continue
            if any(c.get('name') == start_name for c in calls_in(fn.get('body'))):
                continue  # wrapper of the start path, not an unrelated method
            probe = {'query': [], 'prompt': []}
            _collect_symbols(fn.get('body'), idx, cfg, 0, set(), probe)
            if probe['query'] or probe['prompt']:
                elsewhere.append({'class': cls, 'method': fn['name'],
                                  'query': [x['name'] for x in probe['query']],
                                  'prompt': [x['name'] for x in probe['prompt']]})

    evidence.append({'start_method': start_name, 'start_call': start_node,
                     'start_line': start_node.get('line'),
                     'dominating_battery_query': found['query'],
                     'dominating_battery_prompt': found['prompt'],
                     'battery_calls_anywhere_in_method': anywhere,
                     'battery_calls_in_unrelated_methods_ignored': elsewhere})
    scope = 'power-user background proxy start path handling battery-optimisation exemption'

    if found['query'] and found['prompt']:
        return _obs('ABSENT', scope, evidence,
                    'BATTERY_OPTIMISATION_QUERIED_AND_USER_PROMPTED_BEFORE_START', start)
    if anywhere['query'] or anywhere['prompt']:
        return _obs('PRESENT', scope, evidence,
                    'BATTERY_OPTIMISATION_HANDLING_NOT_BEFORE_START', start)
    return _obs('PRESENT', scope, evidence,
                'POWER_USER_START_NEVER_CHECKS_OR_PROMPTS_BATTERY_OPTIMISATION', start)


# --------------------------------------------------- FP-32 deprecated setting

def _jcall_name(inv):
    sel = inv.get('select') or {}
    if sel.get('kind') in ('MEMBER_SELECT', 'IDENTIFIER'):
        return sel.get('name')
    return None


def _jcall_receiver(inv):
    sel = inv.get('select') or {}
    return sel.get('receiver') if sel.get('kind') == 'MEMBER_SELECT' else None


def _expr_text(node):
    if not isinstance(node, dict):
        return ''
    k = node.get('kind') or ''
    if k.endswith('LITERAL'):
        v = str(node.get('value'))
        return f'"{v}"' if k == 'STRING_LITERAL' else v
    if k == 'IDENTIFIER':
        return node.get('name', '')
    if k == 'MEMBER_SELECT':
        return f"{_expr_text(node.get('receiver'))}.{node.get('name')}"
    if k == 'METHOD_INVOCATION':
        return f"{_expr_text(node.get('select'))}({','.join(_expr_text(a) for a in node.get('args') or [])})"
    if k == 'NEW_CLASS':
        return f"new {node.get('type')}({','.join(_expr_text(a) for a in node.get('args') or [])})"
    if k == 'VARIABLE':
        return f"{node.get('type', '')} {node.get('name', '')}".strip()
    return node.get('text', '')


def _methods(facts, name):
    return [m for m in facts.get('methods', []) if m.get('name') == name and m.get('has_body')]


def _method(facts, name):
    ms = _methods(facts, name)
    return ms[0] if len(ms) == 1 else None


def _all_java_locals(body):
    out = {}
    for n in iter_nodes(body):
        if n.get('kind') == 'VARIABLE':
            out[n.get('name')] = n
    return out


def _lockscreen_facet(inputs, binding, cfg):
    path = inputs['java_file']
    facts = facts_for(path)
    ev = [{'file': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok'), 'parser': facts.get('parser')}]
    if not facts.get('parse_ok'):
        return 'UNKNOWN', ev, 'JAVA_PARSE_FAILED'
    ms = _methods(facts, binding['method'])
    if not ms:
        return 'UNKNOWN', ev, 'TARGET_METHOD_NOT_UNIQUE_OR_MISSING'
    key = cfg['setting_key']
    reads = []
    for m in ms:
        for node, anc in walk_with_path(m['body']):
            if node.get('kind') != 'METHOD_INVOCATION':
                continue
            args_text = [_expr_text(a) for a in node.get('args') or []]
            if not any(key in a for a in args_text):
                continue
            recv = _expr_text(_jcall_receiver(node))
            conds = [a['cond'].get('text') or _expr_text(a['cond']) for a in anc
                     if isinstance(a, dict) and a.get('kind') == 'IF'
                     and isinstance(a.get('cond'), dict)]
            # the migrated setting is the KEY constant namespace, not the getter receiver:
            # fixed code keeps Settings.System.getInt but passes Settings.Secure.<KEY>.
            key_arg = next((a for a in args_text if key in a), '')
            ns = (cfg['right_namespace'] if key_arg.startswith(cfg['right_namespace'] + '.')
                  else cfg['wrong_namespace'] if key_arg.startswith(cfg['wrong_namespace'] + '.')
                  else None)
            reads.append({'callee': _jcall_name(node), 'key_arg': key_arg, 'namespace': ns,
                          'getter_namespace': recv, 'args': args_text,
                          'enclosing_conditions': conds,
                          'method': m.get('name'), 'line': None})
    ev.append({'method': binding['method'], 'lock_pattern_reads': reads,
               'legacy_namespace': cfg['wrong_namespace'],
               'migrated_namespace': cfg['right_namespace']})
    wrong = [r for r in reads if r['namespace'] == cfg['wrong_namespace']]
    right = [r for r in reads if r['namespace'] == cfg['right_namespace']]
    if wrong:
        return 'PRESENT', ev, 'LOCK_PATTERN_READ_FROM_DEPRECATED_SETTINGS_SYSTEM'
    if right:
        return 'ABSENT', ev, 'LOCK_PATTERN_READ_FROM_SETTINGS_SECURE'
    return 'UNKNOWN', ev, 'NO_LOCK_PATTERN_SETTING_READ_IN_BOUND_METHOD'


def _customtabs_facet(inputs, binding, cfg):
    path = inputs['java_file']
    facts = facts_for(path)
    ev = []
    if not facts.get('parse_ok'):
        return 'UNKNOWN', ev, 'JAVA_PARSE_FAILED'
    ms = _methods(facts, binding.get('view_method', 'view'))
    if not ms:
        return 'UNKNOWN', ev, 'VIEW_METHOD_NOT_UNIQUE_OR_MISSING'
    deprecated, migrated, names = [], [], set()
    for m in ms:
        locals_ = _all_java_locals(m['body'])
        builders = [n for n in locals_.values() if cfg['builder_type'] in (n.get('type') or '')]
        names |= {n.get('name') for n in builders}
        for node in iter_nodes(m['body']):
            if node.get('kind') != 'METHOD_INVOCATION':
                continue
            recv = _jcall_receiver(node)
            if not (recv and recv.get('kind') == 'IDENTIFIER'
                    and recv.get('name') in {n.get('name') for n in builders}):
                continue
            cname = _jcall_name(node)
            if cname in cfg['deprecated_setters']:
                deprecated.append(cname)
            if cname in cfg['migrated_setters']:
                migrated.append(cname)
    if not names:
        return 'UNKNOWN', ev, 'NO_CUSTOMTABS_BUILDER_IN_VIEW'
    ev.append({'method': binding.get('view_method', 'view'), 'builder_vars': sorted(names),
               'deprecated_setters': deprecated, 'migrated_setters': migrated})
    if deprecated:
        return 'PRESENT', ev, 'CUSTOMTABS_DEPRECATED_SETTERS_IN_USE'
    if migrated:
        return 'ABSENT', ev, 'CUSTOMTABS_MIGRATED_TO_COLOR_SCHEME_PARAMS_AND_SHARE_STATE'
    return 'UNKNOWN', ev, 'CUSTOMTABS_BUILDER_CONFIGURATION_NOT_CLASSIFIED'


def _deprecated_lockscreen_setting(rule_id, inputs, binding, cfg):
    start = time.perf_counter()
    primary, pev, preason = _lockscreen_facet(inputs, binding, cfg)
    secondary, sev, sreason = _customtabs_facet(inputs, binding, cfg)
    evidence = [{'facet': 'lock_pattern_setting_namespace', 'result': primary,
                 'reason': preason, 'detail': pev},
                {'facet': 'customtabs_deprecated_setters', 'result': secondary,
                 'reason': sreason, 'detail': sev}]
    scope = ('lock-screen setting namespace used by isSecure + deprecated CustomTabs setters in view')
    if 'PRESENT' in (primary, secondary):
        return _obs('PRESENT', scope, evidence,
                    'DEPRECATED_OR_MIGRATED_API_IN_USE:' + ','.join(
                        f for f, r in (('lock_pattern_setting', primary),
                                       ('customtabs_setters', secondary)) if r == 'PRESENT'), start)
    if primary == 'ABSENT' and secondary == 'ABSENT':
        return _obs('ABSENT', scope, evidence, 'BOTH_FACETS_MIGRATED', start)
    return _obs('UNKNOWN', scope, evidence,
                f'FACET_UNDECIDED:primary={primary},secondary={secondary}', start)


# ------------------------------------------- FP-34 export path + db cleanup

def _names_in(expr):
    return [_jcall_name(n) for n in iter_nodes(expr) if n.get('kind') == 'METHOD_INVOCATION'
            and _jcall_name(n)]


def _export_path_facet(inputs, binding, cfg):
    ev = []
    deck = facts_for(inputs['deck_picker'])
    if not deck.get('parse_ok'):
        return 'UNKNOWN', ev, 'DECKPICKER_PARSE_FAILED'
    ms = _methods(deck, binding['entry_method'])
    if not ms:
        return 'UNKNOWN', ev, 'EXPORT_ENTRY_METHOD_NOT_FOUND'
    local = None
    for m in ms:
        local = _all_java_locals(m['body']).get(binding['export_dir_var'])
        if local is not None:
            break
    if local is None:
        return 'UNKNOWN', ev, 'EXPORT_DIR_LOCAL_NOT_FOUND'
    init = local.get('init')
    call_names = _names_in(init)
    init_text = _expr_text(init)
    ev.append({'method': binding['entry_method'], 'export_dir_var': binding['export_dir_var'],
               'init_expr': init_text, 'calls': call_names})
    if cfg['dispatch_call'] in call_names:
        ev.append({'dispatch': cfg['dispatch_call'],
                   'detail': 'export directory chosen through API-dispatched compat implementation'})
        facet = 'PRESENT'
        reason = 'EXPORT_PATH_SELECTED_BY_API_DISPATCH'
    elif any(n in call_names for n in cfg['external_roots']) or any(
            n in init_text for n in cfg['external_roots']):
        facet = 'ABSENT'
        reason = 'EXPORT_PATH_FIXED_UNDER_USER_VISIBLE_EXTERNAL_ROOT'
    elif any(n in call_names for n in cfg['internal_roots']):
        facet = 'PRESENT'
        reason = 'EXPORT_PATH_UNDER_APP_INTERNAL_STORAGE'
    else:
        facet = 'UNKNOWN'
        reason = 'EXPORT_PATH_ROOT_NOT_CLASSIFIED'

    impls = []
    for p in inputs.get('compat_files', []):
        f = facts_for(p)
        if not f.get('parse_ok'):
            impls.append({'file': str(p), 'parse_ok': False})
            continue
        impl = _method(f, cfg['dispatch_call'])
        if impl is None:
            declared = [m for m in f.get('methods', [])
                        if m.get('name') == cfg['dispatch_call']]
            impls.append({'file': str(p),
                          'impl': 'declared_without_body' if declared else None,
                          'note': ('abstract declaration only' if declared
                                   else 'no getExportPath declaration')})
            continue
        ret = [n for n in iter_nodes(impl.get('body')) if n.get('kind') == 'RETURN']
        root = [_expr_text(r.get('expr')) for r in ret]
        internal = any(any(x in t for x in cfg['internal_roots']) for t in root)
        impls.append({'file': str(p), 'impl': 'present', 'returns': root,
                      'internal_storage': internal})
        if internal:
            facet = 'PRESENT'
            reason = 'COMPAT_IMPLEMENTATION_WRITES_TO_APP_INTERNAL_STORAGE'
    ev.append({'compat_implementations': impls})
    return facet, ev, reason


def _resolve_db_target(arg, locals_):
    text = _expr_text(arg)
    if any(s in text for s in ('.anki2', '.db2')):
        return text
    if arg.get('kind') == 'IDENTIFIER':
        loc = locals_.get(arg.get('name'))
        if loc is not None:
            init = _expr_text(loc.get('init'))
            if any(s in init for s in ('.anki2', '.db2')):
                return init
    if arg.get('kind') == 'NEW_CLASS':
        for a in arg.get('args') or []:
            hit = _resolve_db_target(a, locals_)
            if hit:
                return hit
    return None


def _sqlite_cleanup_facet(inputs, binding, cfg):
    ev = []
    facts = facts_for(inputs['exporter'])
    if not facts.get('parse_ok'):
        return 'UNKNOWN', ev, 'EXPORTER_PARSE_FAILED'
    ms = _methods(facts, binding['exporter_method'])
    if not ms:
        return 'UNKNOWN', ev, 'EXPORTER_METHOD_NOT_FOUND'
    locals_ = {}
    for m in ms:
        locals_.update(_all_java_locals(m['body']))
    raw_delete, safe_delete = [], []
    for m in ms:
        for node in iter_nodes(m['body']):
            if node.get('kind') != 'METHOD_INVOCATION':
                continue
            cname = _jcall_name(node)
            recv = _jcall_receiver(node)
            if cname == 'delete' and recv and recv.get('kind') == 'NEW_CLASS':
                args = recv.get('args') or []
                target = _resolve_db_target(args[0], locals_) if args else None
                if target:
                    raw_delete.append({'line': node.get('line'), 'target': target,
                                       'call': 'File.delete'})
            if cname == 'deleteDatabase':
                args = node.get('args') or []
                target = _resolve_db_target(args[0], locals_) if args else None
                if target:
                    safe_delete.append({'line': node.get('line'), 'target': target,
                                        'call': _expr_text(node.get('select'))})
    ev.append({'method': binding['exporter_method'],
               'sqlite_db_locals': {k: _expr_text(v.get('init'))
                                    for k, v in locals_.items()
                                    if any(s in _expr_text(v.get('init'))
                                           for s in ('.anki2', '.db2'))},
               'raw_file_delete_on_db': raw_delete,
               'delete_database_calls': safe_delete})
    if raw_delete:
        return 'PRESENT', ev, 'SQLITE_INTERMEDIATE_FILE_REMOVED_WITH_BARE_FILE_DELETE'
    if safe_delete:
        return 'ABSENT', ev, 'SQLITE_INTERMEDIATE_FILE_REMOVED_VIA_DELETE_DATABASE'
    return 'UNKNOWN', ev, 'NO_SQLITE_INTERMEDIATE_CLEANUP_IN_BOUND_METHOD'


def _export_and_db_cleanup(rule_id, inputs, binding, cfg):
    start = time.perf_counter()
    path_facet, pev, preason = _export_path_facet(inputs, binding, cfg)
    db_facet, dev, dreason = _sqlite_cleanup_facet(inputs, binding, cfg)
    evidence = [{'facet': 'export_path_consistency', 'result': path_facet,
                 'reason': preason, 'detail': pev},
                {'facet': 'sqlite_sidecar_cleanup', 'result': db_facet,
                 'reason': dreason, 'detail': dev}]
    scope = 'apkg export directory policy and SQLite intermediate-file cleanup'
    if 'PRESENT' in (path_facet, db_facet):
        return _obs('PRESENT', scope, evidence,
                    'EXPORT_DEFECT_PRESENT:' + ','.join(
                        f for f, r in (('export_path', path_facet),
                                       ('sqlite_cleanup', db_facet)) if r == 'PRESENT'), start)
    if path_facet == 'ABSENT' and db_facet == 'ABSENT':
        return _obs('ABSENT', scope, evidence, 'EXPORT_PATH_FIXED_AND_DB_CLEANED_BY_DELETE_DATABASE',
                    start)
    return _obs('UNKNOWN', scope, evidence,
                f'FACET_UNDECIDED:path={path_facet},cleanup={db_facet}', start)


CHECKERS = {
    'SAF_SOURCE_PATH_GATE_WITH_READ_PERMISSION': _saf_source_gate,
    'POWER_USER_BATTERY_OPT_EXEMPTION_GATE': _battery_exemption_gate,
    'DEPRECATED_LOCKSCREEN_SETTING_NAMESPACE': _deprecated_lockscreen_setting,
    'EXPORT_PATH_AND_SQLITE_SIDECAR_CLEANUP': _export_and_db_cleanup,
}


def verify(*args):
    """Accept both v5 styles: (rule_id, inputs, binding, cfg) and (inputs, binding, cfg)."""
    if len(args) == 4:
        rule_id, inputs, binding, cfg = args
    elif len(args) == 3:
        inputs, binding, cfg = args
        rule_id = cfg['rule_id']
    else:
        raise TypeError('verify expects 3 or 4 positional arguments')
    return CHECKERS[rule_id](rule_id, inputs, binding, cfg)
