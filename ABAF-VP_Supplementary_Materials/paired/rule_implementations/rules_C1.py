"""C1 rule family: callback delivery, lifecycle, collection mutation, auth branch,
dependency binding.

verify(rule_id, source_inputs, target_binding, rule_config) -> observation dict.
All five rules run the SAME decision logic on both sides; bindings come from the
versioned v5 alignment record, never from the pair slot. Kotlin targets use the
structural parser in helpers_C1 (javac cannot parse Kotlin); Java targets use the
recovered JDK AST plus a condition parser for javac-normalized leaves.
"""
import hashlib
import json
import pathlib
import sys
import time

V5 = pathlib.Path(__file__).resolve().parents[1]
ROOT = V5.parents[2]
WS = ROOT / 'ABAF_VP_完整实验方案_2026-10-11/workspace'
SNAP = WS / 'p2_pair_selection/snapshots'

sys.path.insert(0, str(V5 / 'src'))
import helpers_C1 as H  # noqa: E402
from javaparse import facts_for  # noqa: E402


def _obs(observation, scope, evidence, reason, duration_s=0.0):
    return {'observation': observation, 'scope': scope, 'evidence': evidence,
            'reason': reason, 'duration_s': duration_s}


def _sha(p):
    p = pathlib.Path(p)
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None


def _read(p):
    return pathlib.Path(p).read_text()


def _invocations(node, out=None):
    if out is None:
        out = []
    for n in _iter_nodes(node):
        if n.get('kind') == 'METHOD_INVOCATION':
            out.append(n)
    return out


def _iter_nodes(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from _iter_nodes(v)
    elif isinstance(node, list):
        for v in node:
            yield from _iter_nodes(v)


# --------------------------------------------------------- 1 OAuth delivery

def _enhanced_for(node, out=None):
    if out is None:
        out = []
    for n in _iter_nodes(node):
        if n.get('kind') == 'ENHANCED_FOR_LOOP':
            out.append(n)
    return out


def check_oauth_callback_registry(inputs, binding, cfg):
    """Completion must be broadcast to every registered initiator listener.

    PRESENT: authorize() carries a one-shot listener and the completion path calls
    only that listener (no registry broadcast). ABSENT: the helper keeps a listener
    collection (add + iterate/notify) and the adapter invokes that broadcast.
    """
    start = time.perf_counter()
    helper_f = pathlib.Path(inputs['helper_file'])
    adapter_f = pathlib.Path(inputs['adapter_file'])
    helper = facts_for(helper_f)
    adapter = facts_for(adapter_f)
    ev = [{'file': str(helper_f), 'sha256': helper.get('_source_sha256', ''),
           'parse_ok': helper.get('parse_ok')},
          {'file': str(adapter_f), 'sha256': adapter.get('_source_sha256', ''),
           'parse_ok': adapter.get('parse_ok')}]
    if not helper.get('parse_ok') or not adapter.get('parse_ok'):
        return _obs('UNKNOWN', 'OAuth completion callback delivery', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    listener_type = cfg['listener_type']
    completion_calls = set(cfg['completion_calls'])

    # helper: listener registry = add-call on a collection + notify loop over it
    registry_collections, broadcast_methods, add_methods = set(), set(), set()
    authorize_param_types = []
    for m in helper['methods']:
        if not m.get('has_body'):
            continue
        if m['name'] == 'authorize':
            authorize_param_types = [p['type'] for p in m['params']]
        for call in _invocations(m['body']):
            sel = call.get('select') or {}
            if sel.get('name') == 'add':
                recv = (sel.get('receiver') or {}).get('name')
                if recv and (call.get('args') or []):
                    registry_collections.add(recv)
                    add_methods.add(m['name'])
        for loop in _enhanced_for(m['body']):
            src = (loop.get('expr') or {}).get('name')
            var = (loop.get('var') or {}).get('name')
            if not src:
                continue
            for call in _invocations(loop.get('body')):
                sel = call.get('select') or {}
                recv = (sel.get('receiver') or {}).get('name')
                if sel.get('name') in completion_calls and recv == var:
                    broadcast_methods.add(m['name'])
                    registry_collections.add(src)
    registry = bool(registry_collections and broadcast_methods)
    takes_listener = any(listener_type in (t or '') for t in authorize_param_types)
    ev.append({'helper_methods': [m['name'] for m in helper['methods']],
               'registry_collections': sorted(registry_collections),
               'add_methods': sorted(add_methods),
               'broadcast_methods': sorted(broadcast_methods),
               'authorize_param_types': authorize_param_types})

    # adapter: completion path delivery kind
    delivery = []
    for m in adapter['methods']:
        if not m.get('has_body'):
            continue
        for call in _invocations(m['body']):
            sel = call.get('select') or {}
            name = sel.get('name')
            recv = sel.get('receiver') or {}
            if name in completion_calls:
                delivery.append({'kind': 'single', 'method': m['name'],
                                 'owner': m.get('owner'), 'call': name,
                                 'receiver': recv.get('name')})
            elif name in broadcast_methods and recv.get('kind') == 'IDENTIFIER':
                delivery.append({'kind': 'broadcast', 'method': m['name'],
                                 'owner': m.get('owner'), 'call': name,
                                 'receiver': recv.get('name')})
    ev.append({'adapter_delivery': delivery})

    redirect_ok = None
    if inputs.get('redirect_file') and pathlib.Path(inputs['redirect_file']).exists():
        red = facts_for(inputs['redirect_file'])
        seq = []
        if red.get('parse_ok'):
            for m in red['methods']:
                if not m.get('has_body'):
                    continue
                for call in _invocations(m['body']):
                    name = (call.get('select') or {}).get('name')
                    if name in set(cfg.get('register_methods', [])) | {'authorize'}:
                        seq.append({'method': m['name'], 'call': name})
        redirect_ok = bool(seq)
        ev.append({'redirect_flow': seq})

    dur = time.perf_counter() - start
    kinds = {d['kind'] for d in delivery}
    if registry and kinds == {'broadcast'} and not takes_listener:
        return _obs('ABSENT', 'OAuth completion callback delivery', ev,
                    'REGISTRY_REGISTERS_AND_BROADCASTS_TO_ALL_LISTENERS', dur)
    if not registry and kinds == {'single'} and takes_listener:
        return _obs('PRESENT', 'OAuth completion callback delivery', ev,
                    'SINGLE_LISTENER_CAPTURED_AT_AUTHORIZE_NO_REGISTRY', dur)
    if registry and 'single' in kinds:
        return _obs('UNKNOWN', 'OAuth completion callback delivery', ev,
                    'REGISTRY_EXISTS_BUT_COMPLETION_STILL_TARGETS_SINGLE_LISTENER', dur)
    return _obs('UNKNOWN', 'OAuth completion callback delivery', ev,
                'CALLBACK_DELIVERY_SHAPE_NOT_DECIDABLE', dur)


# ------------------------------------------- 2 fragment transaction lifecycle

def _guard_polarity(toks, cond_range, cfg):
    """+1: condition true means committing is safe; -1: true means unsafe; 0 other."""
    node = H.parse_expr(toks, *cond_range)
    return _guard_node(toks, node, cfg)


def _guard_node(toks, node, cfg):
    k = node.get('kind')
    if k == 'unary' and node.get('op') == '!':
        v = _guard_node(toks, node['operand'], cfg)
        return -v
    if k == 'binary' and node.get('op') in ('&&', '||'):
        l = _guard_node(toks, node['left'], cfg)
        r = _guard_node(toks, node['right'], cfg)
        if node['op'] == '&&':
            return l if l == r else 0
        return l if l == r else 0
    if k != 'chain':
        return 0
    names = H.chain_names(node)
    calls = {s['name'] for s in node['suffixes'] if s['t'] == 'member'}
    if 'isAtLeast' in calls and any(g in names for g in cfg.get('guard_objects', [])):
        for s in node['suffixes']:
            if s['t'] == 'member' and s['name'] == 'isAtLeast':
                for a in s.get('args') or []:
                    arg = H.parse_expr(toks, *a['range'])
                    if any(st in H.chain_names(arg) for st in cfg.get('guard_states', [])):
                        return 1
        return 0
    if calls & set(cfg.get('blocking_calls', [])):
        return -1
    return 0


def _walk_kt_expr(toks, rng, guarded, ctx, env):
    node = H.parse_expr(toks, *rng)
    for chain in H.iter_chains(node):
        base = chain['base'].get('name') if chain['base'].get('kind') == 'name' else None
        stypes = [s['t'] for s in chain['suffixes']]
        if (base in ctx['commit_calls'] and stypes and stypes[0] in
                ('typeargs', 'call', 'lambda')):
            ctx['commits'].append({'call': base, 'guarded': guarded})
        for s in chain['suffixes']:
            if s['t'] == 'member' and s['name'] in ctx['commit_calls']:
                ctx['commits'].append({'call': s['name'], 'guarded': guarded})
            if s.get('lambda'):
                _walk_kt_block(toks, s['lambda']['body'], guarded, ctx, dict(env))


def _walk_kt_stmt(st, toks, guarded, ctx, env):
    k = st['kind']
    if k == 'block':
        _walk_kt_block(toks, st['range'], guarded, ctx, env)
    elif k == 'if':
        pol = _guard_polarity(toks, st['cond'], ctx['cfg'])
        _walk_kt_stmt(st['then'], toks, guarded or pol > 0, ctx, env)
        if st.get('else'):
            _walk_kt_stmt(st['else'], toks, guarded or pol < 0, ctx, env)
    elif k in ('while', 'for'):
        _walk_kt_stmt(st['body'], toks, guarded, ctx, env)
    elif k == 'try':
        for b in st['blocks']:
            _walk_kt_block(toks, b, guarded, ctx, env)
    elif k == 'expr':
        _walk_kt_expr(toks, st['expr'], guarded, ctx, env)
    elif k == 'val' and st.get('init'):
        _walk_kt_expr(toks, st['init'], guarded, ctx, env)


def _anti_guard_early_return(st, toks, cfg):
    if st['kind'] != 'if' or st.get('else'):
        return False
    then = st['then']
    only_return = (then['kind'] == 'return' or
                   (then['kind'] == 'block' and
                    [x['kind'] for x in H.block_stmts(toks, *then['range'])] in
                    (['return'], ['throw'])))
    return only_return and _guard_polarity(toks, st['cond'], cfg) < 0


def _walk_kt_block(toks, rng, guarded, ctx, env):
    for st in H.block_stmts(toks, *rng):
        _walk_kt_stmt(st, toks, guarded, ctx, env)
        if _anti_guard_early_return(st, toks, ctx['cfg']):
            guarded = True


def check_fragment_txn_lifecycle_guard(inputs, binding, cfg):
    """Fragment transactions in the target method must be dominated by a host
    lifecycle-state guard (RESUMED/STARTED or an early-return unsafe-state check)."""
    start = time.perf_counter()
    path = pathlib.Path(inputs['kt_file'])
    src = _read(path)
    toks = H.tokenize(src)
    ev = [{'file': str(path), 'sha256': _sha(path)}]
    fns = H.find_function(toks, binding['method'])
    if len(fns) != 1:
        return _obs('UNKNOWN', 'fragment transaction lifecycle guard', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING:%d' % len(fns),
                    time.perf_counter() - start)
    ctx = {'commit_calls': set(cfg['commit_calls']), 'commits': [], 'cfg': cfg}
    _walk_kt_block(toks, fns[0]['body'], False, ctx, {})
    ev.append({'method': binding['method'], 'start_line': fns[0]['start_line'],
               'commits': ctx['commits']})
    dur = time.perf_counter() - start
    if not ctx['commits']:
        return _obs('UNKNOWN', 'fragment transaction lifecycle guard', ev,
                    'NO_FRAGMENT_TRANSACTION_IN_TARGET_METHOD', dur)
    unguarded = [c for c in ctx['commits'] if not c['guarded']]
    if unguarded:
        return _obs('PRESENT', 'fragment transaction lifecycle guard', ev,
                    'TRANSACTION_COMMITTED_WITHOUT_HOST_LIFECYCLE_GUARD', dur)
    return _obs('ABSENT', 'fragment transaction lifecycle guard', ev,
                'ALL_TRANSACTIONS_DOMINATED_BY_LIFECYCLE_GUARD', dur)


# ---------------------------------------- 3 collection mutation in iteration

def _resolve_prefix(toks, chain, idx, env):
    base = chain['base']
    if base.get('kind') == 'name' and base.get('name') in env:
        d = dict(env[base['name']])
        d['chain'] = list(d['chain'])
    elif base.get('kind') == 'name':
        d = {'chain': [base['name']], 'snapshot': False, 'element': False}
    else:
        d = {'chain': [], 'snapshot': False, 'element': False}
    for j, s in enumerate(chain['suffixes'][:idx]):
        if s['t'] in ('member', 'ref'):
            d['chain'].append(s['name'])
            if s['name'] in env.get('__snapshot_calls__', ()):
                d['snapshot'] = True
        elif s['t'] == 'call':
            d['chain'].append('()')
            if d['chain'][-2:-1] and d['chain'][-2] in env.get('__snapshot_calls__', ()):
                d['snapshot'] = True
    return d


def _resolve_expr(toks, rng, env):
    node = H.parse_expr(toks, *rng)
    if node.get('kind') != 'chain':
        return None
    d = _resolve_prefix(toks, node, len(node['suffixes']), env)
    names = [s['name'] for s in node['suffixes'] if s['t'] == 'member']
    if names and names[-1] in ('next', 'element', 'first', 'firstOrNull'):
        d['element'] = True
    return d


def _walk_mut_block(toks, rng, ctx, env, in_iter):
    for st in H.block_stmts(toks, *rng):
        if st['kind'] == 'val' and st.get('init') and st.get('name'):
            d = _resolve_expr(toks, st['init'], env)
            if d:
                env[st['name']] = d
        _walk_mut_stmt(st, toks, ctx, env, in_iter)


def _walk_mut_stmt(st, toks, ctx, env, in_iter):
    k = st['kind']
    if k == 'block':
        _walk_mut_block(toks, st['range'], ctx, env, in_iter)
        return
    if k == 'val' and st.get('init'):
        d = _resolve_expr(toks, st['init'], env)
        child = dict(env)
        if st.get('name') and d:
            child[st['name']] = d
        _walk_mut_expr(toks, st['init'], ctx, child, in_iter)
        return
    if k == 'if':
        _walk_mut_expr(toks, st['cond'], ctx, env, in_iter)
        _walk_mut_stmt(st['then'], toks, ctx, env, in_iter)
        if st.get('else'):
            _walk_mut_stmt(st['else'], toks, ctx, env, in_iter)
        return
    if k == 'for':
        d = _resolve_expr(toks, st['iterable'], env) if st.get('iterable') else None
        child = dict(env)
        if st.get('var') and d:
            child[st['var']] = {'chain': d['chain'] + ['<element>'],
                                'snapshot': d['snapshot'], 'element': True}
        _walk_mut_stmt(st['body'], toks, ctx, child, True)
        return
    if k == 'while':
        _walk_mut_stmt(st['body'], toks, ctx, env, True)
        return
    if k == 'try':
        for b in st['blocks']:
            _walk_mut_block(toks, b, ctx, env, in_iter)
        return
    if k == 'expr':
        _walk_mut_expr(toks, st['expr'], ctx, env, in_iter)


def _walk_mut_expr(toks, rng, ctx, env, in_iter):
    node = H.parse_expr(toks, *rng)
    for chain in H.iter_chains(node):
        base = chain['base'].get('name') if chain['base'].get('kind') == 'name' else None
        for idx, s in enumerate(chain['suffixes']):
            name = s.get('name') if s['t'] == 'member' else None
            if name is not None:
                recv = _resolve_prefix(toks, chain, idx, env)
                if in_iter and name in ctx['mutation_calls']:
                    direct = (ctx['collection_member'] in recv['chain']
                              and not recv['element'])
                    element = recv.get('element') and ctx['collection_member'] in recv['chain']
                    if direct or element:
                        ctx['mutations'].append({
                            'call': name, 'line': None, 'snapshot': recv['snapshot'],
                            'element': bool(element), 'receiver_chain': recv['chain']})
            if s.get('lambda'):
                lam = s['lambda']
                recv = _resolve_prefix(toks, chain, idx, env)
                callee = name or base
                child = dict(env)
                if callee in ctx['scope_calls']:
                    for p in lam['params']:
                        child[p] = {'chain': recv['chain'], 'snapshot': recv['snapshot'],
                                    'element': False}
                else:
                    for p in lam['params']:
                        child[p] = {'chain': recv['chain'] + ['<element>'],
                                    'snapshot': recv['snapshot'], 'element': True}
                _walk_mut_block(toks, lam['body'], ctx, child, True)
            for a in s.get('args') or []:
                _walk_mut_expr(toks, a['range'], ctx, env, in_iter)


def check_collection_mutation_in_iteration(inputs, binding, cfg):
    """Deleting an element of a live collection during iteration (no snapshot)."""
    start = time.perf_counter()
    path = pathlib.Path(inputs['kt_file'])
    src = _read(path)
    toks = H.tokenize(src)
    ev = [{'file': str(path), 'sha256': _sha(path)}]
    fns = H.find_function(toks, binding['method'])
    if len(fns) != 1:
        return _obs('UNKNOWN', 'collection mutation during iteration', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING:%d' % len(fns),
                    time.perf_counter() - start)
    env = {'__snapshot_calls__': set(cfg['snapshot_calls'])}
    ctx = {'mutation_calls': set(cfg['mutation_calls']),
           'collection_member': cfg['collection_member'],
           'scope_calls': set(cfg.get('scope_calls', [])),
           'mutations': []}
    _walk_mut_block(toks, fns[0]['body'], ctx, env, False)
    ev.append({'method': binding['method'], 'start_line': fns[0]['start_line'],
               'mutations_in_iteration': ctx['mutations']})
    dur = time.perf_counter() - start
    if not ctx['mutations']:
        return _obs('ABSENT', 'collection mutation during iteration', ev,
                    'NO_MUTATION_OF_TARGET_COLLECTION_INSIDE_ITERATION', dur)
    if any(not m['snapshot'] for m in ctx['mutations']):
        return _obs('PRESENT', 'collection mutation during iteration', ev,
                    'LIVE_COLLECTION_MUTATED_WHILE_ITERATED', dur)
    return _obs('ABSENT', 'collection mutation during iteration', ev,
                'SNAPSHOT_COLLECTION_ITERATED_BEFORE_MUTATION', dur)


# ------------------------------------------- 4 input-type gate completeness

def _enum_constants(src):
    toks = H.tokenize(src)
    out = []
    for i, t in enumerate(toks):
        if t.kind == 'IDENT' and t.val == 'enum':
            j = i + 1
            while j < len(toks) and toks[j].val != '{':
                j += 1
            if j >= len(toks):
                return []
            e = H.match(toks, j)
            depth, cur = 0, []
            for k in range(j + 1, e):
                v = toks[k].val
                if v in '([{':
                    depth += 1
                elif v in ')]}':
                    depth -= 1
                elif depth == 0 and v in (',', ';'):
                    if cur:
                        out.append(cur[0])
                    cur = []
                    if v == ';':
                        break
                    continue
                if depth == 0 and toks[k].kind == 'IDENT' and not cur:
                    cur.append(v)
            if cur:
                out.append(cur[0])
            break
    return out


def _refs_var(node, var):
    if isinstance(node, dict):
        if node.get('k') == 'name' and var in node.get('path', []):
            return True
        if node.get('k') == 'call' and var in node.get('path', []):
            return True
        return any(_refs_var(v, var) for v in node.values())
    if isinstance(node, list):
        return any(_refs_var(v, var) for v in node)
    return False


def _required_input_var(activity):
    for m in activity['methods']:
        if m['name'] != 'onCreate' or not m.get('has_body'):
            continue
        for st in m['body']:
            if st.get('kind') != 'VARIABLE':
                continue
            for inv in _invocations(st.get('init')):
                for a in inv.get('args') or []:
                    if a.get('kind') == 'IDENTIFIER' and a.get('name') == 'EXTRA_REQUIRED_INPUT':
                        return st.get('name')
    return None


def _find_gate(activity):
    var = _required_input_var(activity)
    for m in activity['methods']:
        if m['name'] != 'onCreate' or not m.get('has_body'):
            continue
        for st in m['body']:
            if st.get('kind') != 'IF':
                continue
            then = st.get('then') or {}
            stmts = then.get('stmts', []) if then.get('kind') == 'BLOCK' else [then]
            if [s.get('kind') for s in stmts] != ['RETURN']:
                continue
            cond = _cond_text(st.get('cond'))
            node = H.parse_java_condition(cond)
            if var and _refs_var(node, var):
                return m, cond, node
    return None, None, None


def _cond_text(cond):
    if not cond:
        return ''
    if cond.get('kind') in ('PARENTHESIZED', 'UNARY', 'BINARY'):
        return cond.get('text', '')
    return cond.get('text', '')


def check_input_type_gate_completeness(inputs, binding, cfg):
    """The onCreate gate must admit every text-entry RequiredInputType."""
    start = time.perf_counter()
    act_f = pathlib.Path(inputs['activity_file'])
    par_f = pathlib.Path(inputs['parcel_file'])
    activity = facts_for(act_f)
    parcel = facts_for(par_f)
    ev = [{'file': str(act_f), 'sha256': activity.get('_source_sha256', ''),
           'parse_ok': activity.get('parse_ok')},
          {'file': str(par_f), 'sha256': parcel.get('_source_sha256', ''),
           'parse_ok': parcel.get('parse_ok')}]
    if not activity.get('parse_ok') or not parcel.get('parse_ok'):
        return _obs('UNKNOWN', 'input-type gate completeness', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    enum_types = _enum_constants(_read(par_f))
    ev.append({'enum': binding.get('enum'), 'enum_constants': enum_types})
    m, cond_text, cond = _find_gate(activity)
    if m is None:
        return _obs('UNKNOWN', 'input-type gate completeness', ev,
                    'NO_MTYPE_GATE_IN_ONCREATE', time.perf_counter() - start)

    # resolve isTextInput()-style predicates from the parcel source switch
    pred_cache = {}

    def resolve_call(path, type_name):
        name = path[-1] if path else ''
        if name not in pred_cache:
            meth = next((x for x in parcel['methods'] if x['name'] == name
                         and x.get('has_body')), None)
            if meth is None:
                pred_cache[name] = None
            else:
                pred_cache[name] = H.java_switch_case_map(
                    _read(par_f), meth['start_line'], meth['end_line'])
        mp = pred_cache[name]
        if not mp:
            return None
        if type_name in mp:
            return mp[type_name]
        return mp.get('default')

    required = list(cfg['text_input_types'])
    ev.append({'gate_condition': cond_text, 'required_text_types': required})
    vals = {t: H.eval_gate_expr(cond, t, resolve_call) for t in required}
    ev.append({'gate_truth_per_required_type': vals,
               'predicate_tables': {k: v for k, v in pred_cache.items() if v}})
    dur = time.perf_counter() - start
    if any(v is None for v in vals.values()):
        return _obs('UNKNOWN', 'input-type gate completeness', ev,
                    'GATE_PREDICATE_NOT_EVALUABLE_FOR_ALL_REQUIRED_TYPES', dur)
    if all(v is False for v in vals.values()):
        return _obs('ABSENT', 'input-type gate completeness', ev,
                    'GATE_ADMITS_ALL_TEXT_INPUT_TYPES', dur)
    return _obs('PRESENT', 'input-type gate completeness', ev,
                'GATE_REJECTS_TEXT_INPUT_TYPES:' + ','.join(t for t, v in vals.items() if v),
                dur)


# --------------------------------------------- 5 variant DI binding closure

def _dsl_definitions(toks):
    """Koin `single/factory/scoped/viewModel` definitions with their type key."""
    out = []
    for c in H.find_calls(toks, {'single', 'factory', 'scoped', 'viewModel'}):
        typers = [s['names'] for s in c['suffixes'] if s['t'] == 'typeargs']
        args = [a for s in c['suffixes'] if s['t'] in ('member', 'call')
                for a in (s.get('args') or [])]
        lam = next((s['lambda'] for s in c['suffixes'] if s.get('lambda')), None)
        out.append({'call': c['base'].get('name'), 'type_args': typers[0] if typers else [],
                    'args': args, 'lambda': lam, 'line': None})
    return out


def _arg_true(toks, args, name):
    for a in args:
        if a.get('name') != name:
            continue
        seg = toks[a['range'][0]:a['range'][1]]
        if any(t.val == 'true' for t in seg):
            return True
    return False


def _injector_type(seg, injector):
    """(is_injector_call, explicit_type_or_None) for one argument token slice."""
    for i, t in enumerate(seg):
        if t.kind != 'IDENT' or t.val != injector:
            continue
        if i > 0 and seg[i - 1].val in ('.', '?.'):
            continue
        if i + 1 < len(seg) and seg[i + 1].val == '(':
            return True, None
        if i + 1 < len(seg) and seg[i + 1].val == '<':
            j, names, depth = i + 1, [], 0
            while j < len(seg):
                if seg[j].val == '<':
                    depth += 1
                    if depth > 1:
                        names.append('<')
                elif seg[j].val == '>':
                    depth -= 1
                    if depth == 0:
                        return True, ''.join(names)
                    names.append('>')
                else:
                    names.append(seg[j].val)
                j += 1
    return False, None


def _calls_in_range(toks, rng, names):
    node = H.parse_expr(toks, *rng)
    out = []
    for ch in H.iter_chains(node):
        base = ch['base'].get('name')
        seq = [s['name'] for s in ch['suffixes'] if s['t'] == 'member']
        if base in names or (seq and seq[0] in names):
            out.append(ch)
    return out


def check_di_binding_completeness(inputs, binding, cfg):
    """An eagerly created consumer's injected dependency must have a binding in the
    variant's module graph (variant source set + common modules)."""
    start = time.perf_counter()
    consumer_f = pathlib.Path(inputs['consumer_file'])
    consumer_toks = H.tokenize(_read(consumer_f))
    ctor = H.class_primary_ctor_params(consumer_toks, cfg['consumer_class'])
    ev = [{'file': str(consumer_f), 'sha256': _sha(consumer_f),
           'consumer_ctor': ctor}]
    if ctor is None:
        return _obs('UNKNOWN', 'variant DI binding closure', ev,
                    'CONSUMER_CLASS_WITH_PRIMARY_CTOR_NOT_FOUND',
                    time.perf_counter() - start)
    consumer_types = {v.split('<')[0].strip(): k for k, v in ctor.items()}

    provided, required, problems = [], [], []
    for f in inputs['variant_files'] + inputs['common_module_files']:
        p = pathlib.Path(f)
        toks = H.tokenize(_read(p))
        for d in _dsl_definitions(toks):
            key = d['type_args'][0] if d['type_args'] else None
            provided.append({'file': str(p), 'key': key, 'call': d['call'],
                             'eager': _arg_true(toks, d['args'], cfg['eager_arg'])})
    provided_keys = {x['key'] for x in provided if x['key']}

    for f in inputs['common_module_files']:
        p = pathlib.Path(f)
        toks = H.tokenize(_read(p))
        for d in _dsl_definitions(toks):
            if not d['lambda'] or not _arg_true(toks, d['args'], cfg['eager_arg']):
                continue
            lam = d['lambda']
            for ch in _calls_in_range(toks, lam['body'], {cfg['consumer_class']}):
                for s in ch['suffixes']:
                    if s['t'] not in ('member', 'call'):
                        continue
                    for a in s.get('args') or []:
                        seg_toks = toks[a['range'][0]:a['range'][1]]
                        is_inj, explicit = _injector_type(seg_toks, cfg['injector'])
                        if not is_inj:
                            continue
                        if a.get('name') and a['name'] in ctor:
                            rtype = ctor[a['name']].split('<')[0].strip()
                        elif explicit:
                            rtype = explicit
                        else:
                            problems.append({'arg': a.get('name'),
                                             'reason': 'UNRESOLVED_TYPE'})
                            continue
                        required.append({'type': rtype, 'arg': a.get('name'),
                                         'consumer': cfg['consumer_class'],
                                         'eager': True, 'file': str(p)})
    ev.append({'provided_types': provided, 'required_types': required,
               'unresolved': problems})
    dur = time.perf_counter() - start
    if problems:
        return _obs('UNKNOWN', 'variant DI binding closure', ev,
                    'REQUIRED_TYPE_UNRESOLVED', dur)
    if not required:
        return _obs('ABSENT', 'variant DI binding closure', ev,
                    'NO_EAGER_INJECTED_DEPENDENCY_FOUND', dur)
    missing = [r for r in required if r['type'] not in provided_keys]
    if missing:
        return _obs('PRESENT', 'variant DI binding closure', ev,
                    'EAGER_CONSUMER_DEPENDENCY_NOT_BOUND:' + ','.join(
                        sorted({r['type'] for r in missing})), dur)
    return _obs('ABSENT', 'variant DI binding closure', ev,
                'ALL_EAGER_CONSUMER_DEPENDENCIES_BOUND', dur)


CHECKERS = {
    'OAUTH_CALLBACK_LISTENER_REGISTRY': check_oauth_callback_registry,
    'FRAGMENT_TXN_LIFECYCLE_GUARD': check_fragment_txn_lifecycle_guard,
    'COLLECTION_MUTATION_DURING_ITERATION': check_collection_mutation_in_iteration,
    'INPUT_TYPE_GATE_COMPLETENESS': check_input_type_gate_completeness,
    'DI_BINDING_CLOSURE_EAGER_CONSUMER': check_di_binding_completeness,
}


def verify(rule_id, source_inputs, target_binding, rule_config):
    return CHECKERS[rule_id](source_inputs, target_binding, rule_config)


# ------------------------------------------------------------- pair runs

RULE_VERSION = 'v5.rule.c1.1'
PAIR_SPECS = {
    'FP-01': {
        'task': 'FT-001', 'kind': 'REAL', 'rule_id': 'OAUTH_CALLBACK_LISTENER_REGISTRY',
        'binding': {'helper_class': 'OsmOAuthHelper',
                    'adapter_class': 'OsmOAuthAuthorizationAdapter'},
        'cfg': {'listener_type': 'OsmAuthorizationListener',
                'completion_calls': ['authorizationCompleted'],
                'register_methods': ['addListener']},
        'files': {
            'helper_file': 'OsmAnd/src/net/osmand/plus/osmedit/oauth/OsmOAuthHelper.java',
            'adapter_file': 'OsmAnd/src/net/osmand/plus/osmedit/oauth/OsmOAuthAuthorizationAdapter.java',
            'redirect_file': 'OsmAnd/src/net/osmand/plus/helpers/IntentHelper.java'},
    },
    'FP-08': {
        'task': 'FT-008', 'kind': 'REAL', 'rule_id': 'FRAGMENT_TXN_LIFECYCLE_GUARD',
        'binding': {'method': 'onSelectServer'},
        'cfg': {'commit_calls': ['replaceFragment', 'addFragment', 'commit', 'commitNow',
                                 'commitAllowingStateLoss'],
                'guard_objects': ['lifecycle', 'currentState'],
                'guard_states': ['RESUMED'],
                'blocking_calls': ['isStateSaved', 'isFinishing', 'isDestroyed']},
        'files': {'kt_file': 'app/src/main/java/org/jellyfin/mobile/fragment/WebViewFragment.kt'},
    },
    'FP-10': {
        'task': 'FT-010', 'kind': 'REAL', 'rule_id': 'COLLECTION_MUTATION_DURING_ITERATION',
        'binding': {'method': 'storeUserDevices'},
        'cfg': {'collection_member': 'devices',
                'mutation_calls': ['deleteOnCascade', 'deleteFromRealm', 'remove',
                                   'removeAt', 'removeAll'],
                'snapshot_calls': ['toTypedArray', 'toList', 'toMutableList', 'toSet',
                                   'toMutableSet', 'toCollection'],
                'scope_calls': ['let', 'also', 'run', 'apply']},
        'files': {'kt_file': 'matrix-sdk-android/src/main/java/org/matrix/android/sdk/internal/crypto/store/db/RealmCryptoStore.kt'},
    },
    'FP-31': {
        'task': 'FT-031', 'kind': 'REAL', 'rule_id': 'INPUT_TYPE_GATE_COMPLETENESS',
        'binding': {'method': 'onCreate', 'enum': 'RequiredInputType'},
        'cfg': {'text_input_types': ['BACKUP_CODE', 'NUMERIC_9X4', 'NUMERIC_9X4_AUTOCRYPT',
                                     'PASSPHRASE', 'PASSPHRASE_AUTH',
                                     'PASSPHRASE_SYMMETRIC']},
        'files': {'activity_file': 'OpenKeychain/src/main/java/org/sufficientlysecure/keychain/ui/PassphraseDialogActivity.java',
                  'parcel_file': 'OpenKeychain/src/main/java/org/sufficientlysecure/keychain/service/input/RequiredInputParcel.java'},
    },
    'FP-33': {
        'task': 'FT-033', 'kind': 'REAL', 'rule_id': 'DI_BINDING_CLOSURE_EAGER_CONSUMER',
        'binding': {'module_fun': 'developmentModuleAdditions',
                    'variant_source_set': 'app-thunderbird/src/beta/kotlin'},
        'cfg': {'consumer_class': 'InMemoryFeatureFlagProvider',
                'eager_arg': 'createdAtStart', 'injector': 'get'},
        'files': {'variant_files': ['app-thunderbird/src/beta/kotlin/net/thunderbird/android/dev/BetaConfig.kt'],
                  'common_module_files': ['app-thunderbird/src/main/kotlin/net/thunderbird/android/ThunderbirdKoinModule.kt',
                                          'legacy/common/src/main/java/com/fsck/k9/LegacyCommonAppModule.kt'],
                  'consumer_file': 'core/featureflag/src/commonMain/kotlin/net/thunderbird/core/featureflag/InMemoryFeatureFlagProvider.kt'},
    },
}


def _resolve_side(spec, slot, side):
    base = SNAP / slot / side
    out = {}
    for k, v in spec['files'].items():
        if isinstance(v, list):
            out[k] = [base / x for x in v]
        else:
            out[k] = base / v
    return out


def _hash_inputs(inputs):
    out = {}
    for k, v in inputs.items():
        if isinstance(v, list):
            out[k] = {str(x): _sha(x) for x in v}
        else:
            out[k] = _sha(v)
    return out


def run_side(slot, side, write=True):
    spec = PAIR_SPECS[slot]
    inputs = _resolve_side(spec, slot, side)
    checker = CHECKERS[spec['rule_id']]
    cmd = [sys.executable, str(V5 / 'src/rules_C1.py'), 'run-pairs', '--pair', slot,
           '--side', side]
    t0 = time.perf_counter()
    try:
        result = checker(inputs, spec['binding'], spec['cfg'])
        exit_status = 0
    except Exception as e:  # crashes are UNKNOWN, never guessed
        result = {'observation': 'UNKNOWN', 'scope': spec['rule_id'], 'evidence': [],
                  'reason': 'CHECKER_CRASH:' + repr(e), 'duration_s': 0.0}
        exit_status = 1
    dur = time.perf_counter() - t0
    receipt = {
        'pair_slot': slot, 'task_id': spec['task'], 'side': side,
        'kind': spec['kind'], 'family': 'C1', 'rule_id': spec['rule_id'],
        'rule_version': RULE_VERSION, 'binding': spec['binding'],
        'rule_config': spec['cfg'], 'observation': result['observation'],
        'scope': result['scope'], 'reason': result['reason'],
        'evidence': result['evidence'], 'input_sha256': _hash_inputs(inputs),
        'command': cmd, 'exit_status': exit_status,
        'duration_s': round(dur, 4), 'checker': 'rules_C1',
        'checker_sha256': _sha(pathlib.Path(__file__)),
        'helper_sha256': _sha(V5 / 'src/helpers_C1.py'),
        'method': 'B4 v2加目标规则补正',
        'scoring_reference_read_by_checker': False,
    }
    if write:
        outdir = V5 / 'runs/C1'
        outdir.mkdir(parents=True, exist_ok=True)
        (outdir / f'{slot}-{side}.json').write_text(
            json.dumps(receipt, ensure_ascii=False, indent=2))
    return receipt


def run_pairs(only=None, sides=('buggy', 'fixed')):
    rows = []
    slots = [only] if only else list(PAIR_SPECS)
    for slot in slots:
        for side in sides:
            r = run_side(slot, side)
            rows.append(r)
            print(slot, side, r['rule_id'], r['observation'], r['reason'])
    path = V5 / 'runs/C1/c1_sides.jsonl'
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text('\n'.join(json.dumps(r, ensure_ascii=False) for r in rows) + '\n')
    return rows


# ------------------------------------------------------ counterexamples

CE = V5 / 'runs/C1/counterexamples'

_JAVA_LISTENER = """package ce;
public class Helper {
    private final Adapter adapter = new Adapter();
    public void authorize(String verifier, Listener listener) {
        adapter.authorize(verifier, this, listener);
    }
    public interface Listener { void authorizationCompleted(); }
}
"""

_JAVA_ADAPTER_SINGLE = """package ce;
public class Adapter {
    public void authorize(String v, Helper h, Helper.Listener l) {
        new Task(h, l).run();
    }
    private class Task {
        private final Helper helper;
        private final Helper.Listener listener;
        Task(Helper h, Helper.Listener l) { helper = h; listener = l; }
        void done() {
            if (listener != null) {
                listener.authorizationCompleted();
            }
        }
    }
}
"""

_JAVA_HELPER_REGISTRY = """package ce;
import java.util.HashSet;
import java.util.Set;
public class Helper {
    private final Adapter adapter = new Adapter();
    private final Set<Listener> listeners = new HashSet<>();
    public void addListener(Listener l) { listeners.add(l); }
    public void authorize(String verifier) { adapter.authorize(verifier, this); }
    public void notifyAndRemoveListeners() {
        for (Listener l : listeners) { l.authorizationCompleted(); }
        listeners.clear();
    }
    public interface Listener { void authorizationCompleted(); }
}
"""

_JAVA_ADAPTER_BROADCAST = """package ce;
public class Adapter {
    public void authorize(String v, Helper h) { new Task(h).run(); }
    private class Task {
        private final Helper helper;
        Task(Helper h) { helper = h; }
        void done() { helper.notifyAndRemoveListeners(); }
    }
}
"""

_JAVA_ADAPTER_WRONG_OBJECT = """package ce;
public class Adapter {
    private final Notifier notifier = new Notifier();
    public void authorize(String v, Helper h, Helper.Listener l) { new Task(h, l).run(); }
    private class Task {
        private final Helper helper;
        private final Helper.Listener listener;
        Task(Helper h, Helper.Listener l) { helper = h; listener = l; }
        void done() { notifier.onComplete(); }
    }
}
class Notifier { void onComplete() { } }
"""

_JAVA_ADAPTER_BRANCH = """package ce;
public class Adapter {
    public void authorize(String v, Helper h, Helper.Listener l) { new Task(h, l).run(); }
    private class Task {
        private final Helper helper;
        private final Helper.Listener listener;
        Task(Helper h, Helper.Listener l) { helper = h; listener = l; }
        void done() {
            try {
                listener.authorizationCompleted();
            } catch (RuntimeException e) {
                helper.notifyAndRemoveListeners();
            }
        }
    }
}
"""

_KTX_FRAGMENT_BUGGY = """package ce
class S : Fragment() {
    fun go(error: Boolean = false) {
        if (error) activity?.replaceFragment<ErrFragment>()
        else activity?.addFragment<ErrFragment>()
    }
}
"""

_KTX_GUARDED = """package ce
class S : Fragment() {
    fun go(error: Boolean = false) {
        activity?.run {
            if (lifecycle.currentState.isAtLeast(Lifecycle.State.RESUMED)) {
                if (error) {
                    replaceFragment<ErrFragment>()
                } else {
                    addFragment<ErrFragment>()
                }
            }
        }
    }
}
"""

_KTX_EARLY_RETURN_GUARD = """package ce
class S : Fragment() {
    fun go(error: Boolean = false) {
        if (!activity.lifecycle.currentState.isAtLeast(Lifecycle.State.RESUMED)) return
        if (error) activity?.replaceFragment<ErrFragment>()
        else activity?.addFragment<ErrFragment>()
    }
}
"""

_KTX_NO_TXN = """package ce
class S : Fragment() {
    fun go(error: Boolean = false) {
        val extras = Bundle().apply { putBoolean("error", error) }
        showNotice(extras)
    }
}
"""

_KTX_PARTIAL_GUARD = """package ce
class S : Fragment() {
    fun go(error: Boolean = false) {
        if (error) activity?.replaceFragment<ErrFragment>()
        else activity?.run {
            if (lifecycle.currentState.isAtLeast(Lifecycle.State.RESUMED)) {
                addFragment<ErrFragment>()
            }
        }
    }
}
"""

_KTX_COLLECTION_BUGGY = """package ce
class Store {
    fun storeUserDevices(user: User, devices: Map<String, Device>) {
        val ids = devices.keys
        user.devices.forEach { d ->
            if (d.id !in ids) { d.deleteOnCascade() }
        }
    }
}
"""

_KTX_COLLECTION_SNAPSHOT = """package ce
class Store {
    fun storeUserDevices(user: User, devices: Map<String, Device>) {
        val ids = devices.keys
        user.devices.toList().forEach { d ->
            if (d.id !in ids) { d.deleteOnCascade() }
        }
    }
}
"""

_KTX_COLLECTION_OTHER = """package ce
class Store {
    fun storeUserDevices(user: User, devices: Map<String, Device>) {
        user.sessions.forEach { s -> s.deleteOnCascade() }
    }
}
"""

_KTX_COLLECTION_ALIAS = """package ce
class Store {
    fun storeUserDevices(user: User, devices: Map<String, Device>) {
        val live = user.devices
        live.forEach { d -> d.deleteOnCascade() }
    }
}
"""

_JAVA_PARCEL = """package ce;
import android.os.Parcelable;
public class RequiredInputParcel implements Parcelable {
    public enum RequiredInputType {
        PASSPHRASE, PASSPHRASE_SYMMETRIC, PASSPHRASE_AUTH,
        BACKUP_CODE, NUMERIC_9X4, NUMERIC_9X4_AUTOCRYPT,
        SECURITY_TOKEN_SIGN, ENABLE_ORBOT, UPLOAD_FAIL_RETRY
    }
    public final RequiredInputType mType = RequiredInputType.PASSPHRASE;
    public Long getSubKeyId() { return null; }
}
"""

_JAVA_PARCEL_TEXT = _JAVA_PARCEL.replace("""    public Long getSubKeyId() { return null; }
""", """    public Long getSubKeyId() { return null; }
    public boolean isTextInput() {
        switch (mType) {
            case BACKUP_CODE:
            case NUMERIC_9X4:
            case NUMERIC_9X4_AUTOCRYPT:
            case PASSPHRASE:
            case PASSPHRASE_AUTH:
            case PASSPHRASE_SYMMETRIC:
                return true;
            default:
                return false;
        }
    }
""")

_JAVA_ACTIVITY = """package ce;
import android.os.Bundle;
public class PassphraseDialogActivity extends FragmentActivity {
    public static final String EXTRA_REQUIRED_INPUT = "required_input";
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        RequiredInputParcel requiredInput = getIntent().getParcelableExtra(EXTRA_REQUIRED_INPUT);
        %s
        PassphraseDialogFragment frag = new PassphraseDialogFragment();
        frag.show(getSupportFragmentManager(), "passphraseDialog");
    }
}
"""

_KTX_DI_VARIANT_MISSING = """package ce
fun Module.developmentModuleAdditions() {
    single<Map<String, BackendFactory>> { emptyMap() }
}
"""

_KTX_DI_VARIANT_BOUND = """package ce
fun Module.developmentModuleAdditions() {
    single<Map<String, BackendFactory>> { emptyMap() }
    single<FeatureFlagOverrides> { NoOpFeatureFlagOverrides() }
}
"""

_KTX_DI_VARIANT_WRONG_TYPE = """package ce
fun Module.developmentModuleAdditions() {
    single<FeatureFlagFactory> { TbFeatureFlagFactory() }
}
"""

_KTX_DI_COMMON = """package ce
val legacyCommonAppModule = module {
    %s
}
"""

_KTX_DI_CONSUMER = """package ce
class InMemoryFeatureFlagProvider(
    private val featureFlagFactory: FeatureFlagFactory,
    private val featureFlagOverrides: FeatureFlagOverrides,
) : FeatureFlagProvider
"""


def _ce_case(root, name, files):
    d = root / name
    d.mkdir(parents=True, exist_ok=True)
    out = {}
    for fname, text in files.items():
        p = d / fname
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)
        out[fname] = p
    return d, out


def run_counterexamples():
    CE.mkdir(parents=True, exist_ok=True)
    results = []

    def add(family, case, category, expected, result, note=''):
        results.append({'rule_id': family, 'case': case, 'category': category,
                        'expected': expected, 'observed': result['observation'],
                        'passed': result['observation'] == expected,
                        'reason': result['reason'], 'note': note})

    # 1 OAuth callback delivery
    d, f = _ce_case(CE / 'OAUTH_CALLBACK_LISTENER_REGISTRY', 'defect_remains',
                    {'Helper.java': _JAVA_LISTENER, 'Adapter.java': _JAVA_ADAPTER_SINGLE})
    r = verify('OAUTH_CALLBACK_LISTENER_REGISTRY',
               {'helper_file': f['Helper.java'], 'adapter_file': f['Adapter.java']},
               {}, {'listener_type': 'Listener',
                    'completion_calls': ['authorizationCompleted'],
                    'register_methods': ['addListener']})
    add('OAUTH_CALLBACK_LISTENER_REGISTRY', 'defect_remains', 'defect_remains', 'PRESENT', r)

    d, f = _ce_case(CE / 'OAUTH_CALLBACK_LISTENER_REGISTRY', 'defect_fixed',
                    {'Helper.java': _JAVA_HELPER_REGISTRY,
                     'Adapter.java': _JAVA_ADAPTER_BROADCAST})
    r = verify('OAUTH_CALLBACK_LISTENER_REGISTRY',
               {'helper_file': f['Helper.java'], 'adapter_file': f['Adapter.java']},
               {}, {'listener_type': 'Listener',
                    'completion_calls': ['authorizationCompleted'],
                    'register_methods': ['addListener']})
    add('OAUTH_CALLBACK_LISTENER_REGISTRY', 'defect_fixed', 'defect_fixed', 'ABSENT', r)

    d, f = _ce_case(CE / 'OAUTH_CALLBACK_LISTENER_REGISTRY', 'wrong_object',
                    {'Helper.java': _JAVA_HELPER_REGISTRY,
                     'Adapter.java': _JAVA_ADAPTER_WRONG_OBJECT})
    r = verify('OAUTH_CALLBACK_LISTENER_REGISTRY',
               {'helper_file': f['Helper.java'], 'adapter_file': f['Adapter.java']},
               {}, {'listener_type': 'Listener',
                    'completion_calls': ['authorizationCompleted'],
                    'register_methods': ['addListener']})
    add('OAUTH_CALLBACK_LISTENER_REGISTRY', 'wrong_object', 'wrong_object', 'UNKNOWN', r)

    d, f = _ce_case(CE / 'OAUTH_CALLBACK_LISTENER_REGISTRY', 'exception_branch',
                    {'Helper.java': _JAVA_HELPER_REGISTRY,
                     'Adapter.java': _JAVA_ADAPTER_BRANCH})
    r = verify('OAUTH_CALLBACK_LISTENER_REGISTRY',
               {'helper_file': f['Helper.java'], 'adapter_file': f['Adapter.java']},
               {}, {'listener_type': 'Listener',
                    'completion_calls': ['authorizationCompleted'],
                    'register_methods': ['addListener']})
    add('OAUTH_CALLBACK_LISTENER_REGISTRY', 'exception_branch', 'exception_path', 'UNKNOWN', r)

    # 2 fragment transaction lifecycle
    cfg_frag = PAIR_SPECS['FP-08']['cfg']
    d, f = _ce_case(CE / 'FRAGMENT_TXN_LIFECYCLE_GUARD', 'defect_remains',
                    {'S.kt': _KTX_FRAGMENT_BUGGY})
    r = verify('FRAGMENT_TXN_LIFECYCLE_GUARD', {'kt_file': f['S.kt']},
               {'method': 'go'}, cfg_frag)
    add('FRAGMENT_TXN_LIFECYCLE_GUARD', 'defect_remains', 'defect_remains', 'PRESENT', r)

    d, f = _ce_case(CE / 'FRAGMENT_TXN_LIFECYCLE_GUARD', 'defect_fixed',
                    {'S.kt': _KTX_GUARDED})
    r = verify('FRAGMENT_TXN_LIFECYCLE_GUARD', {'kt_file': f['S.kt']},
               {'method': 'go'}, cfg_frag)
    add('FRAGMENT_TXN_LIFECYCLE_GUARD', 'defect_fixed', 'defect_fixed', 'ABSENT', r)

    d, f = _ce_case(CE / 'FRAGMENT_TXN_LIFECYCLE_GUARD', 'early_return_guard',
                    {'S.kt': _KTX_EARLY_RETURN_GUARD})
    r = verify('FRAGMENT_TXN_LIFECYCLE_GUARD', {'kt_file': f['S.kt']},
               {'method': 'go'}, cfg_frag)
    add('FRAGMENT_TXN_LIFECYCLE_GUARD', 'early_return_guard', 'defect_fixed', 'ABSENT', r)

    d, f = _ce_case(CE / 'FRAGMENT_TXN_LIFECYCLE_GUARD', 'wrong_object',
                    {'S.kt': _KTX_NO_TXN})
    r = verify('FRAGMENT_TXN_LIFECYCLE_GUARD', {'kt_file': f['S.kt']},
               {'method': 'go'}, cfg_frag)
    add('FRAGMENT_TXN_LIFECYCLE_GUARD', 'wrong_object', 'wrong_object', 'UNKNOWN', r)

    d, f = _ce_case(CE / 'FRAGMENT_TXN_LIFECYCLE_GUARD', 'branch_partial_guard',
                    {'S.kt': _KTX_PARTIAL_GUARD})
    r = verify('FRAGMENT_TXN_LIFECYCLE_GUARD', {'kt_file': f['S.kt']},
               {'method': 'go'}, cfg_frag)
    add('FRAGMENT_TXN_LIFECYCLE_GUARD', 'branch_partial_guard', 'branch', 'PRESENT', r)

    # 3 collection mutation during iteration
    cfg_col = PAIR_SPECS['FP-10']['cfg']
    for case, text, expected, cat in (
            ('defect_remains', _KTX_COLLECTION_BUGGY, 'PRESENT', 'defect_remains'),
            ('defect_fixed', _KTX_COLLECTION_SNAPSHOT, 'ABSENT', 'defect_fixed'),
            ('wrong_object', _KTX_COLLECTION_OTHER, 'ABSENT', 'wrong_object'),
            ('alias_binding', _KTX_COLLECTION_ALIAS, 'PRESENT', 'alias')):
        d, f = _ce_case(CE / 'COLLECTION_MUTATION_DURING_ITERATION', case, {'S.kt': text})
        r = verify('COLLECTION_MUTATION_DURING_ITERATION', {'kt_file': f['S.kt']},
                   {'method': 'storeUserDevices'}, cfg_col)
        add('COLLECTION_MUTATION_DURING_ITERATION', case, cat, expected, r)

    # 4 input-type gate
    cfg_gate = PAIR_SPECS['FP-31']['cfg']
    gate_cases = (
        ('defect_remains',
         _JAVA_ACTIVITY % 'if (requiredInput.mType != RequiredInputType.PASSPHRASE) { return; }',
         'PRESENT', 'defect_remains'),
        ('defect_fixed',
         _JAVA_ACTIVITY % 'if (!requiredInput.isTextInput()) { return; }',
         'ABSENT', 'defect_fixed'),
        ('wrong_object',
         _JAVA_ACTIVITY % 'if (savedInstanceState != null) { return; }',
         'UNKNOWN', 'wrong_object'),
        ('multi_branch',
         _JAVA_ACTIVITY % 'if (requiredInput.mType != RequiredInputType.PASSPHRASE && requiredInput.mType != RequiredInputType.PASSPHRASE_SYMMETRIC) { return; }',
         'PRESENT', 'branch'),
    )
    for case, act_text, expected, cat in gate_cases:
        parcel = _JAVA_PARCEL_TEXT if case == 'defect_fixed' else _JAVA_PARCEL
        d, f = _ce_case(CE / 'INPUT_TYPE_GATE_COMPLETENESS', case,
                        {'PassphraseDialogActivity.java': act_text,
                         'RequiredInputParcel.java': parcel})
        r = verify('INPUT_TYPE_GATE_COMPLETENESS',
                   {'activity_file': f['PassphraseDialogActivity.java'],
                    'parcel_file': f['RequiredInputParcel.java']},
                   {'method': 'onCreate', 'enum': 'RequiredInputType'}, cfg_gate)
        add('INPUT_TYPE_GATE_COMPLETENESS', case, cat, expected, r)

    # 5 DI binding closure
    cfg_di = PAIR_SPECS['FP-33']['cfg']
    di_cases = (
        ('defect_remains', _KTX_DI_VARIANT_MISSING,
         _KTX_DI_COMMON % 'single<FeatureFlagFactory> { TbFeatureFlagFactory() }\n    single<FeatureFlagProvider>(createdAtStart = true) {\n        InMemoryFeatureFlagProvider(featureFlagFactory = get(), featureFlagOverrides = get())\n    }',
         'PRESENT', 'defect_remains'),
        ('defect_fixed', _KTX_DI_VARIANT_BOUND,
         _KTX_DI_COMMON % 'single<FeatureFlagFactory> { TbFeatureFlagFactory() }\n    single<FeatureFlagProvider>(createdAtStart = true) {\n        InMemoryFeatureFlagProvider(featureFlagFactory = get(), featureFlagOverrides = get())\n    }',
         'ABSENT', 'defect_fixed'),
        ('wrong_object', _KTX_DI_VARIANT_WRONG_TYPE,
         _KTX_DI_COMMON % 'single<FeatureFlagFactory> { TbFeatureFlagFactory() }\n    single<FeatureFlagProvider>(createdAtStart = true) {\n        InMemoryFeatureFlagProvider(featureFlagFactory = get(), featureFlagOverrides = get())\n    }',
         'PRESENT', 'wrong_object'),
        ('not_eager', _KTX_DI_VARIANT_MISSING,
         _KTX_DI_COMMON % 'single<FeatureFlagFactory> { TbFeatureFlagFactory() }\n    single<FeatureFlagProvider> {\n        InMemoryFeatureFlagProvider(featureFlagFactory = get(), featureFlagOverrides = get())\n    }',
         'ABSENT', 'wrong_object'),
    )
    for case, variant, common, expected, cat in di_cases:
        d, f = _ce_case(CE / 'DI_BINDING_CLOSURE_EAGER_CONSUMER', case,
                        {'BetaConfig.kt': variant, 'Common.kt': common,
                         'Consumer.kt': _KTX_DI_CONSUMER})
        r = verify('DI_BINDING_CLOSURE_EAGER_CONSUMER',
                   {'variant_files': [f['BetaConfig.kt']],
                    'common_module_files': [f['Common.kt']],
                    'consumer_file': f['Consumer.kt']},
                   {'module_fun': 'developmentModuleAdditions'}, cfg_di)
        add('DI_BINDING_CLOSURE_EAGER_CONSUMER', case, cat, expected, r)

    by_rule = {}
    for x in results:
        s = by_rule.setdefault(x['rule_id'], {'total': 0, 'passed': 0, 'categories': {}})
        s['total'] += 1
        s['passed'] += int(x['passed'])
        c = s['categories'].setdefault(x['category'], {'total': 0, 'passed': 0})
        c['total'] += 1
        c['passed'] += int(x['passed'])
    out = {'suite': 'C1 counterexamples', 'rule_family': 'C1',
           'checker_sha256': _sha(pathlib.Path(__file__)),
           'helper_sha256': _sha(V5 / 'src/helpers_C1.py'),
           'total': len(results), 'passed': sum(int(x['passed']) for x in results),
           'by_rule': by_rule, 'cases': results}
    p = V5 / 'checks/C1_counterexamples.json'
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(out, ensure_ascii=False, indent=2))
    failed = [x for x in results if not x['passed']]
    print('counterexamples', out['passed'], '/', out['total'])
    for x in failed:
        print('FAIL', x['rule_id'], x['case'], 'expected', x['expected'],
              'observed', x['observed'], x['reason'])
    return out


if __name__ == '__main__':
    args = sys.argv[1:]
    if args and args[0] == 'run-pairs':
        only = args[args.index('--pair') + 1] if '--pair' in args else None
        sides = ((args[args.index('--side') + 1],) if '--side' in args
                 else ('buggy', 'fixed'))
        run_pairs(only, sides)
    elif args and args[0] == 'counterexamples':
        run_counterexamples()
    else:
        print('usage: rules_C1.py run-pairs [--pair FP-xx] [--side buggy|fixed]')
