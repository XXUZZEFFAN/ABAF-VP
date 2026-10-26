"""B2 resource-lifecycle rule family.

Three propositions, each evaluated on the statement paths of ONE target method, so
that normal and exceptional exits are covered and the binding is to the SAME object:

  PARCEL_OBTAIN_WITHOUT_RECYCLE   Parcel.obtain() must be recycle()d on every exit path.
  PFD_PIPE_ACQUIRED_NOT_CLOSED    a ParcelFileDescriptor produced by pipeFrom/pipeTo must be
                                  close()d on every exit path; finally counts, a sibling
                                  object's close() does not.
  SU_PIPE_LAST_WRITE_NOT_FLUSHED  a command written to a child-process stdin stream must be
                                  followed by flush() before the method exits.

verify(rule_id, source_inputs, target_binding, rule_config) -> observation dict.
Also accepts verify(source_inputs, target_binding, rule_config) with rule_id inside
rule_config (the 3-arg form in the v5 brief).

Verdicts come from the JDK17 deep AST (javaparse.JavaFactsDeep via facts_for); string
search is only used to classify an already-UNKNOWN outcome (try-with-resources is not
serialised by the shared serialiser, so its absence of an acquisition must not be read
as "repaired").
"""
import pathlib
import re
import time

from javaparse import facts_for, select_method

MAX_PATHS = 256
_WORD = re.compile(r'[A-Za-z_$][A-Za-z0-9_$]*')


def _obs(observation, scope, evidence, reason, duration_s=0.0):
    return {'observation': observation, 'scope': scope, 'evidence': evidence,
            'reason': reason, 'duration_s': duration_s}


# ---------------------------------------------------------------- AST helpers

def _k(n):
    return n.get('kind', '') if isinstance(n, dict) else ''


def _simple(t):
    return str(t or '').split('.')[-1].strip()


def _member_chain(sel):
    if _k(sel) == 'IDENTIFIER':
        return sel.get('name') or ''
    if _k(sel) == 'MEMBER_SELECT':
        base = _member_chain(sel.get('receiver') or {})
        return (base + '.' if base else '') + (sel.get('name') or '')
    return ''


def _recv(sel):
    """Receiver variable name of a method select (None for unqualified calls)."""
    if _k(sel) == 'MEMBER_SELECT':
        base = sel.get('receiver') or {}
        if _k(base) in ('IDENTIFIER', 'MEMBER_SELECT'):
            name = _member_chain(base)
            return name[5:] if name.startswith('this.') else name
    return None


def _callee_name(e):
    if _k(e) == 'METHOD_INVOCATION':
        return (e.get('select') or {}).get('name') or ''
    return ''


def _arg_method_names(new_class):
    return tuple(m for m in (_callee_name(a) for a in (new_class.get('args') or [])) if m)


def _expr_events(e):
    """Linear event stream of an expression: nested calls, then the call itself."""
    if isinstance(e, list):
        out = []
        for x in e:
            out += _expr_events(x)
        return out
    if not isinstance(e, dict):
        return []
    k = e.get('kind', '')
    if k == 'METHOD_INVOCATION':
        sel = e.get('select') or {}
        out = _expr_events(sel)
        out += _expr_events(e.get('args') or [])
        out.append(('CALL', _recv(sel), sel.get('name') or ''))
        return out
    if k == 'NEW_CLASS':
        out = _expr_events(e.get('args') or [])
        out.append(('NEW', None, e.get('type', ''), _arg_method_names(e)))
        return out
    if k == 'ASSIGNMENT':
        var = (e.get('variable') or {}).get('name') or _member_chain(e.get('variable') or {})
        return _rhs_events(e.get('expr'), var)
    out = []
    for key in ('receiver', 'args', 'expr', 'init', 'variable', 'cond'):
        if key in e:
            out += _expr_events(e.get(key))
    return out


def _rhs_events(expr, target):
    if expr is None:
        return []
    out = _expr_events(expr)
    k = _k(expr)
    if k == 'METHOD_INVOCATION':
        sel = expr.get('select') or {}
        out.append(('ASSIGN_CALL', target, _recv(sel), sel.get('name') or ''))
    elif k == 'NEW_CLASS':
        out.append(('NEW', target, expr.get('type', ''), _arg_method_names(expr)))
    else:
        out.append(('ASSIGN', target))
    return out


def _cond_vars(node):
    """Identifiers a condition tests.

    The shared serialiser emits IDENTIFIER nodes for simple operands but a raw text
    node for binary expressions such as `input != null`, so text tokens of a condition
    are scanned as well (this only decides whether a branch is a guarded region; it is
    never used as evidence that a release exists).
    """
    names = set()

    def walk(n):
        if isinstance(n, dict):
            if n.get('kind') == 'IDENTIFIER':
                names.add(n.get('name'))
            text = n.get('text')
            if isinstance(text, str):
                names.update(_WORD.findall(text))
            for key, v in n.items():
                if key != 'text':
                    walk(v)
        elif isinstance(n, list):
            for v in n:
                walk(v)

    walk(node)
    return names


class _TooManyPaths(Exception):
    pass


def _seq_paths(stmts):
    paths = [([], None)]
    for st in stmts or []:
        nxt = []
        for ev, exit_ in paths:
            if exit_ is not None:
                nxt.append((ev, exit_))
                continue
            for sev, sexit in _stmt_paths(st):
                nxt.append((ev + sev, sexit))
        paths = nxt
        if len(paths) > MAX_PATHS:
            raise _TooManyPaths(len(paths))
    return paths


def _fork(then_paths, else_paths, cond_events, cond_node):
    """Fork on a condition, except for the null-guard idiom.

    `if (v != null) { v.close(); }` is the standard optional-acquisition release: the
    condition tests the same object that is acted on in one branch, so both branches
    collapse into one guarded region instead of producing a bogus "no release" path.
    """
    all_paths = list(then_paths) + list(else_paths)
    has_exit = any(ex is not None for _, ex in all_paths)
    branch_receivers = {e[1] for ev, _ in all_paths for e in ev if e[0] == 'CALL'}
    if not has_exit and (_cond_vars(cond_node) & branch_receivers):
        merged = [e for ev, _ in all_paths for e in ev]
        return [(cond_events + merged, None)]
    return [(cond_events + ev, ex) for ev, ex in all_paths]


def _stmt_paths(st):
    if not isinstance(st, dict):
        return [([], None)]
    k = st.get('kind', '')
    if k == 'EXPRESSION_STATEMENT':
        return [(_expr_events(st.get('expr')), None)]
    if k == 'VARIABLE':
        return [([('DECL', st.get('name'), st.get('type', ''))]
                 + _rhs_events(st.get('init'), st.get('name')), None)]
    if k == 'RETURN':
        return [(_expr_events(st.get('expr')), 'RETURN')]
    if k == 'THROW':
        return [(_expr_events(st.get('expr')), 'THROW')]
    if k == 'BLOCK':
        return _seq_paths(st.get('stmts') or [])
    if k == 'IF':
        cond = st.get('cond')
        return _fork(_stmt_paths(st.get('then')), _stmt_paths(st.get('else')),
                     _expr_events(cond), cond)
    if k in ('FOR_LOOP', 'ENHANCED_FOR_LOOP', 'WHILE_LOOP', 'DO_WHILE_LOOP'):
        out = [([], None)]  # zero iterations
        for ev, ex in _stmt_paths(st.get('body')):
            out.append((ev, ex if ex in ('RETURN', 'THROW') else None))
        return out
    if k == 'TRY':
        body_paths = _seq_paths((st.get('body') or {}).get('stmts') or [])
        fin_paths = _stmt_paths(st.get('finally')) if st.get('finally') else [([], None)]
        # An exception may fire after any acquisition inside the try, so catch paths
        # inherit the try-body acquisition events (conservative: they must be released
        # on that path too). The event kinds are kept so rule predicates filter the same way.
        acq_maybe, seen = [], set()
        for ev, _ in body_paths:
            for e in ev:
                if e[0] in ('ASSIGN_CALL', 'NEW') and e[1] and e[1] not in seen:
                    seen.add(e[1])
                    acq_maybe.append(e)
        out = []
        for ev, ex in body_paths:
            for fev, fex in fin_paths:
                out.append((ev + fev, fex or ex))
        for c in st.get('catches') or []:
            prefix = list(acq_maybe)
            for ev, ex in _seq_paths((c.get('body') or {}).get('stmts') or []):
                for fev, fex in fin_paths:
                    out.append((prefix + ev + fev, fex or ex))
        return out
    if k == 'SWITCH':
        out = []
        cases = st.get('cases') or []
        for c in cases:
            for ev, ex in _seq_paths(c.get('body') or []):
                out.append((_expr_events(st.get('expr')) + ev, ex))
        return out or [([], None)]
    if k == 'SYNCHRONIZED':
        return _stmt_paths(st.get('body'))
    text = str(st.get('text') or '').strip()
    if text.startswith('break'):
        return [([], 'BREAK')]
    if text.startswith('continue'):
        return [([], 'CONTINUE')]
    return [([], None)]


# ---------------------------------------------------------------- path checks

def _decl_types(paths):
    types = {}
    for ev, _ in paths:
        for e in ev:
            if e[0] == 'DECL' and e[1] and e[2]:
                types.setdefault(e[1], e[2])
    return types


def _check_all_paths(paths, is_acq, is_release):
    targets = []
    for ev, _ in paths:
        for e in ev:
            t = is_acq(e)
            if t and t not in targets:
                targets.append(t)
    leaking, detail = [], {}
    for t in targets:
        per_path, ok = [], True
        for pi, (ev, exit_) in enumerate(paths):
            idxs = [i for i, e in enumerate(ev) if is_acq(e) == t]
            if not idxs:
                continue
            released = any(is_release(e, t) for e in ev[idxs[-1] + 1:])
            per_path.append({'path': pi, 'exit': exit_ or 'FALLTHROUGH',
                             'released': released})
            ok = ok and released
        detail[t] = per_path
        if not ok:
            leaking.append(t)
    return leaking, targets, detail


def _call_release(methods):
    methods = set(methods)

    def f(e, t):
        return e[0] == 'CALL' and e[1] == t and e[2] in methods
    return f


def _method_source(path, method):
    try:
        lines = pathlib.Path(path).read_text(errors='replace').splitlines()
        return '\n'.join(lines[method['start_line'] - 1:method['end_line']])
    except Exception:
        return ''


# ---------------------------------------------------------------- rules

def _parcel(rule_id, paths, cfg):
    receivers = set(cfg.get('acquisition_receivers') or ['Parcel'])
    methods = set(cfg.get('acquisition_methods') or ['obtain'])

    def acq(e):
        if e[0] == 'ASSIGN_CALL':
            _, t, recv, name = e
            if t and recv in receivers and name in methods:
                return t
        return None

    leaking, targets, detail = _check_all_paths(
        paths, acq, _call_release(cfg.get('release_methods') or ['recycle']))
    if not targets:
        return None, 'NO_PARCEL_ACQUISITION_IN_METHOD', {'targets': []}
    if leaking:
        return 'PRESENT', 'PARCEL_OBTAINED_ON_PATH_WITHOUT_RECYCLE', {
            'targets': targets, 'leaking': leaking, 'paths': detail}
    return 'ABSENT', 'EVERY_ACQUISITION_RECYCLED_ON_ALL_EXIT_PATHS', {
        'targets': targets, 'leaking': [], 'paths': detail}


def _pfd(rule_id, paths, cfg):
    types = _decl_types(paths)
    want = {_simple(t) for t in (cfg.get('types') or ['ParcelFileDescriptor'])}
    callees = set(cfg.get('acquisition_callees') or ['pipeFrom', 'pipeTo'])

    def acq(e):
        if e[0] == 'ASSIGN_CALL':
            _, t, recv, name = e
            if t and name in callees and _simple(types.get(t)) in want:
                return t
        return None

    leaking, targets, detail = _check_all_paths(
        paths, acq, _call_release(cfg.get('release_methods') or ['close']))
    if not targets:
        return None, 'NO_PARCEL_FILE_DESCRIPTOR_ACQUISITION_IN_METHOD', {
            'targets': [], 'declared_types': types}
    if leaking:
        return 'PRESENT', 'PIPE_PFD_ACQUIRED_ON_PATH_WITHOUT_CLOSE', {
            'targets': targets, 'leaking': leaking, 'paths': detail}
    return 'ABSENT', 'EVERY_PIPE_PFD_CLOSED_ON_ALL_EXIT_PATHS', {
        'targets': targets, 'leaking': [], 'paths': detail}


def _su_flush(rule_id, paths, cfg):
    types = _decl_types(paths)
    stream_types = {_simple(t) for t in (cfg.get('stream_types') or ['DataOutputStream'])}
    source_methods = set(cfg.get('source_methods') or ['getOutputStream'])
    writes = set(cfg.get('write_methods') or
                 ['write', 'writeBytes', 'writeUTF', 'writeChars', 'writeInt',
                  'print', 'println', 'append'])
    flushes = set(cfg.get('flush_methods') or ['flush'])
    close_implies_flush = cfg.get('close_implies_flush', True)

    streams = []
    for ev, _ in paths:
        for e in ev:
            if e[0] == 'NEW' and e[1] and _simple(e[2]) in stream_types:
                if not source_methods or (set(e[3]) & source_methods):
                    if e[1] not in streams:
                        streams.append(e[1])
    if not streams:
        return None, 'NO_CHILD_PROCESS_INPUT_STREAM_BOUND_IN_METHOD', {
            'streams': [], 'declared_types': types}
    detail, leaking = {}, []
    for s in streams:
        per_path, ok, written = [], True, False
        for pi, (ev, exit_) in enumerate(paths):
            widx = [i for i, e in enumerate(ev)
                    if e[0] == 'CALL' and e[1] == s and e[2] in writes]
            if not widx:
                continue
            written = True
            tail = ev[widx[-1] + 1:]
            flushed = any(e[0] == 'CALL' and e[1] == s
                          and (e[2] in flushes
                               or (close_implies_flush and e[2] == 'close'))
                          for e in tail)
            per_path.append({'path': pi, 'exit': exit_ or 'FALLTHROUGH',
                             'last_write': ev[widx[-1]][2], 'flushed_after_last_write': flushed})
            ok = ok and flushed
        detail[s] = per_path
        if written and not ok:
            leaking.append(s)
    if not any(detail[s] for s in streams):
        return None, 'NO_WRITE_TO_CHILD_PROCESS_STREAM_IN_METHOD', {'streams': streams}
    if leaking:
        return 'PRESENT', 'LAST_PIPE_WRITE_NOT_FLUSHED_BEFORE_EXIT', {
            'streams': streams, 'leaking': leaking, 'paths': detail}
    return 'ABSENT', 'EVERY_PIPE_WRITE_FLUSHED_BEFORE_EXIT', {
        'streams': streams, 'leaking': [], 'paths': detail}


RULES = {
    'PARCEL_OBTAIN_WITHOUT_RECYCLE': (_parcel, 'android.os.Parcel.obtain()/recycle() lifecycle'),
    'PFD_PIPE_ACQUIRED_NOT_CLOSED': (_pfd, 'ParcelFileDescriptor pipeFrom/pipeTo close on all exits'),
    'SU_PIPE_LAST_WRITE_NOT_FLUSHED': (_su_flush, 'child-process stdin flush after last write'),
}


def _unpack(args):
    if len(args) == 4:
        return args[0], args[1], args[2], args[3]
    if len(args) == 3:
        source_inputs, target_binding, rule_config = args
        rid = (rule_config or {}).get('rule_id') or (target_binding or {}).get('rule_id')
        return rid, source_inputs, target_binding, rule_config
    raise TypeError('verify expects (rule_id, source_inputs, target_binding, rule_config)')


def verify(*args):
    rule_id, source_inputs, target_binding, rule_config = _unpack(args)
    cfg = dict(rule_config or {})
    start = time.perf_counter()
    fn, scope = RULES[rule_id]
    path = source_inputs['java_file']
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', scope, ev, 'JAVA_PARSE_FAILED', time.perf_counter() - start)
    method_name = (target_binding or {}).get('method')
    method = select_method(facts, method_name)
    if method is None:
        return _obs('UNKNOWN', scope, ev, 'TARGET_METHOD_NOT_UNIQUE_OR_MISSING',
                    time.perf_counter() - start)
    ev.append({'method': method_name, 'start_line': method.get('start_line'),
               'end_line': method.get('end_line'),
               'params': method.get('params')})
    try:
        paths = _seq_paths(method['body'])
    except _TooManyPaths as e:
        return _obs('UNKNOWN', scope, ev, f'TOO_MANY_CONTROL_FLOW_PATHS:{e}',
                    time.perf_counter() - start)
    ev.append({'path_count': len(paths),
               'path_exits': [ex or 'FALLTHROUGH' for _, ex in paths]})
    verdict, reason, detail = fn(rule_id, paths, cfg)
    ev.append(detail)
    if verdict is None:
        src = _method_source(path, method)
        if 'try (' in src:
            reason = 'TRY_WITH_RESOURCES_NOT_SERIALISED:' + reason
        return _obs('UNKNOWN', scope, ev, reason, time.perf_counter() - start)
    return _obs(verdict, scope, ev, reason, time.perf_counter() - start)
