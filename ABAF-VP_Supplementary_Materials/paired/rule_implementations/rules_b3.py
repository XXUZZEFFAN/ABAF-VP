"""B3 rule family: window security flag coverage, content-provider call permission,
intent-extra null handling, external-storage writes, runtime permission context,
clipboard exposure.

verify(rule_id, source_inputs, target_binding, rule_config) -> {
    'observation': 'PRESENT'|'ABSENT'|'UNKNOWN', 'scope': str,
    'evidence': list, 'reason': str, 'duration_s': float}

AST first: every control-flow / object-binding claim below is derived from
javaparse.JavaFactsDeep nodes. Source text is used only to (a) locate candidate
files, (b) resolve a field's declared type, and (c) read the sub-expressions that
JavaFactsDeep collapses into a single `text` node (binary/ternary/array-creation
expressions). Collapsed text is combined with the enclosing AST context
(if/try/loop branch, receiver identity), never used alone to prove safety.
Checkers never read reference labels, repair diffs or expected answers.
"""
import pathlib
import re
import time
import xml.etree.ElementTree as ET

from javaparse import facts_for

ANDROID = '{http://schemas.android.com/apk/res/android}'


def _obs(observation, scope, evidence, reason, duration_s=0.0):
    return {'observation': observation, 'scope': scope, 'evidence': evidence,
            'reason': reason, 'duration_s': duration_s}


# --------------------------------------------------------------------------- AST

def _iter_nodes(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from _iter_nodes(v)
    elif isinstance(node, list):
        for v in node:
            yield from _iter_nodes(v)


def _invocations(node, out=None):
    if out is None:
        out = []
    for n in _iter_nodes(node):
        if n.get('kind') == 'METHOD_INVOCATION':
            out.append(n)
    return out


def _new_classes(node):
    return [n for n in _iter_nodes(node) if n.get('kind') == 'NEW_CLASS']


def _call_name(call):
    return (call.get('select') or {}).get('name') or ''


def _call_receiver(call):
    return (call.get('select') or {}).get('receiver') or {}


def _args(call):
    return call.get('args') or []


def _arg_text(node):
    if not isinstance(node, dict):
        return ''
    if 'text' in node:
        return str(node['text'])
    if 'value' in node:
        return str(node['value'])
    if node.get('kind') == 'IDENTIFIER':
        return str(node.get('name') or '')
    if node.get('kind') == 'MEMBER_SELECT':
        return (_arg_text(node.get('receiver')) + '.' + str(node.get('name') or ''))
    if node.get('kind') == 'METHOD_INVOCATION':
        name = _call_name(node)
        return (name + '(...)') if name else 'invocation'
    return ''


def _text_contains(node, token):
    if isinstance(node, list):
        return any(_text_contains(v, token) for v in node)
    if not isinstance(node, dict):
        return False
    if token in str(node.get('text') or ''):
        return True
    if token == node.get('name'):
        return True
    return any(_text_contains(v, token) for v in node.values() if isinstance(v, (dict, list)))


def _literal(node):
    if isinstance(node, dict) and str(node.get('kind', '')).endswith('LITERAL'):
        return node.get('value')
    return None


def _class_name(facts, path):
    stem = pathlib.Path(path).stem
    named = [t['owner'].strip('/') for t in facts.get('types', [])
             if t.get('owner', '').count('/') == 1 and t['owner'].strip('/') not in ('anonymous', '')]
    if stem in named:
        return stem
    return named[0] if named else stem


def _methods_of_class(facts, cls_name):
    """Target component's own methods incl. methods of its anonymous inner classes."""
    prefix = '/' + cls_name
    return [m for m in facts.get('methods', [])
            if m['owner'] == prefix or m['owner'].startswith(prefix + '/')]


def _unique_method(facts, name):
    ms = [m for m in facts.get('methods', []) if m['name'] == name and m.get('has_body')]
    return ms[0] if len(ms) == 1 else None


# ---------------------------------------------------------------------- manifest

def _parse_manifest(path):
    try:
        return ET.parse(path).getroot()
    except Exception:
        return None


def _app(root):
    return root.find('application') if root is not None and root.tag == 'manifest' else None


def _find_component(root, tag, cls_name):
    app = _app(root)
    if app is None:
        return None
    for el in app.findall(tag):
        name = el.get(ANDROID + 'name') or ''
        if name.split('.')[-1] == cls_name:
            return el
    return None


def _exported(el):
    if el is None:
        return False
    attr = (el.get(ANDROID + 'exported') or '').lower()
    if attr in ('true', 'false'):
        return attr == 'true'
    return len(el.findall('intent-filter')) > 0


def _permission_element(root, name):
    if root is None or not name:
        return None
    for el in root.findall('permission'):
        if el.get(ANDROID + 'name') == name:
            return el
    return None


def _permission_level(root, name):
    el = _permission_element(root, name)
    if el is None:
        return None
    return (el.get(ANDROID + 'protectionLevel') or 'normal').strip()


def _declares_uses(root, name):
    return root is not None and name is not None and any(
        el.get(ANDROID + 'name') == name for el in root.findall('uses-permission'))


# ---------------------------------------------------------------- window security

class _JavaModule:
    """Class graph for the passphrase-protected screen family.

    Candidate files are located by text (interface / mixin / secure-flag names);
    every inheritance and lifecycle claim is then taken from the JDK AST.
    """

    _FIELD_NEW = re.compile(r'\b([A-Z][\w$]*)\s+(\w+)\s*=\s*new\s+\1\s*\(')
    _FIELD_DECL = re.compile(r'\b([A-Z][\w$]*)\s+(\w+)\s*;')
    _ABSTRACT = re.compile(r'\babstract\s+class\s+([A-Za-z_$][\w$]*)')

    def __init__(self, root, keywords):
        self.root = pathlib.Path(root)
        self.classes = {}
        self.facts = {}
        self.fields = {}
        self._load(keywords)

    def _load(self, keywords):
        for p in sorted(self.root.rglob('*.java')):
            try:
                text = p.read_text(errors='ignore')
            except OSError:
                continue
            if not any(k in text for k in keywords):
                continue
            facts = facts_for(p)
            self.facts[p] = facts
            abstract = set(self._ABSTRACT.findall(text))
            field_types = {}
            for m in self._FIELD_NEW.finditer(text):
                field_types[m.group(2)] = m.group(1)
            for m in self._FIELD_DECL.finditer(text):
                field_types.setdefault(m.group(2), m.group(1))
            for t in facts.get('types', []):
                owner = t.get('owner', '')
                if owner.count('/') != 1:
                    continue
                name = owner.strip('/')
                if not name:
                    continue
                self.classes[name] = {
                    'file': p, 'extends': _simple_type(t.get('extends')),
                    'implements': _type_list(t.get('implements')),
                    'abstract': name in abstract}
                self.fields[name] = field_types

    def extends(self, cls):
        return (self.classes.get(cls) or {}).get('extends')

    def field_type(self, cls, var):
        return (self.fields.get(cls) or {}).get(var)

    def method(self, cls, name):
        for p, facts in self.facts.items():
            if p != (self.classes.get(cls) or {}).get('file'):
                continue
            for m in facts.get('methods', []):
                if m['owner'] == '/' + cls and m['name'] == name and m.get('has_body'):
                    return m
        return None

    def implements_passphrase(self, cls, iface, seen=None):
        seen = seen or set()
        if cls in seen or cls not in self.classes:
            return False
        seen.add(cls)
        info = self.classes[cls]
        if iface in info['implements']:
            return True
        return self.implements_passphrase(info['extends'], iface, seen)

    def parents(self):
        return {info['extends'] for info in self.classes.values() if info['extends']}


def _simple_type(text):
    if not text:
        return ''
    text = str(text).split('<')[0].strip()
    if text in ('null', 'None'):
        return ''
    return text.split('.')[-1]


def _type_list(text):
    if not text:
        return []
    return [_simple_type(t) for t in re.split(r'[,\[\]\s]+', str(text)) if t and t != 'null']


def _has_secure_flag(method, cfg):
    token = cfg.get('secure_flag', 'FLAG_SECURE')
    setters = set(cfg.get('flag_setters', ['addFlags', 'setFlags']))
    if any(_call_name(c) in setters and _text_contains(c, token)
           for c in _invocations(method['body'])):
        return True
    # flag constant assigned through a local alias variable
    aliases = {st.get('name') for st in _iter_nodes(method['body'])
               if st.get('kind') == 'VARIABLE' and _text_contains(st.get('init') or {}, token)}
    if not aliases:
        return False
    return any(_call_name(c) in setters
               and any((a.get('kind') == 'IDENTIFIER' and a.get('name') in aliases)
                       for a in _args(c))
               for c in _invocations(method['body']))


def _method_applies_secure(module, cls, name, cfg, lifecycle, depth=0, seen=None):
    seen = seen or set()
    key = (cls, name)
    if depth > 4 or key in seen:
        return False, 'RECURSION_LIMIT'
    seen.add(key)
    method = module.method(cls, name)
    if method is None:
        return False, 'NO_METHOD'
    if _has_secure_flag(method, cfg):
        return True, 'FLAG_SECURE_IN_%s.%s' % (cls, name)
    for call in _invocations(method['body']):
        cname = _call_name(call)
        recv = _call_receiver(call)
        recv_name = recv.get('name') or ''
        if cname != name and module.method(cls, cname):
            ok, why = _method_applies_secure(module, cls, cname, cfg, lifecycle, depth + 1, set(seen))
            if ok:
                return True, why
        if cname == lifecycle and recv_name == 'super':
            parent = module.extends(cls)
            if parent:
                ok, why = _method_applies_secure(module, parent, lifecycle, cfg, lifecycle,
                                                 depth + 1, set(seen))
                if ok:
                    return True, why
        if cname == lifecycle and recv_name:
            delegate = module.field_type(cls, recv_name)
            if delegate and delegate in module.classes:
                ok, why = _method_applies_secure(module, delegate, lifecycle, cfg, lifecycle,
                                                 depth + 1, set(seen))
                if ok:
                    return True, why
    return False, 'NO_FLAG_SECURE_IN_%s.%s' % (cls, name)


def _screen_covered(module, cls, iface, cfg, lifecycle, depth=0, seen=None):
    seen = seen or set()
    if cls in seen or depth > 6:
        return False, 'CHAIN_LIMIT'
    seen.add(cls)
    if module.method(cls, lifecycle) is not None:
        return _method_applies_secure(module, cls, lifecycle, cfg, lifecycle, 0, set())
    parent = module.extends(cls)
    if parent and parent in module.classes:
        return _screen_covered(module, parent, iface, cfg, lifecycle, depth + 1, set(seen))
    return False, 'NO_LIFECYCLE_METHOD_UP_TO_CHAIN_ROOT'


def _check_window_secure(inputs, binding, cfg):
    start = time.perf_counter()
    root = pathlib.Path(inputs['source_root'])
    iface = binding.get('protected_interface', 'PassphraseRequiredActivity')
    mixin = binding.get('mixin_class', 'PassphraseRequiredMixin')
    lifecycle = binding.get('lifecycle', 'onResume')
    prefix = cfg.get('base_name_prefix', 'PassphraseRequired')
    keywords = cfg.get('locate_keywords') or [mixin, iface, prefix, cfg.get('secure_flag', 'FLAG_SECURE')]
    ev = [{'source_root': str(root), 'tree_sha256': inputs.get('source_tree_sha256', '')}]
    if not root.exists():
        return _obs('UNKNOWN', 'secure-window flag coverage', ev, 'SOURCE_ROOT_MISSING',
                    time.perf_counter() - start)
    module = _JavaModule(root, keywords)
    if mixin not in module.classes:
        return _obs('UNKNOWN', 'secure-window flag coverage', ev, 'MIXIN_CLASS_NOT_FOUND',
                    time.perf_counter() - start)
    base_names = set(module.parents())
    screens = []
    for cls, info in module.classes.items():
        if cls == mixin or info['abstract']:
            continue
        if not module.implements_passphrase(cls, iface):
            continue
        if cls in base_names or cls.startswith(prefix):
            continue
        screens.append(cls)
    if not screens:
        return _obs('UNKNOWN', 'secure-window flag coverage', ev, 'NO_PASSPHRASE_PROTECTED_SCREENS',
                    time.perf_counter() - start)
    rows, uncovered = [], []
    for cls in sorted(screens):
        covered, via = _screen_covered(module, cls, iface, cfg, lifecycle)
        rows.append({'screen': cls, 'file': str(module.classes[cls]['file'].relative_to(root)),
                     'covered': covered, 'via': via})
        if not covered:
            uncovered.append(cls)
    ev.append({'screens_evaluated': len(rows), 'screens': rows})
    dur = time.perf_counter() - start
    if uncovered:
        return _obs('PRESENT', 'FLAG_SECURE coverage over passphrase-protected screens', ev,
                    'UNCOVERED_PASSPHRASE_SCREENS:%d:%s' % (len(uncovered), ','.join(uncovered)), dur)
    return _obs('ABSENT', 'FLAG_SECURE coverage over passphrase-protected screens', ev,
                'ALL_PASSPHRASE_SCREENS_APPLY_FLAG_SECURE', dur)


# ------------------------------------------------------- provider call() permission

def _data_sinks(method, cfg):
    sinks = set(cfg.get('sink_methods', []))
    sink_types = set(cfg.get('sink_types', []))
    found = []
    for call in _invocations(method['body']):
        if _call_name(call) in sinks:
            found.append({'kind': 'call', 'name': _call_name(call)})
    for nc in _new_classes(method['body']):
        if nc.get('type') in sink_types:
            found.append({'kind': 'new', 'type': nc.get('type')})
    return found


def _check_provider_call(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'ContentProvider.call() operation permission', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    cls = _class_name(facts, path)
    method = _unique_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'ContentProvider.call() operation permission', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    ev.append({'provider_class': cls, 'method': binding['method'],
               'start_line': method.get('start_line')})
    root = _parse_manifest(inputs['manifest'])
    if root is None:
        return _obs('UNKNOWN', 'ContentProvider.call() operation permission', ev,
                    'MANIFEST_UNPARSEABLE', time.perf_counter() - start)
    provider = _find_component(root, 'provider', cls)
    ev.append({'manifest': str(inputs['manifest']), 'provider_found': provider is not None})
    if provider is None:
        return _obs('UNKNOWN', 'ContentProvider.call() operation permission', ev,
                    'PROVIDER_DECLARATION_NOT_FOUND', time.perf_counter() - start)
    perm = provider.get(ANDROID + 'permission')
    read_perm = provider.get(ANDROID + 'readPermission')
    write_perm = provider.get(ANDROID + 'writePermission')
    exported = _exported(provider)
    sinks = _data_sinks(method, cfg)
    ev.append({'exported': exported, 'android:permission': perm,
               'android:readPermission': read_perm, 'android:writePermission': write_perm,
               'data_operations': sinks})
    dur = time.perf_counter() - start
    if not exported:
        return _obs('ABSENT', 'ContentProvider.call() operation permission', ev,
                    'PROVIDER_NOT_EXPORTED', dur)
    if perm:
        return _obs('ABSENT', 'ContentProvider.call() operation permission', ev,
                    'PROVIDER_LEVEL_PERMISSION_DECLARED', dur)
    if not sinks:
        return _obs('ABSENT', 'ContentProvider.call() operation permission', ev,
                    'CALL_PATH_HAS_NO_DATA_OPERATION', dur)
    return _obs('PRESENT', 'ContentProvider.call() operation permission', ev,
                'CALL_PATH_LACKS_PROVIDER_LEVEL_PERMISSION'
                '(read/writePermission_do_not_gate_call)', dur)


# ------------------------------------------------------------ intent extra nullness

_TERMINATORS = ('RETURN', 'THROW')


def _terminates(stmt):
    if not isinstance(stmt, dict):
        return False
    if stmt.get('kind') in _TERMINATORS:
        return True
    if stmt.get('kind') == 'BLOCK':
        stmts = stmt.get('stmts') or []
        return bool(stmts) and _terminates(stmts[-1])
    return False


def _cond_text(cond):
    if not isinstance(cond, dict):
        return ''
    if cond.get('text'):
        return str(cond['text'])
    return _arg_text(cond)


def _null_guards(cond, positive=True):
    text = _cond_text(cond)
    if positive:
        names = re.findall(r'([A-Za-z_$][\w$]*)\s*!=\s*null', text)
        names += re.findall(r'null\s*!=\s*([A-Za-z_$][\w$]*)', text)
    else:
        names = re.findall(r'([A-Za-z_$][\w$]*)\s*==\s*null', text)
        names += re.findall(r'null\s*==\s*([A-Za-z_$][\w$]*)', text)
    return set(names)


class _ExtraAnalyzer:
    """Tracks values read from intent extras and where they get dereferenced."""

    def __init__(self, getters, cfg):
        self.getters = set(getters)
        self.cfg = cfg
        self.extra = set()
        self.findings = []
        self.guarded = []

    def analyze(self, method):
        self.extra = set()
        self._stmts(method['body'], {'npe': False, 'null_ok': set(), 'method': method['name']})

    def _stmts(self, stmts, ctx):
        local_null = set(ctx['null_ok'])
        for st in stmts or []:
            self._stmt(st, dict(ctx, null_ok=local_null))
            if st.get('kind') == 'IF' and _terminates(st.get('then')):
                local_null |= _null_guards(st.get('cond'), positive=False)

    def _stmt(self, st, ctx):
        if not isinstance(st, dict):
            return
        kind = st.get('kind')
        if kind == 'VARIABLE':
            init = st.get('init')
            self._expr(init, ctx)
            name = st.get('name') or ''
            if self._is_extra_read(init):
                self.extra.add(name)
            elif isinstance(init, dict) and init.get('kind') == 'IDENTIFIER' and init.get('name') in self.extra:
                self.extra.add(name)
            return
        if kind in ('EXPRESSION_STATEMENT', 'RETURN', 'THROW'):
            self._expr(st.get('expr'), ctx)
            return
        if kind == 'BLOCK':
            self._stmts(st.get('stmts'), ctx)
            return
        if kind == 'IF':
            self._expr(st.get('cond'), ctx)
            then_ctx = dict(ctx, null_ok=ctx['null_ok'] | _null_guards(st.get('cond'), True))
            self._stmt(st.get('then'), then_ctx)
            else_ctx = dict(ctx, null_ok=ctx['null_ok'] | _null_guards(st.get('cond'), False))
            self._stmt(st.get('else'), else_ctx)
            return
        if kind == 'TRY':
            body_ctx = dict(ctx, npe=ctx['npe'] or self._catches_npe(st))
            self._stmt(st.get('body'), body_ctx)
            for c in st.get('catches') or []:
                self._stmt(c.get('body'), ctx)
            self._stmt(st.get('finally'), ctx)
            return
        if kind in ('FOR_LOOP', 'WHILE_LOOP', 'DO_WHILE_LOOP'):
            self._expr(st.get('cond'), ctx)
            self._stmt(st.get('body'), ctx)
            return
        if kind == 'ENHANCED_FOR_LOOP':
            self._expr(st.get('expr'), ctx)
            self._stmt(st.get('body'), ctx)
            return
        if kind == 'SWITCH':
            self._expr(st.get('expr'), ctx)
            for c in st.get('cases') or []:
                self._stmts(c.get('body'), ctx)
            return
        if kind == 'SYNCHRONIZED':
            self._stmt(st.get('body'), ctx)
            return
        self._expr(st, ctx)

    def _catches_npe(self, try_node):
        for c in try_node.get('catches') or []:
            param = c.get('param') or {}
            typ = param.get('type') or ''
            if _simple_type(typ) in ('NullPointerException', 'RuntimeException',
                                     'Exception', 'Throwable'):
                return True
        return False

    def _is_extra_read(self, expr):
        if not isinstance(expr, dict) or expr.get('kind') != 'METHOD_INVOCATION':
            return False
        name = _call_name(expr)
        if name in self.getters:
            return True
        recv = _call_receiver(expr)
        return (name in ('getString', 'getInt', 'getBoolean')
                and (_call_name(recv) == 'getExtras'
                     or (recv.get('kind') == 'MEMBER_SELECT' and recv.get('name') == 'getExtras')))

    def _expr(self, node, ctx):
        if not isinstance(node, dict):
            return
        if 'text' in node and node.get('kind') not in ('VARIABLE', 'IDENTIFIER', 'MEMBER_SELECT'):
            self._scan_text(node['text'], ctx)
        kind = node.get('kind')
        if kind == 'METHOD_INVOCATION':
            recv = _call_receiver(node)
            if recv.get('kind') == 'IDENTIFIER' and recv.get('name') in self.extra:
                self._deref(recv['name'], ctx, node)
            self._expr(recv, ctx)
            for a in _args(node):
                self._expr(a, ctx)
            return
        if kind == 'MEMBER_SELECT':
            recv = node.get('receiver') or {}
            if recv.get('kind') == 'IDENTIFIER' and recv.get('name') in self.extra:
                self._deref(recv['name'], ctx, node)
            self._expr(recv, ctx)
            return
        for key in ('select', 'receiver', 'init', 'expr', 'variable', 'cond'):
            if key in node:
                self._expr(node[key], ctx)
        for key in ('args', 'stmts', 'body', 'then', 'else'):
            val = node.get(key)
            if isinstance(val, list):
                for v in val:
                    self._expr(v, ctx)

    def _scan_text(self, text, ctx):
        for var in list(self.extra):
            if re.search(r'(?<![\w.$])' + re.escape(var) + r'\s*\.', text):
                self._deref(var, ctx, {'text': text})

    def _deref(self, var, ctx, node):
        if ctx.get('npe') or var in ctx.get('null_ok', set()):
            self.guarded.append({'var': var, 'method': ctx.get('method'),
                                 'site': node.get('text') or _call_name(node)})
            return
        self.findings.append({'var': var, 'method': ctx.get('method'),
                              'site': node.get('text') or _call_name(node)})


def _check_intent_extra(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'intent extra null handling', ev, 'JAVA_PARSE_FAILED',
                    time.perf_counter() - start)
    cls = _class_name(facts, path)
    methods = _methods_of_class(facts, cls)
    target = [m for m in methods if m['name'] == binding['method'] and m.get('has_body')]
    if not target:
        return _obs('UNKNOWN', 'intent extra null handling', ev,
                    'TARGET_METHOD_MISSING', time.perf_counter() - start)
    analyzer = _ExtraAnalyzer(cfg['extra_getters'], cfg)
    for m in methods:
        analyzer.analyze(m)
    ev.append({'class': cls, 'target_method': binding['method'],
               'methods_scanned': [m['name'] for m in methods],
               'extra_vars': sorted(analyzer.extra),
               'unguarded_dereferences': analyzer.findings,
               'guarded_dereferences': analyzer.guarded[:20]})
    dur = time.perf_counter() - start
    if analyzer.findings:
        return _obs('PRESENT', 'unchecked intent-extra dereference in component entry path', ev,
                    'UNGUARDED_EXTRA_DEREFERENCE:%d' % len(analyzer.findings), dur)
    if analyzer.extra:
        return _obs('ABSENT', 'unchecked intent-extra dereference in component entry path', ev,
                    'EXTRA_VALUES_NULL_GUARDED_OR_NPE_HANDLED', dur)
    return _obs('UNKNOWN', 'unchecked intent-extra dereference in component entry path', ev,
                'NO_INTENT_EXTRA_READ', dur)


# ------------------------------------------------------------ external storage write

def _dir_kind(node, cfg):
    if not isinstance(node, dict):
        return None
    if node.get('kind') == 'METHOD_INVOCATION':
        name = _call_name(node)
        if name in cfg.get('external_dir_methods', []):
            return 'external'
        if name in cfg.get('internal_dir_methods', []):
            return 'internal'
    return None


def _resolve_file_kind(node, file_kinds, cfg):
    if not isinstance(node, dict):
        return None
    if node.get('kind') == 'IDENTIFIER':
        return file_kinds.get(node.get('name'))
    if node.get('kind') == 'NEW_CLASS':
        kind = _dir_kind((node.get('args') or [{}])[0], cfg)
        if kind:
            return kind
        return _resolve_file_kind((node.get('args') or [{}])[0], file_kinds, cfg)
    return _dir_kind(node, cfg)


class _StorageAnalyzer:
    def __init__(self, cfg):
        self.cfg = cfg
        self.file_kinds = {}
        self.streams = {}
        self.tainted = set()
        self.writes = []
        self.sources = []

    def analyze(self, methods):
        for m in methods:
            self._walk_list(m['body'])

    def _walk_list(self, stmts):
        for st in stmts or []:
            self._walk(st)

    def _walk(self, node):
        if isinstance(node, list):
            self._walk_list(node)
            return
        if not isinstance(node, dict):
            return
        if node.get('kind') == 'VARIABLE':
            self._var(node)
        if node.get('kind') == 'METHOD_INVOCATION':
            self._call(node)
        for key, val in node.items():
            if key in ('name', 'type', 'kind', 'text', 'value', 'select'):
                continue
            if isinstance(val, (dict, list)):
                self._walk(val)

    def _var(self, st):
        name = st.get('name') or ''
        init = st.get('init')
        kind = _resolve_file_kind(init, self.file_kinds, self.cfg)
        if kind:
            self.file_kinds[name] = kind
        if isinstance(init, dict) and init.get('kind') == 'NEW_CLASS' \
                and init.get('type') in self.cfg.get('stream_types', []):
            arg0 = (init.get('args') or [{}])[0]
            target = _resolve_file_kind(arg0, self.file_kinds, self.cfg)
            if target:
                self.streams[name] = target
        if self._tainted(init):
            self.tainted.add(name)

    def _call(self, call):
        name = _call_name(call)
        recv = _call_receiver(call)
        args = _args(call)
        if name in self.cfg.get('sensitive_sources', []):
            self.sources.append({'method': name})
            # taint the variable receiving the source in an assignment context
        if name in self.cfg.get('propagators', []) and args:
            base = self._tainted(recv)
            if base:
                for a in args:
                    if a.get('kind') == 'IDENTIFIER':
                        self.tainted.add(a['name'])
        if name in self.cfg.get('write_methods', []) and recv.get('kind') == 'IDENTIFIER':
            stream = recv.get('name')
            if stream in self.streams:
                self.writes.append({'stream': stream, 'target': self.streams[stream],
                                    'tainted': self._tainted(args[0]) if args else False,
                                    'data_expr': _arg_text(args[0]) if args else ''})

    def _tainted(self, node):
        if not isinstance(node, dict):
            return False
        if node.get('kind') == 'IDENTIFIER':
            return node.get('name') in self.tainted
        if node.get('kind') == 'METHOD_INVOCATION':
            if _call_name(node) in self.cfg.get('sensitive_sources', []):
                return True
            if self._tainted(_call_receiver(node)):
                return True
            return any(self._tainted(a) for a in _args(node))
        if node.get('kind') == 'MEMBER_SELECT':
            return self._tainted(node.get('receiver'))
        if node.get('kind') == 'NEW_CLASS':
            return any(self._tainted(a) for a in node.get('args') or [])
        return any(self._tainted(v) for v in node.values() if isinstance(v, (dict, list)))


def _check_external_storage(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'sensitive data written to external storage', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    cls = _class_name(facts, path)
    methods = [m for m in _methods_of_class(facts, cls) if m.get('has_body')]
    if not any(m['name'] == binding['method'] for m in methods):
        return _obs('UNKNOWN', 'sensitive data written to external storage', ev,
                    'TARGET_METHOD_MISSING', time.perf_counter() - start)
    analyzer = _StorageAnalyzer(cfg)
    analyzer.analyze(methods)
    ev.append({'class': cls, 'target_method': binding['method'],
               'file_targets': analyzer.file_kinds, 'streams': analyzer.streams,
               'writes': analyzer.writes, 'sensitive_sources': analyzer.sources[:10]})
    dur = time.perf_counter() - start
    if not analyzer.writes:
        return _obs('UNKNOWN', 'sensitive data written to external storage', ev,
                    'NO_FILE_WRITE_IN_TARGET_METHOD', dur)
    risky = [w for w in analyzer.writes if w['target'] == 'external' and w['tainted']]
    if risky:
        return _obs('PRESENT', 'sensitive data written to external storage', ev,
                    'SENSITIVE_WRITE_TO_EXTERNAL_STORAGE:%d' % len(risky), dur)
    if any(w['target'] == 'external' for w in analyzer.writes):
        return _obs('ABSENT', 'sensitive data written to external storage', ev,
                    'EXTERNAL_WRITE_WITHOUT_SENSITIVE_SOURCE', dur)
    return _obs('ABSENT', 'sensitive data written to external storage', ev,
                'WRITES_TARGET_INTERNAL_STORAGE', dur)


# ------------------------------------------------- runtime permission on component

def _sensitive_sinks(method, cfg):
    names = set(cfg.get('sensitive_methods', []))
    return [{'call': _call_name(c), 'receiver': _call_receiver(c).get('name')}
            for c in _invocations(method['body']) if _call_name(c) in names]


def _runtime_permission_call(method, api):
    for call in _invocations(method['body']):
        if _call_name(call) == api:
            args = _args(call)
            perm = _literal(args[0]) if args else None
            return {'api': api, 'permission': perm, 'via': 'ast_invocation',
                    'checks_return_value': _checks_return_value(method, api)}
    # the call may sit inside a collapsed binary condition (e.g. == PERMISSION_GRANTED);
    # the constant kind + text keep the enclosing structural context available.
    pattern = re.compile(re.escape(api) + r'\s*\(\s*"([^"]+)"')
    for node in _iter_nodes(method['body']):
        text = str(node.get('text') or '')
        m = pattern.search(text)
        if m:
            return {'api': api, 'permission': m.group(1), 'via': 'collapsed_expression_text',
                    'checks_return_value': bool(re.search(
                        re.escape(api) + r'\s*\([^)]*\)\s*(==|!=)', text))}
    return None


def _checks_return_value(method, api):
    text = ' '.join(str(n.get('text') or '') for n in _iter_nodes(method['body']))
    return bool(re.search(re.escape(api) + r'\s*\([^)]*\)\s*(==|!=)', text))


def _check_runtime_permission(inputs, binding, cfg, rule_id):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'system-enforced component permission', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    cls = _class_name(facts, path)
    method = _unique_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'system-enforced component permission', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    root = _parse_manifest(inputs['manifest'])
    if root is None:
        return _obs('UNKNOWN', 'system-enforced component permission', ev,
                    'MANIFEST_UNPARSEABLE', time.perf_counter() - start)
    service = _find_component(root, 'service', cls)
    if service is None:
        return _obs('UNKNOWN', 'system-enforced component permission', ev,
                    'SERVICE_DECLARATION_NOT_FOUND', time.perf_counter() - start)
    app = _app(root)
    service_perm = service.get(ANDROID + 'permission') or (app.get(ANDROID + 'permission') if app is not None else None)
    level = _permission_level(root, service_perm) if service_perm else None
    signature = bool(level and 'signature' in level)
    runtime = _runtime_permission_call(method, cfg['runtime_api'])
    sinks = _sensitive_sinks(method, cfg)
    self_granted = False
    if runtime and runtime['permission']:
        plevel = _permission_level(root, runtime['permission'])
        self_granted = bool(plevel and 'signature' not in plevel
                            and _declares_uses(root, runtime['permission']))
    exported = _exported(service)
    ev.append({'service_class': cls, 'exported': exported,
               'service_permission': service_perm, 'permission_protection_level': level,
               'runtime_check': runtime, 'runtime_permission_self_granted': self_granted,
               'sensitive_operations': sinks})
    dur = time.perf_counter() - start
    scope = 'system-enforced component permission vs runtime self-check (%s)' % cfg['runtime_api']
    if not exported:
        return _obs('ABSENT', scope, ev, 'SERVICE_NOT_EXPORTED', dur)
    if service_perm and level is None:
        return _obs('UNKNOWN', scope, ev, 'SERVICE_PERMISSION_NOT_DECLARED', dur)
    if service_perm and signature:
        return _obs('ABSENT', scope, ev, 'SERVICE_PERMISSION_SIGNATURE_ENFORCED_BY_SYSTEM', dur)
    if service_perm and not signature:
        return _obs('PRESENT', scope, ev, 'SERVICE_PERMISSION_NOT_SIGNATURE_PROTECTED', dur)
    if not sinks:
        return _obs('UNKNOWN', scope, ev, 'NO_SENSITIVE_OPERATION_IN_TARGET_METHOD', dur)
    if runtime and self_granted:
        return _obs('PRESENT', scope, ev,
                    'RUNTIME_SELF_CHECK_DEFEATED_BY_SELF_GRANTED_PERMISSION', dur)
    if runtime and not self_granted:
        return _obs('ABSENT', scope, ev, 'RUNTIME_CHECK_NOT_SELF_GRANTED', dur)
    return _obs('PRESENT', scope, ev, 'SENSITIVE_SERVICE_EXPORTED_WITHOUT_SYSTEM_PERMISSION', dur)


# ------------------------------------------------------------------- clipboard

def _method_sensitive_names(methods, cfg):
    names = set()
    for m in methods:
        if _body_has_sensitive(m['body'], cfg):
            names.add(m['name'])
    return names


def _body_has_sensitive(body, cfg):
    for call in _invocations(body):
        if _call_name(call) in cfg.get('sensitive_getters', []):
            return True
    return False


def _value_sensitive(node, var_inits, sensitive_methods, cfg, depth=0):
    if depth > 5 or not isinstance(node, dict):
        return False
    if node.get('kind') == 'IDENTIFIER':
        init = var_inits.get(node.get('name'))
        return init is not None and _value_sensitive(init, var_inits, sensitive_methods, cfg, depth + 1)
    if node.get('kind') == 'METHOD_INVOCATION':
        if _call_name(node) in sensitive_methods:
            return True
    for call in _invocations(node):
        if _call_name(call) in cfg.get('sensitive_getters', []) \
                or _call_name(call) in sensitive_methods:
            return True
    for key in ('receiver', 'select', 'expr', 'init'):
        val = node.get(key)
        if isinstance(val, dict) and _value_sensitive(val, var_inits, sensitive_methods, cfg, depth + 1):
            return True
    return False


def _check_clipboard(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'sensitive content written to global clipboard', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    cls = _class_name(facts, path)
    methods = [m for m in _methods_of_class(facts, cls) if m.get('has_body')]
    if not any(m['name'] == binding['method'] for m in methods):
        return _obs('UNKNOWN', 'sensitive content written to global clipboard', ev,
                    'TARGET_METHOD_MISSING', time.perf_counter() - start)
    sensitive_methods = _method_sensitive_names(methods, cfg)
    findings, non_sensitive = [], []
    for m in methods:
        var_inits = {st.get('name'): st.get('init') for st in _iter_nodes(m['body'])
                     if st.get('kind') == 'VARIABLE'}
        for call in _invocations(m['body']):
            if _call_name(call) != cfg['clip_method']:
                continue
            args = _args(call)
            arg = args[0] if args else {}
            value, label = None, None
            if arg.get('kind') == 'IDENTIFIER' and arg.get('name') in var_inits:
                value = var_inits[arg['name']]
            else:
                value = arg
            if isinstance(value, dict) and value.get('kind') == 'METHOD_INVOCATION' \
                    and _call_name(value) == 'newPlainText':
                vargs = _args(value)
                label = _literal(vargs[0]) if vargs else None
                value = vargs[1] if len(vargs) > 1 else {}
            sensitive = _value_sensitive(value, var_inits, sensitive_methods, cfg)
            row = {'method': m['name'], 'label': label,
                   'value_expr': _arg_text(value), 'sensitive': sensitive}
            (findings if sensitive else non_sensitive).append(row)
    ev.append({'class': cls, 'sensitive_source_methods': sorted(sensitive_methods),
               'clipboard_writes': findings + non_sensitive})
    dur = time.perf_counter() - start
    if findings:
        return _obs('PRESENT', 'sensitive content written to global clipboard', ev,
                    'SENSITIVE_CONTENT_SET_AS_PRIMARY_CLIP:%d' % len(findings), dur)
    if non_sensitive:
        return _obs('ABSENT', 'sensitive content written to global clipboard', ev,
                    'PRIMARY_CLIP_CONTENT_IS_CONSTANT_OR_NON_SENSITIVE', dur)
    return _obs('UNKNOWN', 'sensitive content written to global clipboard', ev,
                'NO_PRIMARY_CLIP_WRITE', dur)


# --------------------------------------------------------------------- dispatch

CHECKERS = {
    'WINDOW_FLAG_SECURE_COVERAGE': _check_window_secure,
    'PROVIDER_CALL_OPERATION_PERMISSION': _check_provider_call,
    'INTENT_EXTRA_UNGUARDED_DEREFERENCE': _check_intent_extra,
    'EXTERNAL_STORAGE_SENSITIVE_WRITE': _check_external_storage,
    'CHECK_CALLING_OR_SELF_PERMISSION_SELF_GRANTED': _check_runtime_permission,
    'ENFORCE_CALLING_OR_SELF_PERMISSION_SELF_GRANTED': _check_runtime_permission,
    'CLIPBOARD_SENSITIVE_PRIMARY_CLIP': _check_clipboard,
}


RUNTIME_RULES = ('CHECK_CALLING_OR_SELF_PERMISSION_SELF_GRANTED',
                 'ENFORCE_CALLING_OR_SELF_PERMISSION_SELF_GRANTED')


def verify(rule_id, source_inputs, target_binding, rule_config):
    fn = CHECKERS[rule_id]
    if rule_id in RUNTIME_RULES:
        return fn(source_inputs, target_binding, rule_config, rule_id)
    return fn(source_inputs, target_binding, rule_config)
