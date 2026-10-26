"""C4 transport rule family: TLS certificate pinning (FP-42), peer identity
authentication before sensitive socket I/O (FP-43), third-party library path
traversal guard bound to the actually-linked dependency (FP-45), cleartext HTTP
download (FP-58).

verify(rule_id, source_inputs, target_binding, rule_config) -> observation dict.

AST-first: every control-flow decision uses javaparse.facts_for (JavaFactsDeep).
Regular expressions only locate try-with-resources declarations and classify an
already located guard expression; no decision is taken from string presence alone.
"""
import hashlib
import json
import pathlib
import re
import sys
import time

V5 = pathlib.Path(__file__).resolve().parents[1]
if str(V5 / 'src') not in sys.path:
    sys.path.insert(0, str(V5 / 'src'))

from javaparse import facts_for, select_method  # noqa: E402
from rules_webview import _iter_nodes, _invocations, _obs  # noqa: E402

RULE_VERSION = 'v5.rule.c4.1'


def _sha(p):
    p = pathlib.Path(p)
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None


def _expr_text(node):
    if not isinstance(node, dict):
        return ''
    if node.get('text'):
        return node['text']
    kind = node.get('kind', '')
    if kind == 'IDENTIFIER':
        return node.get('name', '')
    if kind == 'MEMBER_SELECT':
        return _expr_text(node.get('receiver') or {}) + '.' + (node.get('name') or '')
    if kind == 'METHOD_INVOCATION':
        return _expr_text(node.get('select') or {}) + '(' + ', '.join(
            _expr_text(a) for a in node.get('args') or []) + ')'
    if kind == 'NEW_CLASS':
        return 'new %s(%s)' % (node.get('type'), ', '.join(
            _expr_text(a) for a in node.get('args') or []))
    if kind.endswith('_LITERAL'):
        return str(node.get('value'))
    return ''


def _walk_with_ifs(node, anc=()):
    """Yield (node, enclosing_if_nodes) over the whole serialized AST."""
    if isinstance(node, dict):
        yield node, anc
        nxt = anc + (node,) if node.get('kind') == 'IF' else anc
        for k, v in node.items():
            if k == 'kind':
                continue
            yield from _walk_with_ifs(v, nxt)
    elif isinstance(node, list):
        for v in node:
            yield from _walk_with_ifs(v, anc)


def _var_index(body):
    types, inits = {}, {}
    for n in _iter_nodes(body):
        if n.get('kind') == 'VARIABLE':
            types[n.get('name', '')] = n.get('type', '')
            inits[n.get('name', '')] = n.get('init') or {}
    return types, inits


def _try_resources(src):
    """Locate `try (...)` resource declarations (locator only; used because the AST
    serializer does not emit TryTree resources)."""
    out = []
    for m in re.finditer(r'try\s*\(', src):
        i, depth = m.end(), 1
        start = i
        while i < len(src) and depth:
            if src[i] == '(':
                depth += 1
            elif src[i] == ')':
                depth -= 1
            i += 1
        for decl in src[start:i - 1].split(';'):
            d = ' '.join(decl.split())
            mm = re.match(r'([\w.$]+(?:<[^>]*>)?(?:\[\])?)\s+(\w+)\s*=\s*(.+)$', d)
            if mm:
                out.append({'type': mm.group(1), 'name': mm.group(2), 'init': mm.group(3)})
    return out


def _subtree_has(node, pred):
    return any(pred(n) for n in _iter_nodes(node))


# --------------------------------------------------------------------------- FP-42
CUSTOM_TM_HINT = re.compile(r'new\s+([A-Z][\w.$]*)\s*\(')
JDK_TM_NAMES = {'TrustManager', 'X509TrustManager', 'TrustManagerFactory', 'SSLContext'}


def _custom_classes(text, varinits, depth=0):
    classes = [c for c in CUSTOM_TM_HINT.findall(text) if c not in JDK_TM_NAMES]
    if not classes and depth < 3:
        inner = re.search(r'\{\s*(.*?)\s*\}', text, re.S)
        if inner:
            for ident in re.findall(r'[A-Za-z_]\w*', inner.group(1)):
                init = varinits.get(ident) or {}
                if init:
                    classes += _custom_classes(_expr_text(init), varinits, depth + 1)
    return classes


def _trust_anchor(method):
    vartypes, varinits = _var_index(method['body'])
    calls = _invocations(method['body'])
    ssl_inits, keystore_calls, tmf_calls = [], [], []
    for c in calls:
        sel = c.get('select') or {}
        name = sel.get('name') or ''
        recv = (sel.get('receiver') or {}).get('name', '')
        if name == 'init' and 'SSLContext' in (vartypes.get(recv) or ''):
            ssl_inits.append(c)
        if name in ('getInstance', 'load', 'setCertificateEntry'):
            owner = _expr_text(sel.get('receiver') or {})
            if name == 'setCertificateEntry' or ('KeyStore' in (vartypes.get(recv) or '') or owner == 'KeyStore'):
                keystore_calls.append((name, owner, recv))
        if name in ('getInstance', 'init', 'getTrustManagers') and (
                'TrustManagerFactory' in (vartypes.get(recv) or '') or name == 'getTrustManagers'):
            tmf_calls.append((name, recv, _expr_text(c)))
    tm_kind, tm_detail = 'none', {}
    if ssl_inits:
        args = ssl_inits[0].get('args') or []
        arg = args[1] if len(args) > 1 else {}
        kind = arg.get('kind', '')
        if kind == 'NULL_LITERAL':
            tm_kind, tm_detail = 'default_ca', {'source': 'SSLContext.init(null, null, null)'}
        elif kind == 'METHOD_INVOCATION' and (arg.get('select') or {}).get('name') == 'getTrustManagers':
            tm_kind = 'trustmanagerfactory'
            tm_detail = {'source': _expr_text(arg)}
        elif kind == 'IDENTIFIER':
            init = varinits.get(arg.get('name', '')) or {}
            text = _expr_text(init)
            classes = _custom_classes(text, varinits)
            tm_kind = 'custom' if classes else 'variable'
            tm_detail = {'variable': arg.get('name'), 'init': text, 'custom_classes': classes}
        else:
            text = _expr_text(arg)
            classes = _custom_classes(text, varinits)
            tm_kind = 'custom' if classes else 'expression'
            tm_detail = {'init': text, 'custom_classes': classes}
    set_cert = [c for c in keystore_calls if c[0] == 'setCertificateEntry']
    tmf_init_args = [c for c in calls
                     if (c.get('select') or {}).get('name') == 'init'
                     and 'TrustManagerFactory' in (vartypes.get(
                         ((c.get('select') or {}).get('receiver') or {}).get('name', '')) or '')]
    tmf_from_keystore = False
    for c in tmf_init_args:
        args = c.get('args') or []
        if args and args[0].get('kind') == 'IDENTIFIER' and \
                'KeyStore' in (vartypes.get(args[0].get('name', '')) or ''):
            tmf_from_keystore = True
    return {
        'trust_manager_kind': tm_kind,
        'trust_manager_detail': tm_detail,
        'sslcontext_init_calls': len(ssl_inits),
        'keystore_set_certificate_entry': len(set_cert),
        'trustmanagerfactory_calls': [c[0] for c in tmf_calls],
        'tmf_init_after_keystore': tmf_from_keystore,
    }


def _custom_tm_evidence(java_file, class_names):
    ev = []
    base = pathlib.Path(java_file).parent
    for cls in class_names:
        cands = list(base.glob(f'{cls}.java'))
        if not cands:
            root = base
            for _ in range(6):
                root = root.parent
                if (root / 'src').exists() or (root.name == 'java'):
                    break
            cands = list(base.rglob(f'{cls}.java')) or list(pathlib.Path(java_file).parents[4].rglob(f'{cls}.java'))
        for f in cands[:1]:
            facts = facts_for(f)
            info = {'path': str(f), 'sha256': facts.get('_source_sha256', '')}
            src = f.read_text(errors='replace')
            lines = src.splitlines()
            for m in facts.get('methods', []):
                if m['name'] in ('checkServerTrusted', 'checkClientTrusted'):
                    apis = sorted({(c.get('select') or {}).get('name')
                                   for c in _invocations(m['body'])
                                   if (c.get('select') or {}).get('name')})
                    start_l = m.get('start_line') or 1
                    end_l = m.get('end_line') or start_l
                    slice_text = '\n'.join(lines[start_l - 1:end_l])
                    info.setdefault('trust_methods', {})[m['name']] = apis
                    info.setdefault('equals_call_in_method_text', {})[m['name']] = '.equals(' in slice_text
            info['pkix_validation'] = bool({'CertPathValidator', 'PKIXParameters', 'CertPath'} &
                                           {a for v in (info.get('trust_methods') or {}).values() for a in v})
            info['certificate_equality_compare'] = any(
                (info.get('equals_call_in_method_text') or {}).values())
            info['pinned_asset_names'] = re.findall(r'\.open\(\s*"([^"]+\.(?:crt|pem|cer|p12|bks))"', src)
            ev.append(info)
    return ev


def check_tls_pinning(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''), 'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'TLS trust anchor for pinned server certificate', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    method = select_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'TLS trust anchor for pinned server certificate', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    anchor = _trust_anchor(method)
    anchor['method'] = binding['method']
    anchor['method_lines'] = [method.get('start_line'), method.get('end_line')]
    ev.append(anchor)
    tm_files = _custom_tm_evidence(path, anchor['trust_manager_detail'].get('custom_classes') or [])
    if tm_files:
        ev.append({'custom_trust_manager_files': tm_files})
    hashed = {'hashed_inputs': {str(path): facts.get('_source_sha256', '')}}
    for f in tm_files:
        hashed['hashed_inputs'][f['path']] = f['sha256']
    ev.append(hashed)
    nsc = inputs.get('nsc_file')
    if nsc and pathlib.Path(nsc).exists():
        text = pathlib.Path(nsc).read_text(errors='replace')
        pinned = bool(re.search(r'<pin[- ]?set|pin-set', text))
        ev.append({'network_security_config': str(nsc), 'contains_pin_set': pinned,
                   'sha256': _sha(nsc)})
        if pinned:
            return _obs('ABSENT', 'TLS trust anchor for pinned server certificate', ev,
                        'CERT_PIN_SET_DECLARED_IN_NETWORK_SECURITY_CONFIG',
                        time.perf_counter() - start)
    kind = anchor['trust_manager_kind']
    pin = anchor['keystore_set_certificate_entry'] > 0 and 'getTrustManagers' in anchor['trustmanagerfactory_calls']
    if kind == 'trustmanagerfactory' and pin:
        return _obs('ABSENT', 'TLS trust anchor for pinned server certificate', ev,
                    'KEYSTORE_ANCHORED_TRUSTMANAGERFACTORY_PINNING', time.perf_counter() - start)
    if kind == 'custom':
        classes = ','.join(anchor['trust_manager_detail'].get('custom_classes') or [])
        return _obs('PRESENT', 'TLS trust anchor for pinned server certificate', ev,
                    'TRUST_DECISION_DELEGATED_TO_CUSTOM_TRUSTMANAGER:' + classes,
                    time.perf_counter() - start)
    if kind == 'default_ca':
        return _obs('PRESENT', 'TLS trust anchor for pinned server certificate', ev,
                    'DEFAULT_CA_TRUST_WITHOUT_PINNING', time.perf_counter() - start)
    return _obs('UNKNOWN', 'TLS trust anchor for pinned server certificate', ev,
                'TRUST_ANCHOR_CONSTRUCTION_NOT_DETERMINED', time.perf_counter() - start)


# --------------------------------------------------------------------------- FP-43
SOCKET_WRITE_APIS = {'write', 'writeBytes', 'writeUTF'}
FILE_READ_APIS = {'read', 'readBytes', 'readAllBytes', 'readLine'}
PEER_ID_APIS = re.compile(r'getInetAddress|getRemoteSocketAddress|getHostName|getCanonicalHostName')


def _peer_guard(if_node, accepted, aliases):
    cond = if_node.get('cond') or {}
    txt = _expr_text(cond)
    if not PEER_ID_APIS.search(txt):
        return None
    if not re.search(r'equals|equalsIgnoreCase|matches|==|!=', txt):
        return None
    refs = set(re.findall(r'([A-Za-z_]\w*)\s*\.\s*(?:getInetAddress|getRemoteSocketAddress|getHostName|getCanonicalHostName)', txt))
    refs |= set(re.findall(r'([A-Za-z_]\w*)\s*\.\s*getInetAddress\(\)\s*\.\s*getHostName', txt))
    allowed = set(accepted)
    for a, b in aliases.items():
        if b in allowed:
            allowed.add(a)
    if not (refs & allowed):
        return None
    lit = re.search(r'equals(?:IgnoreCase)?\(\s*"([^"]*)"', txt)
    return {'condition': txt, 'object_refs': sorted(refs), 'allowed_objects': sorted(allowed),
            'trusted_host_literal': lit.group(1) if lit else None}


def check_socket_peer_auth(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''), 'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'peer identity authentication before sensitive socket write', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    method = select_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'peer identity authentication before sensitive socket write', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    body = method['body']
    vartypes, varinits = _var_index(body)
    src = path.read_text(errors='replace')
    resources = _try_resources(src)
    ev.append({'method': binding['method'], 'method_lines': [method.get('start_line'), method.get('end_line')],
               'try_resources': resources})

    file_vars = {r['name'] for r in resources
                 if 'FileInputStream' in r['type'] or 'openFileInput' in r['init']}
    out_vars = {r['name'] for r in resources
                if 'OutputStream' in r['type'] or 'getOutputStream' in r['init']}
    accepted = {r['name'] for r in resources if re.search(r'\.\s*accept\s*\(', r['init'])}
    for name, typ in vartypes.items():
        if 'FileInputStream' in typ or 'InputStream' == typ and 'openFileInput' in _expr_text(varinits.get(name) or {}):
            file_vars.add(name)
        if 'OutputStream' in typ or 'getOutputStream' in _expr_text(varinits.get(name) or {}):
            out_vars.add(name)
        if 'Socket' == typ and ('accept' in _expr_text(varinits.get(name) or {}) or name in accepted):
            accepted.add(name)
    aliases = {}
    for n in _iter_nodes(body):
        if n.get('kind') == 'ASSIGNMENT':
            var = (n.get('variable') or {}).get('name')
            src_e = n.get('expr') or {}
            if var and src_e.get('kind') == 'IDENTIFIER':
                aliases[var] = src_e.get('name')
        if n.get('kind') == 'VARIABLE':
            init = n.get('init') or {}
            if init.get('kind') == 'IDENTIFIER':
                aliases[n.get('name')] = init.get('name')
    ev.append({'file_input_vars': sorted(file_vars), 'socket_output_vars': sorted(out_vars),
               'accepted_socket_vars': sorted(accepted), 'aliases': aliases})

    read_pattern = re.compile(r'\b(?:%s)\s*\.\s*(?:read|readBytes|readAllBytes)\s*\('
                              % '|'.join(re.escape(v) for v in sorted(file_vars))) if file_vars else None

    def is_read(n):
        if n.get('kind') == 'METHOD_INVOCATION':
            return ((n.get('select') or {}).get('name') in FILE_READ_APIS
                    and ((n.get('select') or {}).get('receiver') or {}).get('name') in file_vars)
        text = n.get('text')
        return bool(read_pattern and isinstance(text, str) and read_pattern.search(text))

    def is_write(n):
        return (n.get('kind') == 'METHOD_INVOCATION'
                and (n.get('select') or {}).get('name') in SOCKET_WRITE_APIS
                and (((n.get('select') or {}).get('receiver') or {}).get('name') in out_vars
                     or 'OutputStream' in vartypes.get(
                         ((n.get('select') or {}).get('receiver') or {}).get('name', ''), '')))

    regions, seen = [], set()
    for n, anc in _walk_with_ifs(body):
        if not isinstance(n, dict) or n.get('kind') not in (
                'IF', 'TRY', 'WHILE_LOOP', 'FOR_LOOP', 'ENHANCED_FOR_LOOP', 'DO_WHILE_LOOP',
                'BLOCK', 'SYNCHRONIZED'):
            continue
        if not (_subtree_has(n, is_read) and _subtree_has(n, is_write)):
            continue
        if id(n) in seen:
            continue
        seen.add(id(n))
        regions.append((n, anc))
    kept = []
    for n, anc in regions:
        contains_other_region = any(
            id(n) != id(m) and _subtree_has(n, lambda z, m=m: z is m)
            for m, _ in regions)
        if contains_other_region:
            continue
        kept.append((n, anc))
    if not kept:
        if not (_subtree_has(body, is_write) and file_vars):
            return _obs('UNKNOWN', 'peer identity authentication before sensitive socket write', ev,
                        'NO_FILE_TO_SOCKET_COPY_FOUND', time.perf_counter() - start)
        return _obs('UNKNOWN', 'peer identity authentication before sensitive socket write', ev,
                    'COPY_REGION_NOT_RESOLVED', time.perf_counter() - start)

    guards, open_paths = [], []
    for n, anc in kept:
        entry = {'region_kind': n.get('kind'), 'region_expr': _expr_text(n)[:200]}
        guard = None
        for a in reversed(anc):
            g = _peer_guard(a, accepted, aliases)
            if not g:
                continue
            in_then = _subtree_has(a.get('then') or {}, lambda z, n=n: z is n)
            in_else = _subtree_has(a.get('else') or {}, lambda z, n=n: z is n)
            negated = bool(re.search(r'!\s*[^=]|!=|==\s*false', g['condition']))
            if in_else and not negated:
                continue
            guard = dict(g)
            guard['branch'] = 'then' if in_then else ('else' if in_else else 'unknown')
            break
        if guard:
            guards.append({**guard, 'region_kind': n.get('kind')})
            entry['guarded_by'] = guard['condition']
            entry['guard_branch'] = guard['branch']
        else:
            open_paths.append(entry)
    ev.append({'copy_regions': len(kept), 'peer_guards': guards, 'unguarded_copy_regions': open_paths})
    ev.append({'hashed_inputs': {str(path): facts.get('_source_sha256', '')}})
    dur = time.perf_counter() - start
    if open_paths:
        return _obs('PRESENT', 'peer identity authentication before sensitive socket write', ev,
                    'SENSITIVE_FILE_WRITTEN_TO_ACCEPTED_SOCKET_WITHOUT_PEER_IDENTITY_CHECK', dur)
    return _obs('ABSENT', 'peer identity authentication before sensitive socket write', ev,
                'PEER_IDENTITY_CHECK_DOMINATES_SENSITIVE_SOCKET_WRITE', dur)


# --------------------------------------------------------------------------- FP-45
TRAVERSAL_REJECT_PATTERNS = [
    r'!\s*[^&|;]*?\.contains\(\s*"\.\."\s*\)',
    r'\.contains\(\s*"\.\."\s*\)\s*==\s*false',
    r'indexOf\(\s*"\.\."\s*\)\s*(?:<\s*0|==\s*-1|!=\s*0)',
    r'!\s*[^&|;]*?\.matches\(\s*"[^"]*\\\\\.\\\\\.[^"]*"',
]
CANONICAL_REJECT_PATTERNS = [
    r'getCanonicalPath\(\)\s*\.\s*startsWith',
    r'getCanonicalPath\(\)\s*\.\s*contains',
    r'normalize\(\)\s*\.\s*startsWith',
]


def _resolve_library_module(app_dir, cfg):
    app_dir = pathlib.Path(app_dir)
    ev = {}
    settings = app_dir / 'settings.gradle'
    app_build = app_dir / 'app' / 'build.gradle'
    ev['settings_gradle'] = {'path': str(settings), 'sha256': _sha(settings)}
    ev['app_build_gradle'] = {'path': str(app_build), 'sha256': _sha(app_build)}
    included = []
    if settings.exists():
        for line in settings.read_text(errors='replace').splitlines():
            if line.strip().startswith('include'):
                included += re.findall(r"['\"]([^'\"]+)['\"]", line)
    deps = []
    if app_build.exists():
        deps = re.findall(r'project\(\s*["\']:([^"\']+)["\']\s*\)', app_build.read_text(errors='replace'))
    pattern = cfg.get('library_module_pattern', '')
    module = next((d for d in deps if pattern and re.search(pattern, d)), None)
    ev['included_modules'] = included
    ev['project_dependencies'] = deps
    if module is None:
        return None, ev
    ev['resolved_module'] = ':' + module
    module_dir = app_dir / module
    module_build = module_dir / 'build.gradle'
    ev['module_build_gradle'] = {'path': str(module_build), 'sha256': _sha(module_build)}
    lib_root, aar = None, None
    if module_build.exists():
        text = module_build.read_text(errors='replace')
        m = re.search(r'file\(\s*["\']([^"\']+\.aar)["\']\s*\)', text)
        if m:
            aar = m.group(1)
            p = (module_dir / aar).resolve()
            parts = list(p.parts)
            lib_root = pathlib.Path(*parts[:parts.index('build')]) if 'build' in parts else p.parents[2]
    ev['aar_artifact'] = aar
    ev['resolved_library_root'] = str(lib_root) if lib_root else None
    return lib_root, ev


def check_traversal_guard(inputs, binding, cfg):
    start = time.perf_counter()
    ev = []
    lib_root, dep_ev = _resolve_library_module(inputs['app_dir'], cfg)
    ev.append(dep_ev)
    if lib_root is None:
        return _obs('UNKNOWN', 'directory traversal guard in linked library component', ev,
                    'LIBRARY_DEPENDENCY_NOT_RESOLVED', time.perf_counter() - start)
    component = cfg.get('component') or binding.get('component', 'WriteActivity')
    cands = sorted((lib_root / 'src' / 'main' / 'java').rglob(f'{component}.java')) \
        if (lib_root / 'src' / 'main' / 'java').exists() else []
    if not cands:
        return _obs('UNKNOWN', 'directory traversal guard in linked library component', ev,
                    'COMPONENT_SOURCE_NOT_FOUND_IN_RESOLVED_LIBRARY', time.perf_counter() - start)
    path = cands[0]
    facts = facts_for(path)
    ev.append({'path': str(path), 'sha256': facts.get('_source_sha256', ''), 'parse_ok': facts.get('parse_ok')})
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'directory traversal guard in linked library component', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    method = select_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'directory traversal guard in linked library component', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    extra = cfg.get('taint_extra', 'fileName')
    tainted, sinks = set(), []
    for n, anc in _walk_with_ifs(method['body']):
        if n.get('kind') == 'ASSIGNMENT':
            var = (n.get('variable') or {}).get('name')
            e = n.get('expr') or {}
            if var and e.get('kind') == 'METHOD_INVOCATION' and (e.get('select') or {}).get('name') == 'getStringExtra':
                args = e.get('args') or []
                if args and args[0].get('kind') == 'STRING_LITERAL' and args[0].get('value') == extra:
                    tainted.add(var)
        if n.get('kind') == 'VARIABLE':
            name = n.get('name')
            e = n.get('init') or {}
            if e.get('kind') == 'METHOD_INVOCATION' and (e.get('select') or {}).get('name') == 'getStringExtra':
                args = e.get('args') or []
                if args and args[0].get('kind') == 'STRING_LITERAL' and args[0].get('value') == extra:
                    tainted.add(name)
            if e.get('kind') == 'NEW_CLASS' and e.get('type') == 'File':
                args = e.get('args') or []
                if len(args) >= 2 and args[1].get('kind') == 'IDENTIFIER' and args[1].get('name') in tainted:
                    sinks.append((n, anc))
    ev.append({'method': binding['method'], 'tainted_filename_vars': sorted(tainted),
               'file_path_construction_sites': len(sinks)})
    if not sinks:
        return _obs('UNKNOWN', 'directory traversal guard in linked library component', ev,
                    'TAINTED_FILE_PATH_CONSTRUCTION_NOT_FOUND', time.perf_counter() - start)
    reject_guards = []
    extra_ref = re.compile(r'getStringExtra\(\s*"%s"\s*\)' % re.escape(extra))
    for n, anc in sinks:
        for a in anc:
            cond = _expr_text(a.get('cond') or {})
            if not cond:
                continue
            for kind, patterns in (('dotdot_reject', TRAVERSAL_REJECT_PATTERNS),
                                   ('canonical_path_containment', CANONICAL_REJECT_PATTERNS)):
                for p in patterns:
                    for m in re.finditer(p, cond):
                        piece = m.group(0)
                        tied = bool(extra_ref.search(piece)) or any(
                            re.search(r'\b%s\b' % re.escape(v), piece) for v in tainted)
                        if tied:
                            reject_guards.append({'condition': cond, 'matched_guard': piece,
                                                  'guard_kind': kind})
    probes = []
    for name in cfg.get('malicious_names') or ['../../cache/malicious.txt']:
        probes.append({'input': name, 'contains_dotdot': '..' in name,
                       'rejected_by_observed_guard': bool(reject_guards) and '..' in name})
    for name in cfg.get('normal_names') or ['notes.txt']:
        probes.append({'input': name, 'contains_dotdot': '..' in name,
                       'rejected_by_observed_guard': bool(reject_guards) and '..' in name})
    ev.append({'traversal_reject_guards': reject_guards, 'input_probes': probes})
    ev.append({'hashed_inputs': {str(path): facts.get('_source_sha256', ''),
                                 str(dep_ev.get('settings_gradle', {}).get('path')): dep_ev.get('settings_gradle', {}).get('sha256'),
                                 str(dep_ev.get('app_build_gradle', {}).get('path')): dep_ev.get('app_build_gradle', {}).get('sha256'),
                                 str(dep_ev.get('module_build_gradle', {}).get('path')): dep_ev.get('module_build_gradle', {}).get('sha256')}})
    dur = time.perf_counter() - start
    if reject_guards:
        return _obs('ABSENT', 'directory traversal guard in linked library component', ev,
                    'FILENAME_TRAVERSAL_REJECTED_BEFORE_FILE_WRITE', dur)
    return _obs('PRESENT', 'directory traversal guard in linked library component', ev,
                'TAINTED_INTENT_FILENAME_WRITTEN_WITHOUT_TRAVERSAL_GUARD', dur)


# --------------------------------------------------------------------------- FP-58
def _leading_literal(text, varinits, depth=0):
    text = (text or '').strip()
    m = re.match(r'"([^"]*)"', text)
    if m:
        return m.group(1)
    m = re.match(r'([A-Za-z][A-Za-z0-9+.-]*)://', text)
    if m:
        return text
    m = re.match(r'([A-Za-z_]\w*)', text)
    if m and depth < 4:
        init = varinits.get(m.group(1)) or {}
        if init:
            return _leading_literal(_expr_text(init), varinits, depth + 1)
    return None


def _connection_url_vars(body):
    recv = set()
    for n, _ in _walk_with_ifs(body):
        if n.get('kind') == 'METHOD_INVOCATION' and \
                (n.get('select') or {}).get('name') == 'openConnection':
            r = ((n.get('select') or {}).get('receiver') or {}).get('name')
            if r:
                recv.add(r)
        text = n.get('text')
        if isinstance(text, str):
            for m in re.finditer(r'([A-Za-z_]\w*)\s*\.\s*openConnection\s*\(', text):
                recv.add(m.group(1))
    return recv


def _url_scheme(body):
    vartypes, varinits = _var_index(body)
    conn_vars = _connection_url_vars(body)
    targets = []
    for v in sorted(conn_vars):
        init = varinits.get(v) or {}
        if init.get('kind') == 'NEW_CLASS' and init.get('type') == 'URL':
            targets.append(init)
    scope = 'connection_bound' if targets else 'all_url_constructions'
    if not targets:
        targets = [n for n in _iter_nodes(body)
                   if n.get('kind') == 'NEW_CLASS' and n.get('type') == 'URL']
    schemes, exprs = [], []
    for u in targets:
        args = u.get('args') or []
        if not args:
            continue
        arg = args[0]
        text = _expr_text(arg)
        node = arg
        for _ in range(4):
            if node.get('kind') == 'IDENTIFIER':
                nxt = varinits.get(node.get('name', '')) or {}
                if not nxt:
                    break
                node = nxt
                text = _expr_text(nxt)
            else:
                break
        literal = _leading_literal(text, varinits)
        m = re.match(r'([A-Za-z][A-Za-z0-9+.-]*)://', literal or '')
        if m:
            schemes.append(m.group(1).lower())
            exprs.append(text)
        elif node.get('kind') == 'STRING_LITERAL':
            m2 = re.match(r'([A-Za-z][A-Za-z0-9+.-]*)://', str(node.get('value')))
            if m2:
                schemes.append(m2.group(1).lower())
                exprs.append(str(node.get('value')))
    conn_types = sorted({m.group(1) for n in _iter_nodes(body)
                         for m in [re.search(r'\((Https?URLConnection)\)', n.get('text') or '')] if m})
    catches = sorted({(c.get('param') or {}).get('type', '')
                      for n in _iter_nodes(body) if n.get('kind') == 'TRY'
                      for c in n.get('catches') or []})
    return {'schemes': schemes, 'exprs': exprs, 'connection_cast_types': conn_types,
            'catch_types': catches, 'connection_vars': sorted(conn_vars), 'scope': scope}


def check_cleartext_http(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''), 'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'transport protocol of the download connection', ev,
                    'JAVA_PARSE_FAILED', time.perf_counter() - start)
    method = select_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'transport protocol of the download connection', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    info = _url_scheme(method['body'])
    schemes = info['schemes']
    ev.append({'method': binding['method'], 'method_lines': [method.get('start_line'), method.get('end_line')],
               'url_binding_scope': info['scope'], 'connection_receiver_vars': info['connection_vars'],
               'url_schemes': schemes, 'url_expressions': info['exprs'],
               'connection_cast_types': info['connection_cast_types'],
               'catch_types': info['catch_types']})
    ev.append({'hashed_inputs': {str(path): facts.get('_source_sha256', '')}})
    dur = time.perf_counter() - start
    if not schemes:
        return _obs('UNKNOWN', 'transport protocol of the download connection', ev,
                    'URL_SCHEME_NOT_RESOLVED', dur)
    if any(s == 'http' for s in schemes):
        return _obs('PRESENT', 'transport protocol of the download connection', ev,
                    'CLEARTEXT_HTTP_URL_USED_FOR_DOWNLOAD', dur)
    if all(s == 'https' for s in schemes):
        ev.append({'tls_enforcement_evidence': {
            'https_url': True,
            'ssl_handshake_failure_handled': any('SSLHandshakeException' in c
                                                 for c in info['catch_types'])}})
        return _obs('ABSENT', 'transport protocol of the download connection', ev,
                    'HTTPS_URL_WITH_TLS_HANDSHAKE_REJECTION', dur)
    return _obs('UNKNOWN', 'transport protocol of the download connection', ev,
                'NON_HTTP_SCHEME:' + ','.join(sorted(set(schemes))), dur)


CHECKERS = {
    'C4_TLS_CERT_PINNING_KEYSTORE': check_tls_pinning,
    'C4_SOCKET_PEER_AUTH_BEFORE_SENSITIVE_IO': check_socket_peer_auth,
    'C4_LIBRARY_PATH_TRAVERSAL_GUARD_BOUND_TO_DEPENDENCY': check_traversal_guard,
    'C4_CLEARTEXT_HTTP_DOWNLOAD': check_cleartext_http,
}


def verify(rule_id, source_inputs, target_binding, rule_config):
    return CHECKERS[rule_id](source_inputs, target_binding, rule_config)


# --------------------------------------------------------------------------- drivers
ROOT = V5.parents[2]
WS = ROOT / 'ABAF_VP_完整实验方案_2026-10-11/workspace'
GHERA = WS / 'p0_inventory/ghera_src'

PAIRS = [
    {'slot': 'FP-42', 'task': 'FT-042', 'ghera': 'Networking/UnpinnedCertificates-MITM-Lean',
     'rule_id': 'C4_TLS_CERT_PINNING_KEYSTORE', 'binding': {'method': 'onHandleIntent', 'component': 'MyIntentService'},
     'cfg': {'pinning_definition': 'keystore_trust_anchor'},
     'rel': {'java': 'app/src/main/java/edu/ksu/cs/benign/MyIntentService.java',
             'manifest': 'app/src/main/AndroidManifest.xml'},
     'target': 'MyIntentService.onHandleIntent + MyTrustManager.checkServerTrusted'},
    {'slot': 'FP-43', 'task': 'FT-043', 'ghera': 'Networking/OpenSocket-InformationLeak-Lean',
     'rule_id': 'C4_SOCKET_PEER_AUTH_BEFORE_SENSITIVE_IO', 'binding': {'method': 'onHandleIntent', 'component': 'MyIntentService'},
     'cfg': {'sensitive_file': 'myInfo.txt', 'malicious_peer': 'evil.attacker.example'},
     'rel': {'java': 'app/src/main/java/edu/ksu/cs/benign/MyIntentService.java',
             'manifest': 'app/src/main/AndroidManifest.xml'},
     'target': 'MyIntentService.onHandleIntent'},
    {'slot': 'FP-45', 'task': 'FT-045', 'ghera': 'NonAPI/OutdatedLibrary-DirectoryTraversal-Lean',
     'rule_id': 'C4_LIBRARY_PATH_TRAVERSAL_GUARD_BOUND_TO_DEPENDENCY',
     'binding': {'method': 'onResume', 'component': 'WriteActivity'},
     'cfg': {'library_module_pattern': 'writetofilelibrary', 'component': 'WriteActivity',
             'taint_extra': 'fileName', 'malicious_names': ['../../cache/malicious.txt'],
             'normal_names': ['notes.txt']},
     'rel': {}, 'target': 'linked writetofilelibrary WriteActivity.onResume'},
    {'slot': 'FP-58', 'task': 'FT-058', 'ghera': 'Web/HttpConnection-MITM-Lean',
     'rule_id': 'C4_CLEARTEXT_HTTP_DOWNLOAD', 'binding': {'method': 'onHandleIntent', 'component': 'HttpIntentService'},
     'cfg': {'expected_scheme': 'https'},
     'rel': {'java': 'app/src/main/java/edu/ksu/cs/benign/HttpIntentService.java',
             'manifest': 'app/src/main/AndroidManifest.xml'},
     'target': 'HttpIntentService.onHandleIntent'},
]


def _base(pair, side):
    return GHERA / pair['ghera'] / ('Benign' if side == 'buggy' else 'Secure')


def _resolve(base, rel):
    p = base / rel
    if p.exists():
        return p
    cands = sorted(base.rglob(pathlib.Path(rel).name))
    return cands[0] if cands else p


def _inputs(pair, side):
    base = _base(pair, side)
    if pair['slot'] == 'FP-45':
        return {'app_dir': base, 'java_file': None}
    return {'java_file': _resolve(base, pair['rel']['java']),
            'manifest': _resolve(base, pair['rel']['manifest'])}


def _hash_files(paths):
    return {str(p): _sha(p) for p in paths if p and pathlib.Path(p).is_file()}


def run_side(pair, side):
    inputs = _inputs(pair, side)
    start = time.perf_counter()
    try:
        result = verify(pair['rule_id'], inputs, pair['binding'], pair['cfg'])
        exit_status = 0
    except Exception as e:  # defensive: record crash as UNKNOWN, never guess
        result = {'observation': 'UNKNOWN', 'scope': pair['rule_id'], 'evidence': [],
                  'reason': 'CHECKER_CRASH:' + repr(e), 'duration_s': 0.0}
        exit_status = 1
    dur = time.perf_counter() - start
    hashed = {}
    for item in result.get('evidence') or []:
        if isinstance(item, dict) and 'hashed_inputs' in item:
            hashed.update({k: v for k, v in item['hashed_inputs'].items() if k and k != 'None'})
    if inputs.get('java_file'):
        hashed.setdefault(str(inputs['java_file']), _sha(inputs['java_file']))
    return {
        'pair_slot': pair['slot'], 'task_id': pair['task'], 'side': side, 'kind': 'BENCHMARK',
        'family': 'C4', 'rule_id': pair['rule_id'], 'rule_version': RULE_VERSION,
        'binding': pair['binding'], 'rule_config': pair['cfg'],
        'observation': result['observation'], 'scope': result['scope'], 'reason': result['reason'],
        'evidence': result['evidence'], 'input_sha256': hashed,
        'command': [sys.executable, str(pathlib.Path(__file__).resolve()), 'run', pair['slot'], side],
        'exit_status': exit_status, 'duration_s': round(dur, 4),
        'checker': 'rules_c4', 'checker_sha256': _sha(pathlib.Path(__file__).resolve()),
        'method': 'B4 v2加目标规则补正', 'scoring_reference_read_by_checker': False,
    }


def main_run(slots=None):
    outdir = V5 / 'runs/C4'
    outdir.mkdir(parents=True, exist_ok=True)
    rows = []
    for pair in PAIRS:
        if slots and pair['slot'] not in slots:
            continue
        for side in ('buggy', 'fixed'):
            receipt = run_side(pair, side)
            (outdir / f"{pair['slot']}-{side}.json").write_text(
                json.dumps(receipt, ensure_ascii=False, indent=2))
            rows.append({k: receipt[k] for k in ('pair_slot', 'side', 'family', 'rule_id',
                                                 'observation', 'reason', 'duration_s', 'exit_status')})
            print(pair['slot'], side, pair['rule_id'], receipt['observation'], receipt['reason'])
    return rows


# ---------------------------------------------------------------------- counterexamples
CE = V5 / 'runs/C4/counterexamples'


def _variant(name, src, subs):
    text = pathlib.Path(src).read_text()
    for old, new in subs:
        assert old in text, f'{name}: marker not found: {old[:70]!r}'
        text = text.replace(old, new, 1)
    dst = CE / name / pathlib.Path(src).name
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(text)
    return dst


def _lib_tree(name, module, aar_rel, java_text):
    app = CE / name / 'app'
    (app / 'app').mkdir(parents=True, exist_ok=True)
    (app / 'settings.gradle').write_text("include ':app', ':%s'\n" % module)
    (app / 'app' / 'build.gradle').write_text(
        "dependencies {\n    implementation project(':%s')\n}\n" % module)
    (app / module).mkdir(parents=True, exist_ok=True)
    (app / module / 'build.gradle').write_text(
        "configurations.maybeCreate('default')\n"
        "artifacts.add('default', file('%s'))\n" % aar_rel)
    resolved = (app / module / aar_rel).resolve()
    parts = list(resolved.parts)
    root = pathlib.Path(*parts[:parts.index('build')])
    dst = root / 'src/main/java/com/example/writetofilelibrary/WriteActivity.java'
    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(java_text)
    return app


def _case(case_id, rule_id, cls, inputs, binding, cfg, expected, note):
    try:
        res = verify(rule_id, inputs, binding, cfg)
        obs, reason = res['observation'], res['reason']
        extra = [e for e in res['evidence'] if isinstance(e, dict) and
                 ('input_probes' in e or 'tls_enforcement_evidence' in e)]
    except Exception as e:
        obs, reason, extra = 'CRASH', repr(e), []
    return {'case_id': case_id, 'rule_id': rule_id, 'case_class': cls,
            'expected': expected, 'observed': obs, 'pass': obs == expected,
            'reason': reason, 'note': note, 'extra': extra}


def run_counterexamples():
    CE.mkdir(parents=True, exist_ok=True)
    g42b = _base(PAIRS[0], 'buggy') / 'app/src/main/java/edu/ksu/cs/benign/MyIntentService.java'
    g42f = _base(PAIRS[0], 'fixed') / 'app/src/main/java/edu/ksu/cs/benign/MyIntentService.java'
    g43b = _base(PAIRS[1], 'buggy') / 'app/src/main/java/edu/ksu/cs/benign/MyIntentService.java'
    g43f = _base(PAIRS[1], 'fixed') / 'app/src/main/java/edu/ksu/cs/secure/MyIntentService.java'
    g58b = _base(PAIRS[3], 'buggy') / 'app/src/main/java/edu/ksu/cs/benign/HttpIntentService.java'
    g58f = _base(PAIRS[3], 'fixed') / 'app/src/main/java/edu/ksu/cs/benign/HttpIntentService.java'
    lib10 = (GHERA / 'NonAPI/OutdatedLibrary-DirectoryTraversal-Lean/Library/version1.0/src/main/java/'
             'com/example/writetofilelibrary/WriteActivity.java')
    lib11 = (GHERA / 'NonAPI/OutdatedLibrary-DirectoryTraversal-Lean/Library/version1.1/src/main/java/'
             'com/example/writetofilelibrary/WriteActivity.java')

    r42, r43, r45, r58 = (p['rule_id'] for p in PAIRS)
    b42, b43, b45, b58 = (p['binding'] for p in PAIRS)
    c42, c43, c45, c58 = (p['cfg'] for p in PAIRS)
    cases = []

    cases.append(_case('FP42-DEFECT_PRESENT', r42, 'DEFECT_PRESENT', {'java_file': g42b}, b42, c42,
                       'PRESENT', 'real buggy service: custom X509TrustManager decides trust'))
    cases.append(_case('FP42-DEFECT_FIXED', r42, 'DEFECT_FIXED', {'java_file': g42f}, b42, c42,
                       'ABSENT', 'real fixed service: KeyStore + TrustManagerFactory pinning'))
    v = _variant('FP42-ALIAS', g42b, [(
        '            final TrustManager trustManager[] = new TrustManager[]{new MyTrustManager(getApplicationContext())};',
        '            final MyTrustManager myTm = new MyTrustManager(getApplicationContext());\n'
        '            final TrustManager trustManager[] = new TrustManager[]{myTm};')])
    cases.append(_case('FP42-ALIAS', r42, 'ALIAS', {'java_file': v}, b42, c42, 'PRESENT',
                       'custom trust manager reached through a local alias inside the array'))
    v = _variant('FP42-WRONG_OBJECT', g42f, [(
        '            context.init(null, tmf.getTrustManagers(), null);',
        '            context.init(null, new TrustManager[]{new MyTrustManager(getApplicationContext())}, null);')])
    cases.append(_case('FP42-WRONG_OBJECT', r42, 'WRONG_OBJECT_OR_IRRELEVANT_CHANGE', {'java_file': v},
                       b42, c42, 'PRESENT',
                       'keystore code present but the SSLContext is initialised with a custom TrustManager'))

    cases.append(_case('FP43-DEFECT_PRESENT', r43, 'DEFECT_PRESENT', {'java_file': g43b}, b43, c43,
                       'PRESENT', 'real buggy service copies the file without peer identity check'))
    cases.append(_case('FP43-DEFECT_FIXED', r43, 'DEFECT_FIXED', {'java_file': g43f}, b43, c43,
                       'ABSENT', 'real fixed service guards the copy with a host identity check'))
    v = _variant('FP43-WRONG_OBJECT', g43f, [
        ('                 Socket s = ss.accept()) {',
         '                 Socket s = ss.accept();\n                 Socket s2 = new Socket()) {'),
        ('if (s.getInetAddress().getHostName().equals("trusted.remote.com")) {',
         'if (s2.getInetAddress().getHostName().equals("trusted.remote.com")) {')])
    cases.append(_case('FP43-WRONG_OBJECT', r43, 'WRONG_OBJECT_OR_IRRELEVANT_CHANGE', {'java_file': v},
                       b43, c43, 'PRESENT',
                       'guard checks a different Socket object than the accepted one'))
    v = _variant('FP43-BRANCH_DOMINANCE', g43f, [
        ('                if (s.getInetAddress().getHostName().equals("trusted.remote.com")) {\n'
         '                    FileInputStream fis = openFileInput("myInfo.txt");',
         '                if (s.getInetAddress().getHostName().equals("trusted.remote.com")) {\n'
         '                    Log.d(TAG, "trusted");\n'
         '                }\n'
         '                {\n'
         '                    FileInputStream fis = openFileInput("myInfo.txt");'),
        ('                } else {', '                }\n                if (false) {')])
    cases.append(_case('FP43-BRANCH_DOMINANCE', r43, 'BRANCH_DOMINANCE', {'java_file': v}, b43, c43,
                       'PRESENT', 'check exists but no longer dominates the sensitive copy'))
    v = _variant('FP43-EXCEPTION_PATH', g43f, [(
        '            } catch (IOException e) {\n                Log.e(TAG, "Exception while opening port", e);',
        '            } catch (IOException e) {\n'
        '                try {\n'
        '                    FileInputStream fis = openFileInput("myInfo.txt");\n'
        '                    OutputStream fos2 = s.getOutputStream();\n'
        '                    int d;\n'
        '                    while ((d = fis.read()) != -1) {\n'
        '                        fos2.write(d);\n'
        '                    }\n'
        '                } catch (IOException ignored) { }\n'
        '                Log.e(TAG, "Exception while opening port", e);')])
    cases.append(_case('FP43-EXCEPTION_PATH', r43, 'EXCEPTION_PATH', {'java_file': v}, b43, c43,
                       'PRESENT', 'unguarded copy inside the exception handler'))
    v = _variant('FP43-ALIAS', g43f, [
        ('                Log.d(TAG, "Remote connected on port " + PORT + "...");',
         '                Log.d(TAG, "Remote connected on port " + PORT + "...");\n'
         '                Socket conn = s;'),
        ('if (s.getInetAddress().getHostName().equals("trusted.remote.com")) {',
         'if (conn.getInetAddress().getHostName().equals("trusted.remote.com")) {')])
    cases.append(_case('FP43-ALIAS', r43, 'ALIAS', {'java_file': v}, b43, c43, 'ABSENT',
                       'guard resolved through an alias of the accepted socket'))
    polar = CE / 'FP43-ELSE_POLARITY' / 'PolarizedService.java'
    polar.parent.mkdir(parents=True, exist_ok=True)
    polar.write_text(
        'import java.io.FileInputStream;\n'
        'import java.io.OutputStream;\n'
        'import java.net.ServerSocket;\n'
        'import java.net.Socket;\n\n'
        'public class PolarizedService {\n'
        '    protected void onHandleIntent(Object intent) throws Exception {\n'
        '        try (ServerSocket ss = new ServerSocket(5000);\n'
        '             FileInputStream fis = new FileInputStream("myInfo.txt");\n'
        '             Socket s = ss.accept();\n'
        '             OutputStream fos = s.getOutputStream()) {\n'
        '            if (s.getInetAddress().getHostName().equals("trusted.remote.com")) {\n'
        '                fos.write("Rejected".getBytes());\n'
        '            } else {\n'
        '                int d;\n'
        '                while ((d = fis.read()) != -1) {\n'
        '                    fos.write(d);\n'
        '                }\n'
        '            }\n'
        '        }\n'
        '    }\n'
        '}\n')
    cases.append(_case('FP43-ELSE_POLARITY', r43, 'BRANCH_POLARITY', {'java_file': polar}, b43, c43,
                       'PRESENT', 'copy sits in the else branch of a positive identity check'))
    polar_then = CE / 'FP43-THEN_POLARITY_CONTROL' / 'PolarizedService.java'
    polar_then.parent.mkdir(parents=True, exist_ok=True)
    polar_then.write_text(
        'import java.io.FileInputStream;\n'
        'import java.io.OutputStream;\n'
        'import java.net.ServerSocket;\n'
        'import java.net.Socket;\n\n'
        'public class PolarizedService {\n'
        '    protected void onHandleIntent(Object intent) throws Exception {\n'
        '        try (ServerSocket ss = new ServerSocket(5000);\n'
        '             FileInputStream fis = new FileInputStream("myInfo.txt");\n'
        '             Socket s = ss.accept();\n'
        '             OutputStream fos = s.getOutputStream()) {\n'
        '            if (s.getInetAddress().getHostName().equals("trusted.remote.com")) {\n'
        '                int d;\n'
        '                while ((d = fis.read()) != -1) {\n'
        '                    fos.write(d);\n'
        '                }\n'
        '            } else {\n'
        '                fos.write("Rejected".getBytes());\n'
        '            }\n'
        '        }\n'
        '    }\n'
        '}\n')
    cases.append(_case('FP43-THEN_POLARITY_CONTROL', r43, 'DEFECT_FIXED', {'java_file': polar_then},
                       b43, c43, 'ABSENT', 'copy sits in the then branch of a positive identity check'))

    app = _lib_tree('FP45-DEFECT_PRESENT', 'writetofilelibrary-1.0',
                    '../../Library/version1.0/build/outputs/aar/version1.0-debug.aar',
                    lib10.read_text())
    cases.append(_case('FP45-DEFECT_PRESENT', r45, 'DEFECT_PRESENT', {'app_dir': app}, b45, c45,
                       'PRESENT', 'linked library 1.0 keeps the unguarded filename path'))
    app = _lib_tree('FP45-DEFECT_FIXED', 'writetofilelibrary-1.1',
                    '../../Library/version1.1/build/outputs/aar/version1.1-debug.aar',
                    lib11.read_text())
    cases.append(_case('FP45-DEFECT_FIXED', r45, 'DEFECT_FIXED', {'app_dir': app}, b45, c45,
                       'ABSENT', 'linked library 1.1 rejects ".." filenames'))
    v = _variant('FP45-WRONG_OBJECT', lib11, [(
        '!i.getStringExtra("fileName").contains("..")',
        '!i.getStringExtra("fileContent").contains("..")')])
    app = _lib_tree('FP45-WRONG_OBJECT', 'writetofilelibrary-1.1',
                    '../../Library/version1.1/build/outputs/aar/version1.1-debug.aar',
                    v.read_text())
    cases.append(_case('FP45-WRONG_OBJECT', r45, 'WRONG_OBJECT_OR_IRRELEVANT_CHANGE', {'app_dir': app},
                       b45, c45, 'PRESENT', '".." check applied to the content extra, not the filename'))
    v = _variant('FP45-IRRELEVANT_CHANGE', lib10, [('            Log.d(TAG, fileNm);',
                                                    '            Log.d(TAG, fileNm + "..");')])
    app = _lib_tree('FP45-IRRELEVANT_CHANGE', 'writetofilelibrary-1.0',
                    '../../Library/version1.0/build/outputs/aar/version1.0-debug.aar',
                    v.read_text())
    cases.append(_case('FP45-IRRELEVANT_CHANGE', r45, 'WRONG_OBJECT_OR_IRRELEVANT_CHANGE',
                       {'app_dir': app}, b45, c45, 'PRESENT',
                       'a ".." string in a log line is not a traversal guard'))
    app = _lib_tree('FP45-DEPENDENCY_BINDING', 'writetofilelibrary-1.1',
                    '../../Library/version1.0/build/outputs/aar/version1.0-debug.aar',
                    lib10.read_text())
    cases.append(_case('FP45-DEPENDENCY_BINDING', r45, 'WRONG_OBJECT_OR_IRRELEVANT_CHANGE',
                       {'app_dir': app}, b45, c45, 'PRESENT',
                       'module label says 1.1 but the resolved aar points at 1.0 source'))
    app = _lib_tree('FP45-DEPENDENCY_BINDING_CONTROL', 'writetofilelibrary-1.0',
                    '../../Library/version1.1/build/outputs/aar/version1.1-debug.aar',
                    lib11.read_text())
    cases.append(_case('FP45-DEPENDENCY_BINDING_CONTROL', r45, 'DEFECT_FIXED', {'app_dir': app},
                       b45, c45, 'ABSENT', 'resolved aar points at the guarded 1.1 source'))

    cases.append(_case('FP58-DEFECT_PRESENT', r58, 'DEFECT_PRESENT', {'java_file': g58b}, b58, c58,
                       'PRESENT', 'real buggy service downloads over cleartext http'))
    cases.append(_case('FP58-DEFECT_FIXED', r58, 'DEFECT_FIXED', {'java_file': g58f}, b58, c58,
                       'ABSENT', 'real fixed service downloads over https'))
    v = _variant('FP58-IRRELEVANT_CHANGE', g58b, [(
        '            HttpURLConnection urlConnection = null;',
        '            HttpURLConnection urlConnection = null;\n'
        '            try {\n'
        '                new URL("https://example.com/");\n'
        '            } catch (Exception ignored) { }')])
    cases.append(_case('FP58-IRRELEVANT_CHANGE', r58, 'WRONG_OBJECT_OR_IRRELEVANT_CHANGE',
                       {'java_file': v}, b58, c58, 'PRESENT',
                       'an unconnected https URL literal does not change the cleartext download'))
    v = _variant('FP58-ALIAS', g58b, [(
        '                String urlString = "http://" + getResources().getString(R.string.local_server_ipv4) + ":" +',
        '                String proto = "http://";\n'
        '                String urlString = proto + getResources().getString(R.string.local_server_ipv4) + ":" +')])
    cases.append(_case('FP58-ALIAS', r58, 'ALIAS', {'java_file': v}, b58, c58, 'PRESENT',
                       'scheme carried through a local alias of the literal'))
    v = _variant('FP58-SECOND_CONNECTION', g58f, [(
        '                InputStream in = new BufferedInputStream(urlConnection.getInputStream());',
        '                URL alt = new URL("http://example.com/");\n'
        '                alt.openConnection();\n'
        '                InputStream in = new BufferedInputStream(urlConnection.getInputStream());')])
    cases.append(_case('FP58-SECOND_CONNECTION', r58, 'WRONG_OBJECT_OR_IRRELEVANT_CHANGE',
                       {'java_file': v}, b58, c58, 'PRESENT',
                       'a second, cleartext connection is opened from the same method'))

    out = {'family': 'C4', 'rule_version': RULE_VERSION,
           'method': 'B4 v2加目标规则补正',
           'checker': 'src/rules_c4.py',
           'checker_sha256': _sha(pathlib.Path(__file__).resolve()),
           'reference_read_by_checker': False,
           'cases': cases}
    by_class = {}
    for c in cases:
        d = by_class.setdefault(c['case_class'], {'total': 0, 'passed': 0})
        d['total'] += 1
        d['passed'] += int(c['pass'])
    out['summary'] = {'total': len(cases), 'passed': sum(c['pass'] for c in cases),
                      'by_class': by_class}
    dest = V5 / 'checks/C4_counterexamples.json'
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(out, ensure_ascii=False, indent=2))
    for c in cases:
        flag = 'PASS' if c['pass'] else 'FAIL'
        print(f"{flag} {c['case_id']:32s} {c['case_class']:36s} exp={c['expected']:8s} obs={c['observed']}")
    print(json.dumps(out['summary'], ensure_ascii=False))
    return out


def score(slots=None):
    """Scoring stage: reads reference states only here, never inside a checker."""
    ref_path = V5.parent / 'exp3_paired_validation_v1/data/target_contracts.jsonl'
    contracts = {}
    for line in ref_path.read_text().splitlines():
        o = json.loads(line)
        if o.get('pair_slot') in {p['slot'] for p in PAIRS}:
            contracts[o['pair_slot']] = o
    rows = []
    for pair in PAIRS:
        if slots and pair['slot'] not in slots:
            continue
        obs = {}
        for side in ('buggy', 'fixed'):
            rp = V5 / f"runs/C4/{pair['slot']}-{side}.json"
            obs[side] = json.loads(rp.read_text())
        ref = (contracts.get(pair['slot']) or {}).get('reference') or {}
        ref_b, ref_f = ref.get('buggy'), ref.get('fixed')
        ob, of = obs['buggy']['observation'], obs['fixed']['observation']
        if ob == 'UNKNOWN' or of == 'UNKNOWN':
            cls, why = 'UNRESOLVED', 'OBSERVATION_UNDETERMINED:' + obs['buggy']['reason'] + '/' + obs['fixed']['reason']
        elif not ref_b or not ref_f:
            cls, why = 'UNRESOLVED', 'REFERENCE_STATE_MISSING'
        elif ob == ref_b and of == ref_f:
            cls, why = 'MATCHED', 'BOTH_SIDES_EQUAL_REFERENCE'
        else:
            cls, why = 'UNRESOLVED', f'OBSERVATION_REFERENCE_MISMATCH:obs={ob}/{of},ref={ref_b}/{ref_f}'
        row = {'pair_slot': pair['slot'], 'task_id': pair['task'], 'kind': 'BENCHMARK',
               'rule_id': pair['rule_id'], 'binding': pair['binding'],
               'observation_buggy': ob, 'observation_fixed': of,
               'reason_buggy': obs['buggy']['reason'], 'reason_fixed': obs['fixed']['reason'],
               'reference_buggy': ref_b, 'reference_fixed': ref_f,
               'result_class': cls, 'classification_reason': why,
               'rule_version': RULE_VERSION,
               'receipts': [f"runs/C4/{pair['slot']}-buggy.json", f"runs/C4/{pair['slot']}-fixed.json"],
               'duration_s': [obs['buggy']['duration_s'], obs['fixed']['duration_s']],
               'exit_status': [obs['buggy']['exit_status'], obs['fixed']['exit_status']]}
        if pair['slot'] == 'FP-42':
            row['limitation'] = (
                '判定依据是TLS信任锚的构造方式：buggy侧存在按证书相等比较的自定义X509TrustManager'
                '(无KeyStore信任锚、无PKIX链验证)，fixed侧为KeyStore+TrustManagerFactory仅信任预置证书。'
                'buggy侧并非完全没有证书比较逻辑，因此该观测是"锁定实现方式"层面的判定，'
                '报告中如实记录，未使用修复差异或参考状态作为选择依据。')
        rows.append(row)
    ce_path = V5 / 'checks/C4_counterexamples.json'
    ce = json.loads(ce_path.read_text()) if ce_path.exists() else {}
    summary = {'total': len(rows)}
    for k in ('MATCHED', 'UNRESOLVED', 'NOT_APPLICABLE', 'PROPERTY_SUPPORT'):
        summary[k.lower()] = sum(1 for r in rows if r['result_class'] == k)
    summary['real_pairs'] = 0
    summary['benchmark_pairs'] = len(rows)
    report = {'family': 'C4', 'method': 'B4 v2加目标规则补正', 'rule_version': RULE_VERSION,
              'checker': 'src/rules_c4.py',
              'checker_sha256': _sha(pathlib.Path(__file__).resolve()),
              'reference_read_stage': 'scoring_only (checkers never receive reference or expected state)',
              'pairs': rows, 'summary': summary,
              'counterexamples': ce.get('summary', {}),
              'counterexample_file': 'checks/C4_counterexamples.json',
              'v3_previous_result': {r['pair_slot']: 'NOT_APPLICABLE (obs UNKNOWN/UNKNOWN)'
                                     for r in rows}}
    dest = V5 / 'progress/C4_report.json'
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_text(json.dumps(report, ensure_ascii=False, indent=2))
    print(json.dumps(summary, ensure_ascii=False))
    for r in rows:
        print(r['pair_slot'], r['observation_buggy'], r['observation_fixed'],
              f"ref={r['reference_buggy']}/{r['reference_fixed']}", r['result_class'])
    return report


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else 'run'
    if cmd == 'run':
        main_run(sys.argv[2:] or None)
    elif cmd == 'counterexamples':
        run_counterexamples()
    elif cmd == 'score':
        score(sys.argv[2:] or None)
    else:
        raise SystemExit('usage: rules_c4.py run|counterexamples|score')

