"""A1 manifest/build-config rule family. Unified, parameterized implementations.

verify(source_inputs, target_binding, rule_config) -> observation dict (see plan §4.2).
XML is parsed with ElementTree; build-script sourceSets are parsed with regex only to
locate the manifest override declaration, then resolved against the module tree.
"""
import pathlib
import xml.etree.ElementTree as ET

ANDROID = '{http://schemas.android.com/apk/res/android}'


def _obs(observation, scope, evidence, reason, duration_s=0.0):
    return {'observation': observation, 'scope': scope, 'evidence': evidence,
            'reason': reason, 'duration_s': duration_s}


def parse_manifest(path):
    try:
        return ET.parse(path).getroot()
    except Exception:
        return None


def _app(root):
    return root.find('application') if root is not None and root.tag == 'manifest' else None


def check_metrics_optout(inputs, binding, cfg):
    path = inputs['manifest']
    root = parse_manifest(path)
    app = _app(root)
    ev = [{'path': str(path), 'sha256': inputs.get('manifest_sha256', '')}]
    if app is None:
        return _obs('UNKNOWN', 'manifest application meta-data', ev, 'MANIFEST_UNPARSEABLE_OR_NO_APPLICATION')
    for md in app.findall('meta-data'):
        if md.get(ANDROID + 'name') == cfg['metadata_name']:
            val = md.get(ANDROID + 'value')
            if (val or '').lower() == 'true':
                return _obs('ABSENT', 'WebView metrics opt-out declaration', ev,
                            'METADATA_OPTOUT_TRUE_DECLARED')
            return _obs('PRESENT', 'WebView metrics opt-out declaration', ev,
                        'METADATA_PRESENT_BUT_NOT_TRUE')
    return _obs('PRESENT', 'WebView metrics opt-out declaration', ev,
                'METADATA_OPTOUT_MISSING')


def effective_manifest_path(module_dir, build_files):
    """Resolve the manifest path the build system will merge.

    Parse sourceSets manifest overrides from groovy/kotlin build scripts; fall back to
    src/main/AndroidManifest.xml when no override exists. Returns (path, evidence_list).
    """
    module_dir = pathlib.Path(module_dir)
    ev = []
    for bf in build_files:
        p = pathlib.Path(bf)
        if not p.exists():
            continue
        src = p.read_text()
        ev.append({'path': str(p), 'sha256': '', 'role': 'build_script_parsed'})
        # match e.g. sourceSets { main { manifest.srcFile '...' } } or manifest.srcFile("...")
        import re
        for m in re.finditer(r'manifest\.srcFile\s*(?:\(|\s)\s*["\']([^"\']+)["\']', src):
            rel = m.group(1)
            cand = (module_dir / rel).resolve()
            ev[-1]['matched'] = rel
            return pathlib.Path(cand), ev
    return module_dir / 'src/main/AndroidManifest.xml', ev


def check_sourceset_manifest(inputs, binding, cfg):
    module = pathlib.Path(inputs['module_dir'])
    build_files = inputs.get('build_files') or []
    eff, ev = effective_manifest_path(module, build_files)
    eff_exists = eff.exists()
    stray = [pathlib.Path(p) for p in inputs.get('stray_manifests', []) if pathlib.Path(p).exists()]
    stray = [s for s in stray if s.resolve() != eff.resolve()]
    ev = ev + [{'path': str(s), 'role': 'stray_manifest_outside_effective_path'} for s in stray]
    ev.append({'path': str(eff), 'role': 'effective_sourceSet_manifest', 'exists': eff_exists})
    if eff_exists and not stray:
        return _obs('ABSENT', 'module manifest participates in build via sourceSet', ev,
                    'MANIFEST_AT_EFFECTIVE_SOURCESET_PATH')
    if stray and not eff_exists:
        return _obs('PRESENT', 'module manifest participates in build via sourceSet', ev,
                    'SECURITY_MANIFEST_OUTSIDE_EFFECTIVE_SOURCESET_PATH')
    if stray and eff_exists:
        return _obs('UNKNOWN', 'module manifest participates in build via sourceSet', ev,
                    'MANIFEST_IN_BOTH_PATHS')
    return _obs('UNKNOWN', 'module manifest participates in build via sourceSet', ev,
                'NO_MANIFEST_FOUND')


def check_queries_service(inputs, binding, cfg):
    path = inputs['manifest']
    root = parse_manifest(path)
    ev = [{'path': str(path)}]
    if root is None:
        return _obs('UNKNOWN', 'manifest queries declaration', ev, 'MANIFEST_UNPARSEABLE')
    action = cfg['service_action']
    for q in root.findall('queries'):
        for intent in q.findall('intent'):
            for act in intent.findall('action'):
                if act.get(ANDROID + 'name') == action:
                    return _obs('ABSENT', 'package-visibility queries declaration', ev,
                                'QUERIES_INTENT_ACTION_DECLARED')
    return _obs('PRESENT', 'package-visibility queries declaration', ev,
                'QUERIES_INTENT_ACTION_MISSING')


def check_task_affinity(inputs, binding, cfg):
    path = inputs['manifest']
    root = parse_manifest(path)
    app = _app(root)
    ev = [{'path': str(path)}]
    if app is None:
        return _obs('UNKNOWN', 'application taskAffinity', ev, 'MANIFEST_UNPARSEABLE_OR_NO_APPLICATION')
    ta = app.get(ANDROID + 'taskAffinity')
    if ta is None:
        return _obs('PRESENT', 'application taskAffinity', ev, 'TASK_AFFINITY_NOT_DECLARED_DEFAULTS_TO_PACKAGE')
    if ta == '':
        return _obs('ABSENT', 'application taskAffinity', ev, 'TASK_AFFINITY_EMPTY_BREAKS_AFFINITY')
    return _obs('PRESENT', 'application taskAffinity', ev,
                'TASK_AFFINITY_NON_EMPTY')


def check_over_permission(inputs, binding, cfg):
    """Over-declared permission: declared in the module manifest but unused by the
    module's own source code (AST usage-signature scan, same logic both sides)."""
    import time
    from javaparse import facts_for
    from rules_webview import _iter_nodes
    start = time.perf_counter()
    path = inputs['manifest']
    root = parse_manifest(path)
    ev = [{'path': str(path)}]
    if root is None:
        return _obs('UNKNOWN', 'permission declaration vs module usage', ev, 'MANIFEST_UNPARSEABLE')
    perm = cfg['permission']
    declared = any(up.get(ANDROID + 'name') == perm for up in root.findall('uses-permission'))
    if not declared:
        return _obs('ABSENT', 'permission declaration vs module usage', ev,
                    'PERMISSION_NOT_DECLARED')
    # usage scan over the manifest-owning module's own source
    usages = []
    src_root = pathlib.Path(inputs['module_source_root'])
    files = [p for p in src_root.rglob('*') if p.suffix in ('.java', '.kt')]
    sigs = cfg['usage_signatures']  # [{'type': 'PowerManager.WakeLock', 'methods': ['acquire']}, ...]
    for f in files:
        if f.suffix != '.java':
            # kotlin fallback: locate-only text scan marks unresolved rather than proof
            text = f.read_text()
            if any(s['type'] in text for s in sigs):
                usages.append({'path': str(f), 'via': 'kt_locate_only'})
            continue
        facts = facts_for(f)
        if not facts.get('parse_ok'):
            return _obs('UNKNOWN', 'permission declaration vs module usage', ev,
                        'MODULE_SOURCE_UNPARSEABLE:' + f.name)
        for m in facts['methods']:
            vartypes = {}
            for st in _iter_nodes(m['body']):
                if st.get('kind') == 'VARIABLE':
                    vartypes[st.get('name','')] = st.get('type', '')
            for call in _invocations(m['body']):
                sel = call.get('select', {})
                name = sel.get('name') or ''
                recv = sel.get('receiver') or {}
                recv_name = recv.get('name') or ''
                recv_text = recv.get('text') or recv_name
                for s in sigs:
                    if name not in s['methods']:
                        continue
                    declared = vartypes.get(recv_name, '')
                    if s['type'] in declared or s['type'].split('.')[-1] in recv_text:
                        usages.append({'path': str(f), 'method': m['name'], 'call': name,
                                       'receiver_type': declared})
    if usages:
        ev.append({'module_usage': usages})
        return _obs('ABSENT', 'permission declaration vs module usage', ev,
                    'PERMISSION_DECLARED_AND_USED_BY_MODULE')
    return _obs('PRESENT', 'permission declaration vs module usage', ev,
                'PERMISSION_DECLARED_BUT_UNUSED_BY_MODULE_CODE')


def _invocations(node, out=None):
    """Yield every METHOD_INVOCATION dict in an AST expression tree."""
    if out is None:
        out = []
    if isinstance(node, dict):
        if node.get('kind') == 'METHOD_INVOCATION':
            out.append(node)
        for v in node.values():
            _invocations(v, out)
    elif isinstance(node, list):
        for v in node:
            _invocations(v, out)
    return out


CHECKERS = {
    'MANIFEST_WEBVIEW_METRICS_OPTOUT': check_metrics_optout,
    'MANIFEST_SOURCESET_EFFECTIVE_PATH': check_sourceset_manifest,
    'MANIFEST_QUERIES_SERVICE_DISCOVERY': check_queries_service,
    'MANIFEST_TASK_AFFINITY_EMPTY': check_task_affinity,
    'MANIFEST_OVER_PERMISSION_UNUSED': check_over_permission,
}


def verify(rule_id, source_inputs, target_binding, rule_config):
    fn = CHECKERS[rule_id]
    return fn(source_inputs, target_binding, rule_config)
