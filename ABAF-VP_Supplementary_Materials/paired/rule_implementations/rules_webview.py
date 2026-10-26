"""A3 WebView rule family. Bind every Settings setter to the SAME WebView object that
loads content; evaluate concrete setter boolean literals from the JDK AST.

verify(rule_id, source_inputs, target_binding, rule_config) -> observation dict.
"""
import time
from javaparse import facts_for, select_method


def _obs(observation, scope, evidence, reason, duration_s=0.0):
    return {'observation': observation, 'scope': scope, 'evidence': evidence,
            'reason': reason, 'duration_s': duration_s}


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


def _literal_bool(arg):
    if isinstance(arg, dict) and arg.get('kind', '').endswith('LITERAL'):
        v = str(arg.get('value'))
        if v in ('true', 'false'):
            return v == 'true'
    return None


class WebViewScope:
    """Object binding within one method: WebView locals, their Settings handles, and
    every setter/load call resolved against the owning WebView."""

    def __init__(self, method):
        self.method = method
        self.webviews = {}      # var name -> True (declared type WebView)
        self.settings_vars = {} # var name -> webview var name (from v.getSettings())
        self.setters = []       # (webview_key, setting, bool_value, order)
        self.loads = []         # (webview_key, load_kind, arg0_value)
        self.cookie_calls = []  # (setting, bool_value) for CookieManager.getInstance()
        self._scan()

    def _scan(self):
        order = 0
        for st in _iter_nodes(self.method['body']):
            if st.get('kind') == 'VARIABLE':
                name, typ = st.get('name',''), st.get('type', '')
                init = st.get('init') or {}
                if typ.endswith('WebView'):
                    self.webviews[name] = True
                if 'WebSettings' in typ:
                    owner = self._settings_owner(init)
                    if owner:
                        self.settings_vars[name] = owner
                continue
            if st.get('kind') != 'METHOD_INVOCATION':
                continue
            call = st
            order += 1
            sel = call.get('select', {})
            name = sel.get('name') or ''
            receiver = sel.get('receiver') or {}
            args = call.get('args') or []
            if name == 'getSettings':
                continue
            if receiver.get('kind') == 'MEMBER_SELECT':
                base = receiver.get('receiver') or {}
                if base.get('kind') == 'METHOD_INVOCATION' and (base.get('select') or {}).get('name') == 'getSettings':
                    wv = (base.get('select') or {}).get('receiver', {}).get('name')
                    if name.startswith('set') and args:
                        self.setters.append((wv, name, _literal_bool(args[0]), order))
                    continue
                if (base.get('select') or {}).get('name') == 'getInstance' and name == 'setAcceptCookie' and args:
                    self.cookie_calls.append((_literal_bool(args[0]), order))
                    continue
            recv_name = receiver.get('name')
            if recv_name in self.settings_vars and name.startswith('set') and args:
                self.setters.append((self.settings_vars[recv_name], name,
                                     _literal_bool(args[0]), order))
            elif recv_name in self.webviews and name.startswith('load'):
                arg0 = args[0] if args else {}
                val = arg0.get('value') if arg0.get('kind', '').endswith('LITERAL') else None
                self.loads.append((recv_name, name, val))
            elif recv_name in self.webviews and name == 'setWebViewClient':
                pass
            # CookieManager.getInstance().setX(...) reached via receiver METHOD_INVOCATION
            if name == 'setAcceptCookie' and args:
                self.cookie_calls.append((_literal_bool(args[0]), order))

    def _settings_owner(self, init):
        if init.get('kind') != 'METHOD_INVOCATION':
            return None
        sel = init.get('select') or {}
        if sel.get('name') != 'getSettings':
            return None
        recv = sel.get('receiver') or {}
        return recv.get('name')


def _final_value(scope, webview_keys, setting):
    vals = [v for (wv, s, v, o) in scope.setters if s == setting and wv in webview_keys]
    vals = [v for v in vals if v is not None]
    if not vals:
        return None
    if len(set(vals)) > 1:
        return 'CONFLICT'
    return vals[-1]


def _run(rule_id, inputs, binding, cfg):
    start = time.perf_counter()
    facts = facts_for(inputs['java_file'])
    ev = [{'path': str(inputs['java_file']), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', rule_id, ev, 'JAVA_PARSE_FAILED', time.perf_counter() - start)
    method = select_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', rule_id, ev, 'TARGET_METHOD_NOT_UNIQUE_OR_MISSING',
                    time.perf_counter() - start)
    scope = WebViewScope(method)
    ev.append({'method': binding['method'], 'start_line': method.get('start_line'),
               'webviews': sorted(scope.webviews),
               'settings_bindings': scope.settings_vars,
               'setters': [{'webview': w, 'setter': s, 'value': v} for w, s, v, o in scope.setters],
               'loads': scope.loads, 'cookie_calls': scope.cookie_calls})
    dur = time.perf_counter() - start
    if not scope.webviews:
        return _obs('UNKNOWN', rule_id, ev, 'NO_WEBVIEW_OBJECT_IN_METHOD', dur)
    if rule_id == 'WEBVIEW_COOKIE_ACCEPTANCE_DISABLED':
        if not any(l[1] in ('loadUrl', 'loadData', 'loadDataWithBaseURL') for l in scope.loads):
            return _obs('UNKNOWN', rule_id, ev, 'NO_CONTENT_LOAD_IN_METHOD', dur)
        vals = [v for v, o in scope.cookie_calls if v is not None]
        if vals and not any(vals):
            return _obs('ABSENT', 'CookieManager cookie acceptance policy', ev,
                        'COOKIE_ACCEPTANCE_DISABLED_BEFORE_LOAD', dur)
        if any(vals) and all(vals):
            return _obs('PRESENT', 'CookieManager cookie acceptance policy', ev,
                        'COOKIE_ACCEPTANCE_EXPLICITLY_ENABLED', dur)
        return _obs('PRESENT', 'CookieManager cookie acceptance policy', ev,
                    'COOKIE_ACCEPTANCE_NOT_DISABLED_DEFAULT_ACCEPTS', dur)
    # rules bound to the same WebView object that loads content
    loaders = sorted({wv for wv, kind, _ in scope.loads
                      if kind in ('loadUrl', 'loadData', 'loadDataWithBaseURL')})
    if not loaders:
        return _obs('UNKNOWN', rule_id, ev, 'NO_CONTENT_LOAD_IN_METHOD', dur)
    keys = set(loaders)
    per_loader = {wv: _final_value(scope, {wv}, 'setAllowFileAccessFromFileURLs') for wv in loaders}
    if rule_id == 'WEBVIEW_ALLOW_FILE_ACCESS_FROM_FILE_URLS':
        v = per_loader
        if any(x is True for x in v.values()):
            return _obs('PRESENT', 'WebSettings.setAllowFileAccessFromFileURLs(loader object)', ev,
                        'SETTER_TRUE_ON_LOADER_SETTINGS', dur)
        if all(x is False for x in v.values()):
            return _obs('ABSENT', 'WebSettings.setAllowFileAccessFromFileURLs(loader object)', ev,
                        'SETTER_FALSE_ON_LOADER_SETTINGS', dur)
        return _obs('UNKNOWN', 'WebSettings.setAllowFileAccessFromFileURLs(loader object)', ev,
                    'SETTER_NOT_EXPLICITLY_SET_ON_LOADER', dur)
    if rule_id == 'WEBVIEW_JAVASCRIPT_ENABLED_UNTRUSTED':
        v = {wv: _final_value(scope, {wv}, 'setJavaScriptEnabled') for wv in loaders}
        if any(x is True for x in v.values()):
            return _obs('PRESENT', 'WebSettings.setJavaScriptEnabled(loader object)', ev,
                        'JS_ENABLED_WHILE_LOADING', dur)
        if all(x is False for x in v.values()):
            return _obs('ABSENT', 'WebSettings.setJavaScriptEnabled(loader object)', ev,
                        'JS_DISABLED_WHILE_LOADING', dur)
        return _obs('UNKNOWN', 'WebSettings.setJavaScriptEnabled(loader object)', ev,
                    'SETTER_NOT_EXPLICITLY_SET_ON_LOADER', dur)
    if rule_id == 'WEBVIEW_LOAD_BASEURL_FILE_WITH_UNIVERSAL_ACCESS':
        ldb = [l for l in scope.loads if l[1] == 'loadDataWithBaseURL']
        if not ldb:
            return _obs('UNKNOWN', rule_id, ev, 'NO_LOAD_DATA_WITH_BASEURL_IN_METHOD', dur)
        file_scheme = any(isinstance(a, str) and a.startswith('file:') for _, _, a in ldb)
        uni = {wv: _final_value(scope, {wv}, 'setAllowUniversalAccessFromFileURLs') for wv in loaders}
        uni_any_true = any(x is True for x in uni.values())
        uni_all_false = all(x is False for x in uni.values())
        if file_scheme and uni_any_true:
            return _obs('PRESENT', rule_id, ev, 'FILE_BASEURL_WITH_UNIVERSAL_ACCESS_TRUE', dur)
        if not file_scheme or uni_all_false:
            return _obs('ABSENT', rule_id, ev, 'FILE_BASEURL_REMOVED_OR_UNIVERSAL_ACCESS_FALSE', dur)
        return _obs('UNKNOWN', rule_id, ev, 'UNIVERSAL_ACCESS_NOT_EXPLICITLY_SET', dur)
    if rule_id == 'WEBVIEW_ALLOW_CONTENT_WITH_UNIVERSAL_ACCESS':
        content = {wv: _final_value(scope, {wv}, 'setAllowContentAccess') for wv in loaders}
        uni = {wv: _final_value(scope, {wv}, 'setAllowUniversalAccessFromFileURLs') for wv in loaders}
        pair = list(zip(content.values(), uni.values()))
        if any(c is None or u is None for c, u in pair):
            return _obs('UNKNOWN', rule_id, ev, 'SETTERS_NOT_BOTH_EXPLICITLY_SET_ON_LOADER', dur)
        if any(c is True and u is True for c, u in pair):
            return _obs('PRESENT', rule_id, ev, 'CONTENT_ACCESS_AND_UNIVERSAL_ACCESS_BOTH_TRUE', dur)
        return _obs('ABSENT', rule_id, ev, 'CONTENT_OR_UNIVERSAL_ACCESS_DISABLED', dur)
    raise ValueError(rule_id)


CHECKERS = {
    'WEBVIEW_COOKIE_ACCEPTANCE_DISABLED': _run,
    'WEBVIEW_ALLOW_FILE_ACCESS_FROM_FILE_URLS': _run,
    'WEBVIEW_JAVASCRIPT_ENABLED_UNTRUSTED': _run,
    'WEBVIEW_LOAD_BASEURL_FILE_WITH_UNIVERSAL_ACCESS': _run,
    'WEBVIEW_ALLOW_CONTENT_WITH_UNIVERSAL_ACCESS': _run,
}


def verify(rule_id, source_inputs, target_binding, rule_config):
    return CHECKERS[rule_id](rule_id, source_inputs, target_binding, rule_config)
