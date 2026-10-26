"""A2 sharing/config/identity rule family: FileProvider sharing with grant, provider
host binding, hardware identifier replacement. AST-based, object+usage point bound."""
import time
import xml.etree.ElementTree as ET
from javaparse import facts_for, select_method
from rules_webview import _invocations, _obs

ANDROID = '{http://schemas.android.com/apk/res/android}'


def check_share_content_uri(inputs, binding, cfg):
    start = time.perf_counter()
    facts = facts_for(inputs['java_file'])
    ev = [{'path': str(inputs['java_file']), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'cross-app file share URI scheme', ev, 'JAVA_PARSE_FAILED',
                    time.perf_counter() - start)
    method = select_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'cross-app file share URI scheme', ev,
                    'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    calls = _invocations(method['body'])
    names = [c.get('select', {}).get('name') for c in calls]
    from_file = [c for c in calls if c.get('select', {}).get('name') == 'fromFile'
                 and 'Uri' in str(c.get('select', {}).get('receiver', {}).get('text', '')
                                  or c.get('select', {}).get('receiver', {}).get('name', ''))]
    provider_uri = [c for c in calls if c.get('select', {}).get('name') == 'getUriForFile']
    grant_flag = any('FLAG_GRANT_READ_URI_PERMISSION' in str(c) for c in calls)
    ev.append({'method': binding['method'], 'start_line': method.get('start_line'),
               'uri_from_file_calls': len(from_file),
               'fileprovider_getUriForFile_calls': len(provider_uri),
               'grant_read_flag_present': grant_flag})
    dur = time.perf_counter() - start
    if from_file and provider_uri:
        return _obs('UNKNOWN', 'cross-app file share URI scheme', ev, 'MIXED_FILE_AND_CONTENT_URI', dur)
    if from_file:
        return _obs('PRESENT', 'cross-app file share URI scheme', ev,
                    'FILE_URI_VIA_Uri.fromFile_INTO_SHARE_INTENT', dur)
    if provider_uri and grant_flag:
        return _obs('ABSENT', 'cross-app file share URI scheme', ev,
                    'CONTENT_URI_VIA_FILEPROVIDER_WITH_TEMPORARY_GRANT', dur)
    if provider_uri and not grant_flag:
        return _obs('UNKNOWN', 'cross-app file share URI scheme', ev,
                    'CONTENT_URI_BUT_NO_TEMPORARY_GRANT', dur)
    return _obs('UNKNOWN', 'cross-app file share URI scheme', ev, 'NO_SHARE_URI_CONSTRUCTION_FOUND', dur)


def check_provider_host(inputs, binding, cfg):
    start = time.perf_counter()
    try:
        root = ET.parse(inputs['xml_file']).getroot()
    except Exception:
        return _obs('UNKNOWN', 'provider config host binding',
                    [{'path': str(inputs['xml_file'])}], 'XML_UNPARSEABLE',
                    time.perf_counter() - start)
    ev = [{'path': str(inputs['xml_file'])}]
    for prov in root.iter('provider'):
        if (prov.get('name') or '').lower() == cfg['provider_name'].lower():
            imap = prov.find('imap')
            if imap is None:
                return _obs('UNKNOWN', 'provider config host binding', ev,
                            'PROVIDER_HAS_NO_IMAP_ENTRY', time.perf_counter() - start)
            host = imap.get('host')
            ev.append({'provider': cfg['provider_name'], 'declared_imap_host': host,
                       'actual_endpoint': cfg['actual_host'],
                       'endpoint_source': cfg['endpoint_source']})
            if host == cfg['actual_host']:
                return _obs('ABSENT', 'provider config host binding', ev,
                            'HOST_MATCHES_PUBLIC_ENDPOINT', time.perf_counter() - start)
            return _obs('PRESENT', 'provider config host binding', ev,
                        'HOST_MISMATCHES_PUBLIC_ENDPOINT', time.perf_counter() - start)
    return _obs('UNKNOWN', 'provider config host binding', ev, 'PROVIDER_ENTRY_MISSING',
                time.perf_counter() - start)


HARDWARE_ID_APIS = {'getDeviceId', 'getImei', 'getMeid', 'getSubscriberId', 'getSerial', 'getLine1Number'}


def check_hardware_id(inputs, binding, cfg):
    start = time.perf_counter()
    facts = facts_for(inputs['java_file'])
    ev = [{'path': str(inputs['java_file']), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'instance identifier source', ev, 'JAVA_PARSE_FAILED',
                    time.perf_counter() - start)
    hw, uuid_calls = [], []
    from rules_webview import _iter_nodes
    for m in facts['methods']:
        vartypes = {}
        for st in _iter_nodes(m['body']):
            if st.get('kind') == 'VARIABLE':
                vartypes[st.get('name','')] = st.get('type', '')
        for c in _invocations(m['body']):
            sel = c.get('select', {})
            if sel.get('name') in HARDWARE_ID_APIS:
                recv = sel.get('receiver') or {}
                recv_name = recv.get('name') or ''
                declared = vartypes.get(recv_name, '')
                recv_text = recv.get('text') or recv_name
                if 'TelephonyManager' in declared or 'telephony' in recv_text.lower():
                    hw.append({'method': m['name'], 'api': sel.get('name'),
                               'receiver': recv_name, 'receiver_type': declared})
            if sel.get('name') == 'randomUUID':
                uuid_calls.append({'method': m['name']})
    # manifest permission as corroborating evidence only
    perm_ev = None
    man = inputs.get('manifest')
    if man:
        try:
            root = ET.parse(man).getroot()
            perm_ev = sorted(up.get(ANDROID + 'name') for up in root.findall('uses-permission'))
            ev.append({'manifest_permissions': perm_ev})
        except Exception:
            pass
    ev.append({'hardware_id_calls': hw, 'uuid_random_calls': uuid_calls})
    dur = time.perf_counter() - start
    if hw:
        return _obs('PRESENT', 'instance identifier source', ev,
                    'HARDWARE_IDENTIFIER_API_USED_FOR_INSTANCE_ID', dur)
    if uuid_calls:
        return _obs('ABSENT', 'instance identifier source', ev,
                    'RANDOM_UUID_USED_NO_HARDWARE_ID_API_IN_FILE', dur)
    return _obs('UNKNOWN', 'instance identifier source', ev, 'NO_ID_GENERATION_PATH_FOUND', dur)


CHECKERS = {
    'SHARE_CONTENT_URI_WITH_GRANT': check_share_content_uri,
    'PROVIDER_CONFIG_HOST_BINDING': check_provider_host,
    'HARDWARE_ID_REPLACE_UUID': check_hardware_id,
}


def verify(rule_id, source_inputs, target_binding, rule_config):
    return CHECKERS[rule_id](source_inputs, target_binding, rule_config)
