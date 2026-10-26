"""B1 rule family: decoded-input null guard, OAuth URL host duplication, push-body
word-boundary matching, retry-loop termination.

Java targets use the recovered JDK AST (javaparse.JavaFactsDeep). Kotlin targets have
no compiler in the workspace, so their function/class bodies are extracted with a
balanced-delimiter structural parser (strings and comments handled) and evaluated on
concrete boundary inputs; regex is only used to locate the target construct, never as
proof by substring presence.

verify(rule_id, source_inputs, target_binding, rule_config) -> observation dict.
"""
import pathlib
import re
import time

from javaparse import facts_for, select_method


def _obs(observation, scope, evidence, reason, duration_s=0.0):
    return {'observation': observation, 'scope': scope, 'evidence': evidence,
            'reason': reason, 'duration_s': duration_s}


# --------------------------------------------------------------------------- Java AST

def _iter_nodes(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from _iter_nodes(v)
    elif isinstance(node, list):
        for v in node:
            yield from _iter_nodes(v)


def _stmts(node):
    if not isinstance(node, dict):
        return []
    if node.get('kind') == 'BLOCK':
        return node.get('stmts') or []
    return [node]


def _cond_text(node):
    c = (node or {}).get('cond') or {}
    return c.get('text') or c.get('value') or ''


def _strip_outer_parens(s):
    s = (s or '').strip()
    while len(s) >= 2 and s[0] == '(' and s[-1] == ')':
        depth = 0
        ok = True
        for i, ch in enumerate(s):
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    ok = False
                    break
        if not ok:
            break
        s = s[1:-1].strip()
    return s


def _walk_stmt_tree(node, guards=None, out=None):
    """Yield (while_node, enclosing_guards) in source order.

    guards is a list of (cond_text, branch) where branch is 'then' or 'else'."""
    if guards is None:
        guards = []
    if out is None:
        out = []
    if isinstance(node, list):
        for n in node:
            _walk_stmt_tree(n, guards, out)
        return out
    if not isinstance(node, dict):
        return out
    k = node.get('kind')
    if k == 'WHILE_LOOP':
        out.append((node, list(guards)))
        _walk_stmt_tree(node.get('body'), guards, out)
        return out
    if k == 'IF':
        cond = _cond_text(node)
        _walk_stmt_tree(node.get('then'), guards + [(cond, 'then')], out)
        _walk_stmt_tree(node.get('else'), guards + [(cond, 'else')], out)
        return out
    if k == 'BLOCK':
        _walk_stmt_tree(node.get('stmts') or [], guards, out)
        return out
    if k == 'TRY':
        _walk_stmt_tree(node.get('body'), guards, out)
        for c in node.get('catches') or []:
            _walk_stmt_tree(c.get('body'), guards, out)
        _walk_stmt_tree(node.get('finally'), guards, out)
        return out
    for key in ('body', 'then', 'else', 'stmts'):
        if key in node:
            _walk_stmt_tree(node[key], guards, out)
    return out


def _find_new_class(node, type_name, arg_identifier=None):
    hits = []
    for n in _iter_nodes(node):
        if n.get('kind') != 'NEW_CLASS' or n.get('type') != type_name:
            continue
        if arg_identifier is None:
            hits.append(n)
            continue
        for a in n.get('args') or []:
            if a.get('kind') == 'IDENTIFIER' and a.get('name') == arg_identifier:
                hits.append(n)
                break
    return hits


def _is_decode_call(expr, method_name):
    if not isinstance(expr, dict) or expr.get('kind') != 'METHOD_INVOCATION':
        return False
    sel = expr.get('select') or {}
    return (sel.get('name') or '') == method_name


# ------------------------------------------------------------------- FP-05 null guard

def check_decoded_null_guard(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'decoded ciphertext null handling',
                    ev, 'JAVA_PARSE_FAILED', time.perf_counter() - start)
    method = select_method(facts, binding['method'])
    if method is None:
        return _obs('UNKNOWN', 'decoded ciphertext null handling',
                    ev, 'TARGET_METHOD_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)

    decode_method = cfg['decode_method']
    message_type = cfg['message_type']
    body = method['body']
    flat = list(_iter_nodes(body))

    decl = None
    for n in flat:
        if n.get('kind') == 'VARIABLE' and _is_decode_call(n.get('init'), decode_method):
            decl = n
            break
    if decl is None:
        return _obs('UNKNOWN', 'decoded ciphertext null handling', ev,
                    'NO_DECODE_ASSIGNMENT_IN_METHOD', time.perf_counter() - start)
    var = decl.get('name')

    uses = _find_new_class(body, message_type, arg_identifier=var)
    if not uses:
        return _obs('UNKNOWN', 'decoded ciphertext null handling', ev,
                    'DECODED_VALUE_NOT_USED_IN_TARGET_CONSTRUCTOR',
                    time.perf_counter() - start)

    # first use in AST/source order
    first_use = uses[0]
    idx_decl = next(i for i, n in enumerate(flat) if n is decl)
    idx_use = next(i for i, n in enumerate(flat) if n is first_use)

    guard = None
    for n in flat[idx_decl + 1:idx_use]:
        if n.get('kind') != 'IF':
            continue
        cond = _strip_outer_parens(_cond_text(n))
        if not re.fullmatch(rf'{re.escape(var)}\s*==\s*null|null\s*==\s*{re.escape(var)}', cond):
            continue
        then_nodes = list(_iter_nodes(n.get('then')))
        if any(t.get('kind') == 'THROW' for t in then_nodes):
            guard = {'kind': 'if_equals_null_then_throw', 'cond': cond}
            break
    if guard is None:
        # equivalent guard: use enclosed in if (v != null) { ... }
        for n in flat[idx_decl + 1:idx_use]:
            if n.get('kind') != 'IF':
                continue
            cond = _strip_outer_parens(_cond_text(n))
            if not re.fullmatch(rf'{re.escape(var)}\s*!=\s*null|null\s*!=\s*{re.escape(var)}', cond):
                continue
            if any(x is first_use for x in _iter_nodes(n.get('then'))):
                guard = {'kind': 'if_not_null_encloses_use', 'cond': cond}
                break
    require_non_null = False
    for n in flat[idx_decl + 1:idx_use]:
        if n.get('kind') == 'METHOD_INVOCATION':
            sel = n.get('select') or {}
            if (sel.get('name') or '') == 'requireNonNull':
                if any(a.get('kind') == 'IDENTIFIER' and a.get('name') == var
                       for a in n.get('args') or []):
                    require_non_null = True
                    break

    ev.append({'method': binding['method'], 'method_start_line': method.get('start_line'),
               'decoded_variable': var, 'decode_call': decode_method,
               'target_constructor': message_type, 'first_use': 'new ' + message_type,
               'guard': guard, 'require_non_null': require_non_null})
    dur = time.perf_counter() - start
    if guard or require_non_null:
        return _obs('ABSENT', 'decoded ciphertext null validation before decrypt', ev,
                    'DECODED_VALUE_NULL_CHECKED_BEFORE_USE', dur)
    return _obs('PRESENT', 'decoded ciphertext null validation before decrypt', ev,
                'DECODED_VALUE_USED_WITHOUT_NULL_CHECK', dur)


# ----------------------------------------------------------------- Kotlin structural

def _mask_kotlin(src):
    """Blank comments, keep string/char literals so offsets stay valid."""
    out = list(src)
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == '/' and i + 1 < n and src[i + 1] == '/':
            j = src.find('\n', i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = ' '
            i = j
        elif c == '/' and i + 1 < n and src[i + 1] == '*':
            j = src.find('*/', i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if src[k] != '\n':
                    out[k] = ' '
            i = j
        elif c == '"':
            if src.startswith('"""', i):
                j = src.find('"""', i + 3)
                i = n if j < 0 else j + 3
            else:
                i += 1
                while i < n:
                    if src[i] == '\\':
                        i += 2
                        continue
                    if src[i] == '"':
                        i += 1
                        break
                    i += 1
        elif c == "'":
            i += 1
            while i < n:
                if src[i] == '\\':
                    i += 2
                    continue
                if src[i] == "'":
                    i += 1
                    break
                i += 1
        else:
            i += 1
    return ''.join(out)


def _skip_string(s, i):
    q = s[i]
    if s.startswith('"""', i):
        j = s.find('"""', i + 3)
        return len(s) if j < 0 else j + 3
    i += 1
    while i < len(s):
        if s[i] == '\\':
            i += 2
            continue
        if s[i] == q:
            return i + 1
        i += 1
    return i


def _match_delim(s, i, open_ch, close_ch):
    if i >= len(s) or s[i] != open_ch:
        return -1
    depth = 0
    while i < len(s):
        c = s[i]
        if c in ('"', "'"):
            i = _skip_string(s, i)
            continue
        if c == open_ch:
            depth += 1
        elif c == close_ch:
            depth -= 1
            if depth == 0:
                return i
        i += 1
    return -1


def _extract_funs(src, name):
    """All function bodies with the given simple name (masked source)."""
    out = []
    for m in re.finditer(r'\bfun\s+' + re.escape(name) + r'\s*\(', _mask_kotlin(src)):
        o = m.end() - 1
        c = _match_delim(src, o, '(', ')')
        if c < 0:
            continue
        k = c + 1
        while k < len(src) and src[k] not in '{=':
            k += 1
        if k >= len(src) or src[k] != '{':
            continue
        end = _match_delim(src, k, '{', '}')
        if end < 0:
            continue
        out.append({'params': src[o + 1:c], 'body': src[k + 1:end],
                    'start': m.start(), 'body_start': k + 1})
    return out


def _extract_class(src, name):
    m = re.search(r'\bclass\s+' + re.escape(name) + r'\s*\(', _mask_kotlin(src))
    if not m:
        return None
    o = m.end() - 1
    c = _match_delim(src, o, '(', ')')
    if c < 0:
        return None
    k = c + 1
    while k < len(src) and src[k] != '{':
        k += 1
    if k >= len(src):
        return None
    end = _match_delim(src, k, '{', '}')
    if end < 0:
        return None
    return {'params': src[o + 1:c], 'body': src[k + 1:end]}


def _split_top(s, sep):
    parts = []
    depth = 0
    start = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in ('"', "'"):
            i = _skip_string(s, i)
            continue
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0 and s.startswith(sep, i):
            parts.append(s[start:i])
            i += len(sep)
            start = i
            continue
        i += 1
    parts.append(s[start:])
    return parts


def _find_top_token(s, token):
    depth = 0
    i = 0
    while i < len(s):
        c = s[i]
        if c in ('"', "'"):
            i = _skip_string(s, i)
            continue
        if c in '([{':
            depth += 1
        elif c in ')]}':
            depth -= 1
        elif depth == 0 and s.startswith(token, i):
            return i
        i += 1
    return -1


def _eval_template(e, env):
    i = 1
    out = []
    while i < len(e):
        ch = e[i]
        if ch == '\\':
            out.append(e[i + 1])
            i += 2
            continue
        if ch == '"':
            break
        if ch == '$' and i + 1 < len(e):
            if e[i + 1] == '{':
                j = _match_delim(e, i + 1, '{', '}')
                out.append(str(_eval_expr(e[i + 2:j], env)))
                i = j + 1
                continue
            m = re.match(r'[A-Za-z_]\w*', e[i + 1:])
            if m:
                name = m.group(0)
                if name not in env:
                    raise ValueError('UNKNOWN_TEMPLATE_VAR:' + name)
                out.append(str(env[name]))
                i += 1 + len(name)
                continue
        out.append(ch)
        i += 1
    return ''.join(out)


def _eval_branch(text, env):
    text = text.strip()
    if text.startswith('{'):
        end = _match_delim(text, 0, '{', '}')
        return text[1:end], text[end + 1:]
    idx = _find_top_token(text, 'else')
    if idx >= 0:
        return text[:idx], text[idx:]
    return text, ''


def _eval_if(e, env):
    m = re.match(r'if\s*\(', e)
    if not m:
        raise ValueError('IF_SYNTAX')
    o = m.end() - 1
    c = _match_delim(e, o, '(', ')')
    cond = e[o + 1:c]
    rest = e[c + 1:].strip()
    then_txt, remainder = _eval_branch(rest, env)
    truth = _eval_cond(cond, env)
    if truth:
        return _eval_expr(then_txt, env)
    remainder = remainder.strip()
    if remainder.startswith('else'):
        return _eval_expr(remainder[4:].strip(), env)
    raise ValueError('IF_WITHOUT_ELSE')


def _eval_operand(e, env):
    e = e.strip()
    if e == 'null':
        return None
    if e in ('true', 'false'):
        return e == 'true'
    if re.fullmatch(r'-?\d+', e):
        return int(e)
    if e.startswith('"'):
        return _eval_template(e, env)
    m = re.fullmatch(r'(.+)\.removeTrailingSlash\(\)', e, re.S)
    if m:
        return str(_eval_operand(m.group(1), env)).rstrip('/')
    if re.fullmatch(r'[A-Za-z_]\w*', e):
        if e in env:
            return env[e]
        raise ValueError('UNKNOWN_IDENT:' + e)
    raise ValueError('OPERAND:' + e)


def _eval_cond(c, env):
    c = _strip_outer_parens(c)
    if c.startswith('!'):
        return not _eval_cond(c[1:], env)
    for op in ('||', '&&'):
        parts = _split_top(c, op)
        if len(parts) > 1:
            vals = [_eval_cond(p, env) for p in parts]
            return any(vals) if op == '||' else all(vals)
    m = re.fullmatch(r'(.+)\.contains\((.+)\)', c, re.S)
    if m:
        hay = _eval_operand(m.group(1), env)
        needle = _eval_operand(m.group(2), env)
        return str(needle) in str(hay)
    m = re.fullmatch(r'(.+)\.startsWith\((.+)\)', c, re.S)
    if m:
        hay = _eval_operand(m.group(1), env)
        prefix = _eval_operand(m.group(2), env)
        return str(hay).startswith(str(prefix))
    m = re.fullmatch(r'(.+)\s+in\s+(.+)', c, re.S)
    if m:
        needle = _eval_operand(m.group(1), env)
        hay = _eval_operand(m.group(2), env)
        return needle in hay
    for op in ('==', '!='):
        parts = _split_top(c, op)
        if len(parts) == 2:
            a = _eval_operand(parts[0], env)
            b = _eval_operand(parts[1], env)
            return (a == b) if op == '==' else (a != b)
    raise ValueError('COND:' + c)


def _eval_expr(expr, env):
    e = expr.strip()
    if e.startswith('return '):
        e = e[7:].strip()
    while (e.startswith('(') and _match_delim(e, 0, '(', ')') == len(e) - 1) \
            or (e.startswith('{') and _match_delim(e, 0, '{', '}') == len(e) - 1):
        e = e[1:-1].strip()
    if e.startswith('if'):
        return _eval_if(e, env)
    idx = _find_top_token(e, '.let')
    if idx >= 0:
        recv = _eval_expr(e[:idx], env)
        rest = e[idx + 4:].strip()
        if not rest.startswith('{'):
            raise ValueError('LET_WITHOUT_BLOCK')
        end = _match_delim(rest, 0, '{', '}')
        inner = dict(env)
        inner['it'] = recv
        return _eval_expr(rest[1:end], inner)
    parts = _split_top(e, '+')
    if len(parts) > 1:
        return ''.join(str(_eval_expr(p, env)) for p in parts)
    if e.startswith('"'):
        return _eval_template(e, env)
    return _eval_operand(e, env)


def _top_level_return(body):
    idx = _find_top_token(body, 'return')
    if idx < 0:
        return None
    return body[idx + 6:]


# ------------------------------------------------------- FP-06 OAuth host duplication

def check_oauth_host_duplication(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['kotlin_file'])
    src = path.read_text()
    ev = [{'path': str(path), 'sha256': inputs.get('kotlin_file_sha256', '')}]
    masked = _mask_kotlin(src)
    funs = _extract_funs(masked, binding['method'])
    if len(funs) != 1:
        return _obs('UNKNOWN', 'custom OAuth URL host composition', ev,
                    'TARGET_FUNCTION_NOT_UNIQUE_OR_MISSING', time.perf_counter() - start)
    body = funs[0]['body']

    expr = _top_level_return(body)
    if expr is None:
        # expression-bodied / single let-expression function
        expr = body.strip()
    if not expr:
        return _obs('UNKNOWN', 'custom OAuth URL host composition', ev,
                    'NO_RETURN_EXPRESSION', time.perf_counter() - start)

    host = cfg.get('host_param', 'host')
    authorize_path = cfg.get('path_param', 'authorizePath')
    base = {'host': 'https://example.com',
            'clientId': 'client-id', 'serverUrl': 'https://chat.example.com/',
            'serviceName': 'gitlab', 'state': 'state-token', 'scope': 'read_user'}
    boundary = [
        ('absolute_authorize_path', dict(base, **{authorize_path: 'https://example.com/oauth/authorize'})),
        ('relative_authorize_path', dict(base, **{authorize_path: '/oauth/authorize'})),
    ]
    results = []
    for name, env in boundary:
        try:
            url = _eval_expr(expr, env)
        except Exception as exc:
            ev.append({'boundary_input': name, 'eval_error': repr(exc)})
            return _obs('UNKNOWN', 'custom OAuth URL host composition', ev,
                        'BOUNDARY_EVALUATION_FAILED:' + name, time.perf_counter() - start)
        results.append({'boundary_input': name, 'authorize_path': env[authorize_path],
                        'url': url, 'host_occurrences': url.count(env[host])})
    ev.append({'method': binding['method'], 'expression': expr,
               'boundary_results': results})
    dur = time.perf_counter() - start

    abs_case = next(r for r in results if r['boundary_input'] == 'absolute_authorize_path')
    rel_case = next(r for r in results if r['boundary_input'] == 'relative_authorize_path')
    if abs_case['host_occurrences'] >= 2:
        return _obs('PRESENT', 'custom OAuth URL host composition', ev,
                    'HOST_DUPLICATED_WHEN_AUTHORIZE_PATH_ALREADY_ABSOLUTE', dur)
    if abs_case['host_occurrences'] == 1 and rel_case['host_occurrences'] == 1 \
            and rel_case['url'].startswith(base['host']):
        return _obs('ABSENT', 'custom OAuth URL host composition', ev,
                    'HOST_GUARD_KEEPS_SINGLE_HOST_FOR_ABSOLUTE_AND_RELATIVE_PATHS', dur)
    return _obs('UNKNOWN', 'custom OAuth URL host composition', ev,
                'HOST_COMPOSITION_RESULT_UNEXPECTED', dur)


# ---------------------------------------------------- FP-25 push body word boundary

def check_push_body_word_boundary(inputs, binding, cfg):
    start = time.perf_counter()
    em_path = pathlib.Path(inputs['event_match_file'])
    pc_path = pathlib.Path(inputs['push_condition_file'])
    em_src = _mask_kotlin(em_path.read_text())
    pc_src = _mask_kotlin(pc_path.read_text())
    ev = [{'path': str(em_path), 'sha256': inputs.get('event_match_file_sha256', '')},
          {'path': str(pc_path), 'sha256': inputs.get('push_condition_file_sha256', '')}]

    cls = _extract_class(em_src, cfg.get('condition_class', 'EventMatchCondition'))
    if cls is None:
        return _obs('UNKNOWN', 'content.body push-condition word boundary', ev,
                    'CONDITION_CLASS_NOT_FOUND', time.perf_counter() - start)
    funs = [f for f in _extract_funs(cls['body'], binding['method'])
            if all(tok in f['params'] for tok in cfg.get('signature_tokens', []))]
    exclude = cfg.get('signature_exclude', ['ConditionResolver'])
    if len(funs) > 1:
        narrowed = [f for f in funs if not any(tok in f['params'] for tok in exclude)]
        if len(narrowed) == 1:
            funs = narrowed
    if len(funs) != 1:
        return _obs('UNKNOWN', 'content.body push-condition word boundary', ev,
                    'TARGET_MATCH_METHOD_NOT_UNIQUE', time.perf_counter() - start)
    match_body = funs[0]['body']

    body_key = cfg.get('body_key', 'content.body')
    boundary_in_body = False
    key_pos = match_body.find('"%s"' % body_key)
    if key_pos >= 0:
        k = match_body.find('{', key_pos)
        if k >= 0:
            end = _match_delim(match_body, k, '{', '}')
            branch = match_body[k + 1:end] if end > 0 else match_body[k:]
            boundary_in_body = ('(\\\\W|^)' in branch) or ('(\\W|^)' in branch) \
                or ('\\b' in branch and 'boundary' in branch.lower())
    words_param = bool(re.search(r'\bwordsOnly\s*:\s*Boolean', cls['params']))
    substring_path = ('containsMatchIn' in match_body) and bool(
        re.search(r'if\s*\(\s*wordsOnly\s*\)', match_body))
    rule_scoped = bool(re.search(r'RULE_ID_CONTAIN_USER_NAME', pc_src)) and bool(
        re.search(r'EventMatchCondition\s*\(', pc_src))

    ev.append({'condition_class': cfg.get('condition_class', 'EventMatchCondition'),
               'constructor_has_wordsOnly': words_param,
               'match_method': binding['method'],
               'substring_glob_path': substring_path,
               'content_body_word_boundary_branch': boundary_in_body,
               'rule_id_scoped_words_only': rule_scoped})
    dur = time.perf_counter() - start
    if boundary_in_body:
        return _obs('ABSENT', 'content.body push-condition word boundary', ev,
                    'CONTENT_BODY_MATCHED_AT_WORD_BOUNDARY', dur)
    if words_param and (substring_path or rule_scoped):
        return _obs('PRESENT', 'content.body push-condition word boundary', ev,
                    'CONTENT_BODY_GLOB_SUBSTRING_UNLESS_USERNAME_RULE', dur)
    return _obs('UNKNOWN', 'content.body push-condition word boundary', ev,
                'WORD_BOUNDARY_SEMANTICS_UNRESOLVED', dur)


# ------------------------------------------------------- FP-29 retry loop termination

def _eval_operand_java(e, env):
    e = e.strip()
    if e == 'null':
        return None
    if e in ('true', 'false'):
        return e == 'true'
    if re.fullmatch(r'-?\d+', e):
        return int(e)
    m = re.fullmatch(r'(.+)\.size\(\)', e, re.S)
    if m:
        return len(_eval_operand_java(m.group(1), env))
    m = re.fullmatch(r'(.+)\.isEmpty\(\)', e, re.S)
    if m:
        return len(_eval_operand_java(m.group(1), env)) == 0
    m = re.fullmatch(r'(.+)\.length(?:\(\))?', e, re.S)
    if m:
        return len(_eval_operand_java(m.group(1), env))
    if re.fullmatch(r'[A-Za-z_]\w*', e):
        if e in env:
            return env[e]
        raise ValueError('UNKNOWN_IDENT:' + e)
    raise ValueError('OPERAND:' + e)


def _eval_cond_java(c, env):
    c = _strip_outer_parens(c)
    if c.startswith('!'):
        return not _eval_cond_java(c[1:], env)
    for op in ('||', '&&'):
        parts = _split_top(c, op)
        if len(parts) > 1:
            vals = [_eval_cond_java(p, env) for p in parts]
            return any(vals) if op == '||' else all(vals)
    for op in ('==', '!=', '<=', '>=', '<', '>'):
        parts = _split_top(c, op)
        if len(parts) == 2:
            a = _eval_operand_java(parts[0], env)
            b = _eval_operand_java(parts[1], env)
            if op == '==':
                return a == b
            if op == '!=':
                return a != b
            if op == '<=':
                return a <= b
            if op == '>=':
                return a >= b
            if op == '<':
                return a < b
            return a > b
    try:
        v = _eval_operand_java(c, env)
        if isinstance(v, bool):
            return v
    except Exception:
        pass
    raise ValueError('COND:' + c)


def _exec_inline(node, env):
    """Execute one body-level statement under the zero-inner-iteration scenario.

    Returns (signal, updated_env) where signal is None|'break'|'return'|'throw'."""
    if not isinstance(node, dict):
        return None
    k = node.get('kind')
    if k == 'BLOCK':
        for st in node.get('stmts') or []:
            sig = _exec_inline(st, env)
            if sig in ('break', 'return', 'throw'):
                return sig
        return None
    if k == 'BREAK':
        return 'break'
    if k in ('RETURN', 'THROW'):
        return 'return' if k == 'RETURN' else 'throw'
    if k == 'VARIABLE':
        try:
            env[node.get('name')] = _eval_operand_java(
                str((node.get('init') or {}).get('value', 'UNKNOWN')), env)
        except Exception:
            env[node.get('name')] = 'UNKNOWN'
        return None
    if k == 'EXPRESSION_STATEMENT':
        expr = node.get('expr') or {}
        if expr.get('kind') == 'ASSIGNMENT':
            var = (expr.get('variable') or {}).get('name')
            rhs = expr.get('expr') or {}
            try:
                if rhs.get('kind', '').endswith('LITERAL'):
                    env[var] = _eval_operand_java(str(rhs.get('value')), env)
                elif rhs.get('kind') == 'IDENTIFIER':
                    env[var] = env.get(rhs.get('name'), 'UNKNOWN')
                else:
                    env[var] = 'UNKNOWN'
            except Exception:
                env[var] = 'UNKNOWN'
        return None
    if k == 'IF':
        try:
            truth = _eval_cond_java(_cond_text(node), env)
        except Exception:
            return None
        if truth:
            return _exec_inline(node.get('then'), env)
        if node.get('else'):
            return _exec_inline(node.get('else'), env)
        return None
    return None


def _simulate_while(loop, env):
    """Simulate the loop for the boundary input already stored in env."""
    cond = _cond_text(loop)
    body = loop.get('body')
    trace = []
    seen = []
    for _ in range(8):
        try:
            if not _eval_cond_java(cond, env):
                return 'TERMINATES', trace
        except Exception:
            return 'UNKNOWN', trace
        snapshot_before = dict(env)
        signal = None
        for st in _stmts(body):
            if st.get('kind') in ('FOR_LOOP', 'ENHANCED_FOR_LOOP', 'WHILE_LOOP', 'DO_WHILE_LOOP'):
                continue  # empty collection: zero inner iterations
            signal = _exec_inline(st, env)
            if signal in ('break', 'return', 'throw'):
                break
        trace.append({k: env.get(k) for k in ('result', 'format', 'hasOneFormat')
                      if k in env} | {'signal': signal})
        if signal in ('break', 'return', 'throw'):
            return 'TERMINATES', trace
        if env == snapshot_before:
            return 'NON_TERMINATING', trace
        seen.append(dict(env))
    if len(seen) >= 2 and seen[-1] == seen[-2]:
        return 'NON_TERMINATING', trace
    return 'UNKNOWN', trace


def check_retry_loop_termination(inputs, binding, cfg):
    start = time.perf_counter()
    path = pathlib.Path(inputs['java_file'])
    facts = facts_for(path)
    ev = [{'path': str(path), 'sha256': facts.get('_source_sha256', ''),
           'parse_ok': facts.get('parse_ok')}]
    if not facts.get('parse_ok'):
        return _obs('UNKNOWN', 'retry loop termination', ev, 'JAVA_PARSE_FAILED',
                    time.perf_counter() - start)

    verdicts = []
    for method_name in binding['methods']:
        method = select_method(facts, method_name)
        if method is None:
            return _obs('UNKNOWN', 'retry loop termination', ev,
                        'TARGET_METHOD_NOT_UNIQUE_OR_MISSING:' + method_name,
                        time.perf_counter() - start)
        env = {}
        for p in method.get('params') or []:
            pname = p.get('name')
            env[pname] = 'NONNULL' if pname == cfg.get('format_param', 'format') else []
        for n in _iter_nodes(method['body']):
            if n.get('kind') == 'VARIABLE' and n.get('name') not in env:
                init = n.get('init') or {}
                if init.get('kind', '').endswith('LITERAL'):
                    try:
                        env[n['name']] = _eval_operand_java(str(init.get('value')), env)
                    except Exception:
                        env[n['name']] = 'UNKNOWN'
        loops = _walk_stmt_tree(method['body'])
        if not loops:
            return _obs('UNKNOWN', 'retry loop termination', ev,
                        'NO_LOOP_IN_TARGET_METHOD:' + method_name,
                        time.perf_counter() - start)
        method_verdicts = []
        for loop, guards in loops:
            cond = _strip_outer_parens(_cond_text(loop))
            if not re.fullmatch(rf'{re.escape(cfg.get("loop_var", "result"))}\s*==\s*-1', cond):
                continue
            reachable = True
            guard_eval = []
            for gcond, branch in guards:
                try:
                    truth = _eval_cond_java(gcond, env)
                except Exception:
                    truth = None
                guard_eval.append({'guard': gcond, 'branch': branch, 'value': truth})
                if branch == 'then' and truth is False:
                    reachable = False
                if branch == 'else' and truth is True:
                    reachable = False
            if not reachable:
                method_verdicts.append({'loop': cond, 'verdict': 'NOT_REACHED',
                                        'guards': guard_eval, 'trace': []})
                continue
            verdict, trace = _simulate_while(loop, dict(env))
            method_verdicts.append({'loop': cond, 'verdict': verdict,
                                    'guards': guard_eval, 'trace': trace})
        if not method_verdicts:
            return _obs('UNKNOWN', 'retry loop termination', ev,
                        'BOUNDARY_LOOP_NOT_FOUND:' + method_name, time.perf_counter() - start)
        verdicts.append({'method': method_name, 'loops': method_verdicts})

    ev.append({'boundary_input': {'streams': 'empty non-null list',
                                  'format': 'non-null'},
               'methods': verdicts})
    dur = time.perf_counter() - start
    flat = [l['verdict'] for m in verdicts for l in m['loops']]
    if 'NON_TERMINATING' in flat:
        return _obs('PRESENT', 'retry loop termination', ev,
                    'LOOP_EXIT_UNREACHABLE_FOR_EMPTY_LIST_NON_NULL_FORMAT', dur)
    if all(v in ('TERMINATES', 'NOT_REACHED') for v in flat):
        return _obs('ABSENT', 'retry loop termination', ev,
                    'LOOP_TERMINATES_OR_NOT_REACHED_FOR_BOUNDARY_INPUT', dur)
    return _obs('UNKNOWN', 'retry loop termination', ev, 'LOOP_VERDICT_UNRESOLVED', dur)


CHECKERS = {
    'DECODED_INPUT_NULL_GUARD': check_decoded_null_guard,
    'OAUTH_URL_HOST_DUPLICATION_GUARD': check_oauth_host_duplication,
    'PUSH_BODY_WORD_BOUNDARY': check_push_body_word_boundary,
    'RETRY_LOOP_TERMINATION': check_retry_loop_termination,
}


def verify(rule_id, source_inputs, target_binding, rule_config):
    return CHECKERS[rule_id](source_inputs, target_binding, rule_config)
