"""C1 helpers: Kotlin structural parser and Java condition/switch analysis.

Kotlin has no recovered JDK AST here (javac only parses Java), so this module
provides a real tokenizer + structural parser: balanced blocks, function
declarations, control-flow statements, call chains with receivers, lambda
parameters, and implicit `it` binding. It is not a regex/string-presence test;
control-flow facts come from the parsed structure and every rule decision is
made on those nodes.

Java-side helpers fill two gaps of the A-batch JavaFactsDeep serializer that
this family cannot modify: binary/unary conditions (serialized as normalized
source text) are parsed by a small precedence parser, and switch case labels
(dropped by the serializer) are recovered from the method source range.
"""
import re

# ---------------------------------------------------------------- tokenizer

_OPERATORS = ['===', '!==', '..<', '?.', '?:', '!!', '->', '==', '!=', '<=',
              '>=', '&&', '||', '+=', '-=', '*=', '/=', '%=', '::', '..',
              '++', '--']
_SINGLE = set('{}()[],;:.=+-*/%<>!?@')

_CONT_NEXT = {'.', '?.', '?:', '&&', '||', '==', '!=', '===', '!==', '<=',
              '>=', '+', '-', '*', '/', '%', '=', '->', ',', ':', 'else',
              'catch', 'finally', 'is', 'as', '!in'}
_CONT_PREV = {'=', '+', '-', '*', '/', '%', '&&', '||', '==', '!=', '<=',
              '>=', '<', '>', '.', '?.', '?:', '!!', '->', ',', ':', '(', '[',
              '{', '@', 'if', 'else', 'while', 'for', 'in', 'is',
              'as', 'when', '!', 'throw'}

_MODIFIERS = {'private', 'public', 'internal', 'protected', 'override', 'val',
              'var', 'lateinit', 'open', 'final', 'abstract', 'suspend',
              'inline', 'crossinline', 'noinline', 'const', 'operator',
              'infix', 'external', 'tailrec'}


class Tok:
    __slots__ = ('kind', 'val', 'line')

    def __init__(self, kind, val, line):
        self.kind = kind
        self.val = val
        self.line = line

    def __repr__(self):
        return f'{self.kind}:{self.val}@{self.line}'


def tokenize(src):
    toks, i, n, line = [], 0, len(src), 1
    while i < n:
        c = src[i]
        if c == '\n':
            toks.append(Tok('NL', '\n', line))
            line += 1
            i += 1
            continue
        if c in ' \t\r':
            i += 1
            continue
        if src.startswith('//', i):
            j = src.find('\n', i)
            i = n if j < 0 else j
            continue
        if src.startswith('/*', i):
            j = src.find('*/', i + 2)
            j = n if j < 0 else j + 2
            line += src[i:j].count('\n')
            i = j
            continue
        if src.startswith('"""', i):
            j = src.find('"""', i + 3)
            j = n if j < 0 else j + 3
            line += src[i:j].count('\n')
            toks.append(Tok('STR', src[i:j], line))
            i = j
            continue
        if c in '"\'':
            q, j = c, i + 1
            while j < n:
                if src[j] == '\\':
                    j += 2
                    continue
                if src[j] == q:
                    j += 1
                    break
                if q == '"' and src.startswith('${', j):
                    depth, j = 1, j + 2
                    while j < n and depth:
                        if src[j] == '{':
                            depth += 1
                        elif src[j] == '}':
                            depth -= 1
                        j += 1
                    continue
                j += 1
            toks.append(Tok('STR', src[i:j], line))
            line += src[i:j].count('\n')
            i = j
            continue
        if c == '`':
            j = src.find('`', i + 1)
            j = n if j < 0 else j + 1
            toks.append(Tok('IDENT', src[i + 1:j - 1], line))
            i = j
            continue
        if c.isalpha() or c == '_':
            j = i
            while j < n and (src[j].isalnum() or src[j] == '_'):
                j += 1
            toks.append(Tok('IDENT', src[i:j], line))
            i = j
            continue
        if c.isdigit():
            j = i
            while j < n and (src[j].isalnum() or src[j] in '._'):
                j += 1
            toks.append(Tok('NUM', src[i:j], line))
            i = j
            continue
        op = next((o for o in _OPERATORS if src.startswith(o, i)), None)
        if op:
            toks.append(Tok('OP', op, line))
            i += len(op)
            continue
        if c in _SINGLE:
            toks.append(Tok('PUNCT', c, line))
            i += 1
            continue
        i += 1
    return toks


def match(toks, i):
    """Index of the bracket closing toks[i] (same kind), or last index."""
    pairs = {'(': ')', '[': ']', '{': '}', '<': '>'}
    open_v = toks[i].val
    close_v = pairs.get(open_v)
    if close_v is None:
        return i
    depth, j = 0, i
    while j < len(toks):
        v = toks[j].val
        if v == open_v:
            depth += 1
        elif v == close_v:
            depth -= 1
            if depth == 0:
                return j
        j += 1
    return len(toks) - 1


def _significant(toks, i, step, limit):
    while 0 <= i < limit and toks[i].kind == 'NL':
        i += step
    return i


def _can_end(t):
    return t.kind in ('IDENT', 'STR', 'NUM') or t.val in (')', ']', '}', '!!', '++', '--')


def _can_start(t):
    if t.kind != 'IDENT':
        return t.val == '@'
    return t.val in ('if', 'for', 'while', 'return', 'val', 'var', 'when',
                     'try', 'throw', 'object', 'super', 'this') or t.val not in _CONT_NEXT


def split_statements(toks, a, b):
    out, start, depth, i = [], a, 0, a
    while i < b:
        v = toks[i].val
        if v in '([{':
            depth += 1
        elif v in ')]}':
            depth -= 1
        elif depth == 0 and (v == ';' or toks[i].kind == 'NL'):
            if v == ';':
                if start < i:
                    out.append((start, i))
                start = i + 1
            else:
                prev = toks[i - 1] if i - 1 >= start else None
                ni = _significant(toks, i + 1, 1, b)
                if prev and ni < b:
                    nxt = toks[ni]
                    if (_can_end(prev) and _can_start(nxt)
                            and nxt.val not in _CONT_NEXT and prev.val not in _CONT_PREV):
                        out.append((start, i))
                        start = ni
        i += 1
    if start < b:
        out.append((start, b))
    return [(x, y) for x, y in out if x < y]


# ------------------------------------------------------------ expressions

def _try_type_args(toks, i, b):
    """Parse <A, B<C>> at i. Returns (type_names, next_index) or ([], i)."""
    if i >= b or toks[i].val != '<':
        return [], i
    depth, j, names, cur = 0, i, [], []
    while j < b:
        v = toks[j].val
        if v == '<':
            depth += 1
            if depth > 1:
                cur.append(v)
            j += 1
            continue
        if v == '>':
            depth -= 1
            if depth == 0:
                if cur:
                    names.append(''.join(cur))
                return names, j + 1
            cur.append(v)
            j += 1
            continue
        if v == ',' and depth == 1:
            names.append(''.join(cur))
            cur = []
            j += 1
            continue
        cur.append(v)
        j += 1
    return [], i


def parse_args(toks, a, b):
    args, start, depth = [], a, 0
    for i in range(a, b + 1):
        v = toks[i].val if i < b else ','
        if i < b and v in '([{':
            depth += 1
        elif i < b and v in ')]}':
            depth -= 1
        if v == ',' and depth == 0:
            seg = (start, i)
            while seg[0] < seg[1] and toks[seg[0]].kind == 'NL':
                seg = (seg[0] + 1, seg[1])
            while seg[1] > seg[0] and toks[seg[1] - 1].kind == 'NL':
                seg = (seg[0], seg[1] - 1)
            if seg[0] < seg[1]:
                name = None
                if (toks[seg[0]].kind == 'IDENT' and seg[0] + 1 < seg[1]
                        and toks[seg[0] + 1].val == '='):
                    name = toks[seg[0]].val
                    seg = (seg[0] + 2, seg[1])
                if seg[0] < seg[1]:
                    args.append({'name': name, 'range': seg})
            start = i + 1
    return args


def parse_lambda(toks, open_i, close_i):
    depth, arrow = 0, None
    for i in range(open_i + 1, close_i):
        v = toks[i].val
        if v in '([{':
            depth += 1
        elif v in ')]}':
            depth -= 1
        elif depth == 0 and v == '->':
            arrow = i
            break
    if arrow is None:
        return {'params': ['it'], 'implicit_it': True, 'body': (open_i + 1, close_i)}
    names, cur = [], []
    depth = 0
    for i in range(open_i + 1, arrow):
        v = toks[i].val
        if v in '([{':
            depth += 1
        elif v in ')]}':
            depth -= 1
        elif depth == 0 and v == ',':
            if cur:
                names.append(cur[0])
            cur = []
            continue
        if depth == 0 and toks[i].kind == 'IDENT' and not cur:
            cur.append(v)
    if cur:
        names.append(cur[0])
    return {'params': names, 'implicit_it': False, 'body': (arrow + 1, close_i)}


def parse_expr(toks, a, b):
    a, b = _trim(toks, a, b)
    if a >= b:
        return {'kind': 'empty'}
    node, rest = _parse_binary(toks, a, b, 0)
    if rest < b:
        return {'kind': 'opaque', 'range': (a, b)}
    return node


_BIN_LEVELS = [('||',), ('&&',), ('==', '!=', '===', '!=='), ('<', '>', '<=', '>='),
               ('in', '!in', 'is', 'as'), ('?:',), ('..', '..<'), ('+', '-'),
               ('*', '/', '%')]


def _parse_binary(toks, a, b, level):
    if level >= len(_BIN_LEVELS):
        return _parse_unary(toks, a, b)
    ops = _BIN_LEVELS[level]
    skip = set()
    i = a
    while i < b:
        if toks[i].val == '<' and i > 0 and toks[i - 1].kind == 'IDENT':
            names, ni = _try_type_args(toks, i, b)
            if names and (ni >= b or toks[ni].kind == 'NL'
                          or toks[ni].val in ('(', '{', '.', ',', ')', ']', ';')):
                skip.update(range(i, ni))
                i = ni
                continue
        i += 1
    depth, split = 0, None
    for i in range(a, b):
        v = toks[i].val
        if v in '([{':
            depth += 1
        elif v in ')]}':
            depth -= 1
        elif depth == 0 and i > a and v in ops and i not in skip:
            split = i
    if split is None:
        return _parse_binary(toks, a, b, level + 1)
    left, _ = _parse_binary(toks, a, split, level)
    right, _ = _parse_binary(toks, split + 1, b, level)
    return {'kind': 'binary', 'op': toks[split].val, 'left': left, 'right': right}, b


def _parse_unary(toks, a, b):
    if a < b and toks[a].val in ('!', '-', '+', '++', '--'):
        operand, _ = _parse_unary(toks, a + 1, b)
        return {'kind': 'unary', 'op': toks[a].val, 'operand': operand}, b
    if a < b and toks[a].val == '@':
        i = a + 1
        while i < b and toks[i].kind == 'IDENT':
            i += 1
            if i < b and toks[i].val == '(':
                i = match(toks, i) + 1
            if i < b and toks[i].val == ':':
                i += 1
            break
        return _parse_unary(toks, i, b)
    return _parse_postfix(toks, a, b)


def _parse_postfix(toks, a, b):
    base, i = _parse_primary(toks, a, b)
    suffixes = []
    if i < b and toks[i].val == '<':
        targs, i2 = _try_type_args(toks, i, b)
        if targs and (i2 >= b or toks[i2].kind == 'NL'
                      or toks[i2].val in ('(', '{', '.', ',', ')', ']', ';')):
            suffixes.append({'t': 'typeargs', 'names': targs})
            i = i2
    while i < b:
        v = toks[i].val
        if v in ('.', '?.') and i + 1 < b and toks[i + 1].kind == 'IDENT':
            name = toks[i + 1].val
            i += 2
            targs, i2 = _try_type_args(toks, i, b)
            if targs and (i2 >= b or toks[i2].kind == 'NL'
                          or toks[i2].val in ('(', '{', '.', ',', ')', ']', ';')):
                i = i2
            args, lam = [], None
            if i < b and toks[i].val == '(':
                e = match(toks, i)
                args = parse_args(toks, i + 1, e)
                i = e + 1
            if i < b and toks[i].val == '{':
                e = match(toks, i)
                lam = parse_lambda(toks, i, e)
                i = e + 1
            suffixes.append({'t': 'member', 'name': name, 'type_args': targs,
                             'args': args, 'lambda': lam})
            continue
        if v == '(':
            e = match(toks, i)
            suffixes.append({'t': 'call', 'args': parse_args(toks, i + 1, e)})
            i = e + 1
            continue
        if v == '{':
            e = match(toks, i)
            suffixes.append({'t': 'lambda', 'lambda': parse_lambda(toks, i, e)})
            i = e + 1
            continue
        if v in ('!!', '?'):
            suffixes.append({'t': 'postfix', 'op': v})
            i += 1
            continue
        if v == '[':
            e = match(toks, i)
            suffixes.append({'t': 'index', 'range': (i + 1, e)})
            i = e + 1
            continue
        if v == '::' and i + 1 < b:
            suffixes.append({'t': 'ref', 'name': toks[i + 1].val})
            i += 2
            continue
        break
    return {'kind': 'chain', 'base': base, 'suffixes': suffixes}, i


def _parse_primary(toks, a, b):
    if a >= b:
        return {'kind': 'empty'}, b
    t = toks[a]
    if t.kind == 'IDENT' and t.val in ('if', 'when', 'try'):
        return {'kind': 'opaque', 'range': (a, b)}, b
    if t.kind in ('IDENT', 'NUM', 'STR'):
        return {'kind': 'name' if t.kind == 'IDENT' else 'literal', 'name': t.val}, a + 1
    if t.val == '(':
        e = match(toks, a)
        return {'kind': 'paren', 'expr': parse_expr(toks, a + 1, e)}, e + 1
    if t.val == '{':
        e = match(toks, a)
        return {'kind': 'lambda', 'lambda': parse_lambda(toks, a, e)}, e + 1
    return {'kind': 'opaque', 'range': (a, b)}, b


def _trim(toks, a, b):
    while a < b and toks[a].kind == 'NL':
        a += 1
    while b > a and toks[b - 1].kind == 'NL':
        b -= 1
    return a, b


def chain_names(node):
    """Names along a chain, e.g. ['userEntity','devices','iterator','forEach']."""
    if node.get('kind') != 'chain':
        return []
    base = node['base']
    names = [base.get('name')] if base.get('kind') == 'name' else []
    for s in node['suffixes']:
        if s['t'] in ('member', 'ref'):
            names.append(s['name'])
        elif s['t'] == 'call':
            names.append('()')
    return names


def iter_chains(node, out=None):
    """Every chain node inside an expression tree."""
    if out is None:
        out = []
    if isinstance(node, dict):
        if node.get('kind') == 'chain':
            out.append(node)
        for k, v in node.items():
            if k in ('kind', 'name', 'value', 'op'):
                continue
            iter_chains(v, out)
    elif isinstance(node, list):
        for v in node:
            iter_chains(v, out)
    return out


# --------------------------------------------------------- statements

def parse_stmt(toks, a, b):
    a, b = _trim(toks, a, b)
    if a >= b:
        return {'kind': 'empty'}
    first = toks[a].val
    if first in ('val', 'var'):
        i = a + 1
        name = toks[i].val if i < b and toks[i].kind == 'IDENT' else None
        typ = None
        if i + 1 < b and toks[i + 1].val == ':':
            j = i + 2
            while j < b and toks[j].val not in ('=', ';') and toks[j].kind != 'NL':
                j += 1
            typ = ''.join(t.val for t in toks[i + 2:j])
            i = j
        init = None
        while i < b and toks[i].val != '=':
            i += 1
        if i < b:
            init = (i + 1, b)
        return {'kind': 'val', 'name': name, 'type': typ, 'init': init,
                'range': (a, b)}
    if first == 'if':
        return _parse_if(toks, a, b)
    if first in ('while', 'for'):
        return _parse_loop(toks, a, b, first)
    if first in ('return', 'throw'):
        return {'kind': 'return', 'expr': (a + 1, b), 'range': (a, b)}
    if first == 'try':
        return _parse_try(toks, a, b)
    if first == 'when':
        return {'kind': 'when', 'range': (a, b)}
    if first in ('class', 'object', 'interface'):
        return {'kind': 'decl', 'range': (a, b)}
    if toks[a].val == '{':
        e = match(toks, a)
        return {'kind': 'block', 'range': (a + 1, e)}
    return {'kind': 'expr', 'expr': (a, b), 'range': (a, b)}


def _parse_if(toks, a, b):
    depth, p = 0, None
    for i in range(a + 1, b):
        if toks[i].val == '(':
            p = i
            break
    if p is None:
        return {'kind': 'opaque', 'range': (a, b)}
    e = match(toks, p)
    cond = (p + 1, e)
    then_a = _significant(toks, e + 1, 1, b)
    then_stmt, then_end = _parse_subbranch(toks, then_a, b)
    else_stmt = None
    k = _significant(toks, then_end, 1, b)
    if k < b and toks[k].val == 'else':
        s = _significant(toks, k + 1, 1, b)
        else_stmt, _ = _parse_subbranch(toks, s, b)
    return {'kind': 'if', 'cond': cond, 'then': then_stmt, 'else': else_stmt,
            'range': (a, b)}


def _parse_subbranch(toks, a, b):
    a = _significant(toks, a, 1, b)
    if a >= b:
        return {'kind': 'empty'}, b
    if toks[a].val == '{':
        e = match(toks, a)
        return {'kind': 'block', 'range': (a + 1, e)}, e + 1
    depth = 0
    for i in range(a, b):
        v = toks[i].val
        if v in '([{':
            depth += 1
        elif v in ')]}':
            depth -= 1
        elif depth == 0 and toks[i].kind == 'NL':
            return parse_stmt(toks, a, i), i
        elif depth == 0 and v == ';':
            return parse_stmt(toks, a, i), i
    return parse_stmt(toks, a, b), b


def _parse_loop(toks, a, b, kw):
    p = None
    for i in range(a + 1, b):
        if toks[i].val == '(':
            p = i
            break
    if p is None:
        return {'kind': 'opaque', 'range': (a, b)}
    e = match(toks, p)
    head = (p + 1, e)
    body, _ = _parse_subbranch(toks, e + 1, b)
    if kw == 'for':
        var, it = None, None
        depth = 0
        for i in range(head[0], head[1]):
            if toks[i].val == 'in' and depth == 0 and i > head[0]:
                var = toks[i - 1].val
                it = (i + 1, head[1])
                break
        return {'kind': 'for', 'var': var, 'iterable': it, 'body': body,
                'range': (a, b)}
    return {'kind': 'while', 'cond': head, 'body': body, 'range': (a, b)}


def _parse_try(toks, a, b):
    blocks = []
    i = a
    while i < b:
        if toks[i].val in ('try', 'catch', 'finally'):
            j = i + 1
            if j < b and toks[j].val == '(':
                j = match(toks, j) + 1
            j = _significant(toks, j, 1, b)
            if j < b and toks[j].val == '{':
                e = match(toks, j)
                blocks.append((j + 1, e))
                i = e + 1
                continue
        i += 1
    return {'kind': 'try', 'blocks': blocks, 'range': (a, b)}


def block_stmts(toks, a, b):
    return [parse_stmt(toks, x, y) for x, y in split_statements(toks, a, b)]


def walk_stmts(stmts, fn, env=None, ctx=None):
    """Depth-first walk carrying a variable environment and context dict."""
    env = {} if env is None else env
    ctx = {} if ctx is None else ctx
    for st in stmts:
        fn(st, env, ctx)


# ------------------------------------------------------------- functions

def functions(toks):
    out, i, n = [], 0, len(toks)
    while i < n:
        if toks[i].kind == 'IDENT' and toks[i].val == 'fun':
            j = i + 1
            if j < n and toks[j].val == '<':
                j = match(toks, j) + 1
            head, k = [], j
            while k < n and toks[k].val not in ('(', '{', '=', ';'):
                head.append(toks[k])
                k += 1
            if k >= n or toks[k].val != '(':
                i += 1
                continue
            close = match(toks, k)
            name, recv = None, None
            if head and head[-1].kind == 'IDENT':
                name = head[-1].val
            if len(head) >= 2 and head[-2].val == '.':
                recv = ''.join(t.val for t in head[:-2])
            params = _params(toks, k + 1, close)
            m = _significant(toks, close + 1, 1, n)
            # skip an optional `: ReturnType` clause before the body
            while m < n and toks[m].val not in ('{', '='):
                if toks[m].kind == 'NL':
                    nxt = _significant(toks, m, 1, n)
                    if nxt < n and toks[nxt].val in ('fun', 'val', 'var', 'class',
                                                     'object', 'interface', 'override',
                                                     'private', 'internal', 'protected',
                                                     'public', '@'):
                        m = nxt
                        break
                m += 1
            body = None
            if m < n and toks[m].val == '{':
                e = match(toks, m)
                body, endline = (m + 1, e), toks[e].line
            elif m < n and toks[m].val == '=':
                p = m + 1
                depth = 0
                while p < n:
                    v = toks[p].val
                    if v in '([{':
                        depth += 1
                    elif v in ')]}':
                        depth -= 1
                    elif depth == 0 and toks[p].kind == 'NL':
                        break
                    p += 1
                body, endline = (m + 1, p), toks[p - 1].line
            out.append({'name': name, 'receiver': recv, 'params': params,
                        'tokens': toks, 'body': body,
                        'start_line': toks[i].line, 'end_line': endline})
            i = close + 1
            continue
        i += 1
    return out


def _params(toks, a, b):
    out, start, depth = [], a, 0
    for i in range(a, b + 1):
        v = toks[i].val if i < b else ','
        if i < b and v in '([{':
            depth += 1
        elif i < b and v in ')]}':
            depth -= 1
        if v == ',' and depth == 0:
            seg = [t for t in toks[start:i] if t.kind != 'NL']
            if seg:
                name, typ = None, None
                colon = next((x for x in range(len(seg)) if seg[x].val == ':'), None)
                end = colon if colon is not None else next(
                    (x for x in range(len(seg)) if seg[x].val == '='), len(seg))
                for x in range(end - 1, -1, -1):
                    if seg[x].kind == 'IDENT' and seg[x].val not in _MODIFIERS:
                        name = seg[x].val
                        break
                if colon is not None:
                    depth, tsegs = 0, []
                    for t in seg[colon + 1:]:
                        if t.val in '([{<':
                            depth += 1
                        elif t.val in ')]}>':
                            depth -= 1
                        if depth == 0 and t.val == '=':
                            break
                        tsegs.append(t.val)
                    typ = ''.join(tsegs)
                out.append({'name': name, 'type': typ})
            start = i + 1
    return out


def find_function(toks, name, tests=None):
    """Functions with the given name; tests can filter by receiver/params."""
    fs = [f for f in functions(toks) if f['name'] == name and f['body']]
    if tests:
        fs = [f for f in fs if tests(f)]
    return fs


def function_body_stmts(fn):
    return block_stmts(fn['tokens'], fn['body'][0], fn['body'][1])


def class_primary_ctor_params(toks, class_name):
    """name -> type for the primary constructor of `class <name>(...)`."""
    for i, t in enumerate(toks):
        if t.kind == 'IDENT' and t.val == 'class':
            j = i + 1
            while j < len(toks) and toks[j].kind == 'NL':
                j += 1
            if j < len(toks) and toks[j].val == class_name:
                k = j + 1
                while k < len(toks) and toks[k].val not in ('(', '{'):
                    k += 1
                if k < len(toks) and toks[k].val == '(':
                    e = match(toks, k)
                    out = {}
                    for p in _params(toks, k + 1, e):
                        if p['name']:
                            out[p['name']] = p['type']
                    return out
    return None


def find_calls(toks, names):
    """All call chains whose receiver-call name is in `names`."""
    out = []
    for i, t in enumerate(toks):
        if t.kind == 'IDENT' and t.val in names:
            if i > 0 and toks[i - 1].val in ('.', '?.'):
                continue
            node, _ = _parse_postfix(toks, i, len(toks))
            out.append(node)
    return out


# -------------------------------------------------- Java condition text

_JTOK = re.compile(r'\s*(!==|!=|==|&&|\|\||[!()\.]|[A-Za-z_$][A-Za-z0-9_$]*|\d+)')


def _java_tokens(text):
    toks, i = [], 0
    while i < len(text):
        m = _JTOK.match(text, i)
        if not m:
            if text[i:].strip() == '':
                break
            i += 1
            continue
        toks.append(m.group(1))
        i = m.end()
    return toks


class _JavaCond:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, val=None):
        v = self.peek()
        if v is None or (val is not None and v != val):
            return None
        self.i += 1
        return v

    def parse(self):
        return self._or()

    def _or(self):
        node = self._and()
        while self.peek() == '||':
            self.take()
            node = {'k': 'or', 'l': node, 'r': self._and()}
        return node

    def _and(self):
        node = self._eq()
        while self.peek() == '&&':
            self.take()
            node = {'k': 'and', 'l': node, 'r': self._eq()}
        return node

    def _eq(self):
        node = self._unary()
        while self.peek() in ('==', '!='):
            op = self.take()
            node = {'k': 'cmp', 'op': op, 'l': node, 'r': self._unary()}
        return node

    def _unary(self):
        if self.peek() == '!':
            self.take()
            return {'k': 'not', 'e': self._unary()}
        if self.peek() == '(':
            # parenthesized sub-expression or cast-like grouping
            start = self.i
            self.take()
            node = self._or()
            if self.take(')'):
                return node
            self.i = start
        return self._path()

    def _path(self):
        segs = []
        if self.peek() is None:
            return {'k': 'unknown'}
        while True:
            v = self.take()
            if v is None:
                break
            if v == '(':
                continue
            segs.append(v)
            if self.peek() == '.':
                self.take()
                continue
            if self.peek() == '(':
                # call: consume args conservatively
                self.take()
                depth = 1
                args = []
                while self.peek() is not None and depth:
                    x = self.take()
                    if x == '(':
                        depth += 1
                    elif x == ')':
                        depth -= 1
                        if depth == 0:
                            break
                    args.append(x)
                return {'k': 'call', 'path': segs, 'args': args}
            break
        if len(segs) == 1 and segs[0].isdigit():
            return {'k': 'lit', 'v': segs[0]}
        return {'k': 'name', 'path': segs}


def parse_java_condition(text):
    t = _java_tokens(text)
    if not t:
        return {'k': 'unknown'}
    return _JavaCond(t).parse()


def eval_gate_expr(node, type_name, resolve_call):
    """Truth of a Java gate predicate for one enum constant (None = unknown)."""
    k = node.get('k')
    if k == 'or':
        l = eval_gate_expr(node['l'], type_name, resolve_call)
        r = eval_gate_expr(node['r'], type_name, resolve_call)
        if l is True or r is True:
            return True
        if l is None or r is None:
            return None
        return False
    if k == 'and':
        l = eval_gate_expr(node['l'], type_name, resolve_call)
        r = eval_gate_expr(node['r'], type_name, resolve_call)
        if l is False or r is False:
            return False
        if l is None or r is None:
            return None
        return True
    if k == 'not':
        v = eval_gate_expr(node['e'], type_name, resolve_call)
        return None if v is None else (not v)
    if k == 'cmp':
        l, r = node['l'], node['r']
        const = _const_of(r) or _const_of(l)
        if const is None:
            return None
        if node['op'] == '!=':
            return type_name != const
        return type_name == const
    if k == 'call':
        return resolve_call(node['path'], type_name)
    return None


def _const_of(node):
    if node.get('k') == 'name' and len(node['path']) >= 2:
        return node['path'][-1]
    return None


def java_switch_case_map(src, start_line, end_line):
    """Recover `switch` case labels -> returned literal from a method source range.

    JavaFactsDeep drops case labels; the labels decide which enum constants a
    predicate admits, so they are parsed structurally from the method's own
    source range (brace/statement aware), not by searching the file.
    """
    lines = src.splitlines()[start_line - 1:end_line]
    text = '\n'.join(lines)
    toks = tokenize_java_like(text)
    mapping, pending = {}, []
    i, n = 0, len(toks)
    in_switch = False
    depth = 0
    while i < n:
        v = toks[i]
        if v == 'switch':
            in_switch = True
            i += 1
            continue
        if in_switch:
            if v == '{':
                depth += 1
            elif v == '}':
                depth -= 1
                if depth <= 0:
                    in_switch = False
            elif v == 'case':
                j = i + 1
                lab = []
                while j < n and toks[j] != ':':
                    lab.append(toks[j])
                    j += 1
                if lab:
                    pending.append(lab[-1])
                i = j
            elif v == 'default':
                pending.append('default')
            elif v == 'return':
                val = toks[i + 1] if i + 1 < n else ''
                for p in pending:
                    mapping[p] = (val == 'true')
                pending = []
        i += 1
    return mapping


def tokenize_java_like(text):
    return [t for t in re.findall(r'[A-Za-z_$][A-Za-z0-9_$]*|true|false|[{}():;,]', text)]
