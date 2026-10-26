"""C3 structural helpers: comment/string-aware brace matching for declaration-level facts.

Java method bodies and control flow come from javaparse.facts_for (JDK17 AST,
JavaFactsDeep). JavaFactsDeep does not serialise class-level fields, anonymous-class
spans or Kotlin declarations, so this module supplies exactly those facts:

  * blank_comments_strings  - same-length copy with comments/strings blanked, so brace
                              matching can never be confused by braces in literals.
  * match_brace / TypeSpans - nested class/interface/enum body spans.
  * field_decls / field_decl- class-level field declarations with literal initialisers
                              (method line ranges from the AST are excluded).
  * anonymous_span          - `field = new X() { ... }` body span, so an anonymous
                              listener's callbacks can be mapped back to its field.
  * find_functions          - Kotlin `fun` declarations with param types and body spans
                              (no Kotlin compiler is available offline; spans and params
                              are brace/paren matched, not matched on raw text).

Regex here only *locates* candidate declarations; every span, nesting decision and
enclosing-scope decision comes from bracket matching of the blanked source.
"""
import bisect
import re

MODIFIERS = {'public', 'private', 'protected', 'static', 'final', 'volatile', 'transient',
             'synchronized', 'internal', 'const', 'lateinit', 'override', 'open', 'abstract'}


def blank_comments_strings(text):
    """Return a same-length copy with // /* */ "..." '...' \"\"\"...\"\"\" blanked.

    Newlines and offsets are preserved so line numbers and slices stay valid.
    """
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '/' and i + 1 < n and text[i + 1] == '/':
            j = text.find('\n', i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = ' '
            i = j
        elif c == '/' and i + 1 < n and text[i + 1] == '*':
            j = text.find('*/', i + 2)
            j = n if j < 0 else j + 2
            for k in range(i, j):
                if text[k] != '\n':
                    out[k] = ' '
            i = j
        elif text.startswith('"""', i):
            j = text.find('"""', i + 3)
            j = n if j < 0 else j + 3
            for k in range(i, j):
                if text[k] != '\n':
                    out[k] = ' '
            i = j
        elif c in '"\'':
            q = c
            j = i + 1
            while j < n:
                if text[j] == '\\':
                    j += 2
                    continue
                if text[j] == q:
                    j += 1
                    break
                if text[j] == '\n':
                    break
                j += 1
            for k in range(i, min(j, n)):
                if text[k] != '\n':
                    out[k] = ' '
            i = j
        else:
            i += 1
    return ''.join(out)


def match_brace(s, i):
    """Index of the '}' matching the '{' at i, or -1."""
    if i >= len(s) or s[i] != '{':
        return -1
    depth = 0
    for j in range(i, len(s)):
        if s[j] == '{':
            depth += 1
        elif s[j] == '}':
            depth -= 1
            if depth == 0:
                return j
    return -1


def match_paren(s, i):
    if i >= len(s) or s[i] != '(':
        return -1
    depth = 0
    for j in range(i, len(s)):
        if s[j] == '(':
            depth += 1
        elif s[j] == ')':
            depth -= 1
            if depth == 0:
                return j
    return -1


class LineIndex:
    def __init__(self, s):
        self.starts = [0]
        self.starts += [m.end() for m in re.finditer('\n', s)]

    def line_of(self, off):
        return bisect.bisect_right(self.starts, off)

    def offset_of(self, line):
        return self.starts[line - 1] if 1 <= line <= len(self.starts) else None


TYPE_RE = re.compile(r'\b(class|interface|enum)\s+([A-Za-z_$][\w$]*)')


def type_spans(blank):
    """Nested class/interface/enum spans. `body_open`/`end` are brace offsets."""
    spans = []
    for m in TYPE_RE.finditer(blank):
        j = m.end()
        depth = 0
        ok = True
        while j < len(blank):
            ch = blank[j]
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth -= 1
            elif ch == '{' and depth == 0:
                break
            elif ch in ';}' and depth == 0:
                ok = False
                break
            j += 1
        if not ok or j >= len(blank):
            continue
        end = match_brace(blank, j)
        if end < 0:
            continue
        spans.append({'kind': m.group(1), 'name': m.group(2), 'start': m.start(),
                      'name_start': m.start(2), 'body_open': j, 'end': end})
    return spans


def enclosing_type(spans, off):
    best = None
    for sp in spans:
        if sp['body_open'] < off < sp['end']:
            if best is None or sp['body_open'] > best['body_open']:
                best = sp
    return best


def type_depth(blank, body_open, off):
    """Brace depth of `off` relative to the type body opened at body_open."""
    depth = 0
    for k in range(body_open + 1, off):
        if blank[k] == '{':
            depth += 1
        elif blank[k] == '}':
            depth -= 1
    return depth


def parse_field_line(line):
    """Split a class-level `mods Type name = init` line. Returns None if not a field."""
    if '=' not in line:
        return None
    left, right = line.split('=', 1)
    left = left.strip()
    if not left or left.endswith(('.', ',', '(')):
        return None
    name_m = re.search(r'([A-Za-z_$][\w$]*)\s*$', left)
    if not name_m:
        return None
    pre = left[:name_m.start()].strip()
    toks = pre.split()
    while toks and toks[0] in MODIFIERS:
        toks.pop(0)
    if not toks:
        return None
    return {'name': name_m.group(1), 'type': ' '.join(toks), 'init': right.strip().rstrip(';').strip(),
            'raw': line.strip()}


def field_decls(blank, method_lines):
    """Class-level fields keyed by name. `method_lines` = [(start_line, end_line)] from AST."""
    out = {}
    for idx, line in enumerate(blank.split('\n'), start=1):
        if any(a <= idx <= b for a, b in method_lines):
            continue
        d = parse_field_line(line)
        if d and d['type'] and not d['type'].startswith(('return', 'else', 'case')):
            d['line'] = idx
            out.setdefault(d['name'], d)
    return out


def anonymous_span(blank, field_name):
    """Span of `field_name = new X(...) { ... }` (anonymous class body), else None."""
    m = re.search(r'\b' + re.escape(field_name) + r'\s*=\s*new\s+([\w.$]+)\s*\(', blank)
    if not m:
        return None
    pclose = match_paren(blank, m.end() - 1)
    if pclose < 0:
        return None
    k = pclose + 1
    while k < len(blank) and blank[k] in ' \t\r\n':
        k += 1
    if k >= len(blank) or blank[k] != '{':
        return None
    end = match_brace(blank, k)
    if end < 0:
        return None
    return {'type': m.group(1), 'start': m.start(), 'body_open': k, 'end': end}


FUN_RE = re.compile(r'\bfun\s+([A-Za-z_$][\w$]*)\s*\(')


def split_params(params_raw):
    """`a: A, b: B = x` -> [{'name','type'}] (Kotlin)."""
    parts, depth, cur = [], 0, ''
    for ch in params_raw:
        if ch in '(<[':
            depth += 1
        elif ch in ')>]':
            depth -= 1
        if ch == ',' and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    out = []
    for p in parts:
        p = p.split('=')[0].strip()
        if ':' not in p:
            continue
        name, typ = p.split(':', 1)
        out.append({'name': name.strip(), 'type': typ.strip()})
    return out


def find_functions(blank, start, end):
    """Function declarations inside [start,end) at any nesting; body spans brace matched."""
    out = []
    for m in FUN_RE.finditer(blank, start, end):
        popen = m.end() - 1
        pclose = match_paren(blank, popen)
        if pclose < 0 or pclose > end:
            continue
        params_raw = blank[popen + 1:pclose].strip()
        k = pclose + 1
        while k < end and blank[k] in ' \t\r\n':
            k += 1
        if k < end and blank[k] == ':':
            while k < end and blank[k] not in '{=':
                k += 1
        if k < end and blank[k] == '{':
            bend = match_brace(blank, k)
            if bend < 0:
                continue
            rec = {'name': m.group(1), 'params': split_params(params_raw),
                   'params_raw': params_raw, 'start': m.start(), 'body_open': k, 'end': bend}
        elif k < end and blank[k] == '=':
            line_end = blank.find('\n', k)
            line_end = end if line_end < 0 else min(line_end, end)
            rec = {'name': m.group(1), 'params': split_params(params_raw),
                   'params_raw': params_raw, 'start': m.start(), 'body_open': k,
                   'end': line_end, 'expression_body': True}
        else:
            continue
        out.append(rec)
    return out


def locate_line(blank, pattern, line_lo, line_hi):
    """1-based line of the first regex match inside [line_lo,line_hi], else None.

    Location aid only: it points an auditor at the source text of a decision that
    was taken from the AST/structure, it never decides anything by itself.
    """
    li = LineIndex(blank)
    lo = li.offset_of(line_lo) or 0
    hi = li.offset_of(line_hi + 1) or len(blank)
    m = re.search(pattern, blank[lo:hi])
    return li.line_of(lo + m.start()) if m else None


CALL_RE = re.compile(r'([A-Za-z_$][\w$]*(?:\s*\.\s*[A-Za-z_$][\w$]*)*)\s*\(')


def calls(blank, start, end):
    """Call sites in [start,end): receiver chain, call name, raw args, offset."""
    out = []
    for m in CALL_RE.finditer(blank, start, end):
        chain = re.sub(r'\s+', '', m.group(1))
        popen = m.end() - 1
        pclose = match_paren(blank, popen)
        if pclose < 0:
            continue
        segs = chain.split('.')
        out.append({'chain': chain, 'receiver': '.'.join(segs[:-1]), 'name': segs[-1],
                    'args_raw': blank[popen + 1:pclose].strip(), 'offset': m.start(),
                    'args': [a.strip() for a in split_top_level(blank[popen + 1:pclose])]})
    return out


def split_top_level(s):
    parts, depth, cur = [], 0, ''
    for ch in s:
        if ch in '(<[':
            depth += 1
        elif ch in ')>]':
            depth -= 1
        if ch == ',' and depth == 0:
            parts.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return parts
