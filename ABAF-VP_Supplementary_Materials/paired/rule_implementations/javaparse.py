"""JDK17 AST fact extraction via the recovered compiler + JavaFacts.

Parse-only (no Android stubs needed). Facts are cached by source sha256 under
runs/javacache so identical inputs never re-run (run-budget rule).
"""
import hashlib, json, pathlib, subprocess, time

ROOT = pathlib.Path(__file__).resolve().parents[4]
WS = ROOT / 'ABAF_VP_完整实验方案_2026-10-11/workspace'
JDK = WS / 'tools/jdk-17.0.20.1+1/Contents/Home'
JAVAFACTS_DEEP = pathlib.Path(__file__).resolve().parent / 'JavaFactsDeep.java'
V5 = pathlib.Path(__file__).resolve().parents[1]
CACHE = V5 / 'runs/javacache'
RUNLOG = V5 / 'runs/javacache/invocations.jsonl'


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def _ensure_classes():
    classes = CACHE / 'classes5'
    marker = classes / 'JavaFactsDeep.class'
    src_sha = sha(JAVAFACTS_DEEP)
    if marker.exists() and (CACHE / 'classes5.src.sha').read_text() == src_sha:
        return classes
    classes.mkdir(parents=True, exist_ok=True)
    res = subprocess.run([str(JDK / 'bin/javac'), '-d', str(classes), str(JAVAFACTS_DEEP)],
                         capture_output=True, text=True, timeout=120)
    assert res.returncode == 0, res.stderr
    (CACHE / 'classes5.src.sha').write_text(src_sha)
    return classes


def facts_for(path, receipt=None):
    """Return parsed JavaFacts object for a source file (AST-first; cached by sha)."""
    p = pathlib.Path(path)
    h = sha(p)
    cf = CACHE / f'{h}.json'
    if cf.exists():
        return json.loads(cf.read_text())
    classes = _ensure_classes()
    listfile = CACHE / f'_batch_{h}.txt'
    listfile.write_text(str(p) + '\n')
    start = time.perf_counter()
    res = subprocess.run([str(JDK / 'bin/java'), '-cp', str(classes), 'JavaFactsDeep', str(listfile)],
                         capture_output=True, text=True, timeout=300)
    dur = time.perf_counter() - start
    listfile.unlink()
    assert res.returncode == 0, res.stderr[:500]
    line = [l for l in res.stdout.splitlines() if l.strip()][0]
    obj = json.loads(line)
    obj['_source_sha256'] = h
    obj['_duration_s'] = dur
    cf.write_text(json.dumps(obj))
    with RUNLOG.open('a') as f:
        f.write(json.dumps({'command': [str(JDK / 'bin/java'), '-cp', str(classes), 'JavaFactsDeep', '<file>'],
                            'file': str(p), 'sha256': h, 'exit_code': res.returncode,
                            'duration_s': dur, 'parse_ok': obj.get('parse_ok')}) + '\n')
    return obj


def method_facts(javafacts, name):
    """All method objects with the given simple name."""
    return [m for m in javafacts.get('methods', []) if m['name'] == name]


def select_method(javafacts, name):
    """Unique method with body, else None."""
    ms = [m for m in method_facts(javafacts, name) if m.get('has_body')]
    return ms[0] if len(ms) == 1 else None
