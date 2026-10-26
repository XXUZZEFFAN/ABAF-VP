"""C2 rule-family helpers: Kotlin PSI facts + AST walking utilities.

Kotlin has no JDK AST. We reuse the Kotlin compiler PSI that ships inside the
already-installed detekt fat jar (tools/detekt-cli-1.23.8-all.jar) instead of
regex: KotlinFacts serialises declarations/calls/branches, cached by source
sha256 under runs/C2/ktcache/ (same run-budget rule as javaparse).

Java sources go through javaparse.facts_for (JavaFactsDeep).
"""
import hashlib
import json
import pathlib
import subprocess
import time

ROOT = pathlib.Path(__file__).resolve().parents[4]
WS = ROOT / 'ABAF_VP_完整实验方案_2026-10-11/workspace'
JDK = WS / 'tools/jdk-17.0.20.1+1/Contents/Home'
DETEKT = WS / 'tools/detekt-cli-1.23.8-all.jar'
V5 = pathlib.Path(__file__).resolve().parents[1]
KTCACHE = V5 / 'runs/C2/ktcache'
KTLOG = KTCACHE / 'invocations.jsonl'

KOTLIN_FACTS_JAVA = r'''
import org.jetbrains.kotlin.com.intellij.openapi.Disposable;
import org.jetbrains.kotlin.com.intellij.openapi.util.Disposer;
import org.jetbrains.kotlin.com.intellij.psi.PsiFile;
import org.jetbrains.kotlin.com.intellij.psi.PsiFileFactory;
import org.jetbrains.kotlin.cli.jvm.compiler.KotlinCoreEnvironment;
import org.jetbrains.kotlin.cli.jvm.compiler.EnvironmentConfigFiles;
import org.jetbrains.kotlin.config.CompilerConfiguration;
import org.jetbrains.kotlin.idea.KotlinLanguage;
import org.jetbrains.kotlin.psi.*;
import java.io.File;
import java.nio.file.*;
import java.util.*;

/** Parse-only Kotlin PSI serialiser (no resolution, no execution). */
public class KotlinFacts {
  static String q(String s) {
    if (s == null) return "null";
    StringBuilder b = new StringBuilder();
    b.append('"');
    for (int i = 0; i < s.length(); i++) {
      char c = s.charAt(i);
      if (c == '"') b.append("\\\"");
      else if (c == '\\') b.append("\\\\");
      else if (c == '\n') b.append("\\n");
      else if (c == '\r') b.append("\\r");
      else if (c == '\t') b.append("\\t");
      else if (c < 0x20) b.append(' ');
      else b.append(c);
    }
    return b.append('"').toString();
  }
  static String trunc(String s, int n) {
    if (s == null) return "";
    s = s.trim();
    return s.length() <= n ? s : s.substring(0, n) + "...";
  }
  static String obj(String... kv) {
    StringBuilder b = new StringBuilder("{");
    for (int i = 0; i < kv.length; i += 2) {
      if (i > 0) b.append(',');
      b.append(q(kv[i])).append(':').append(kv[i + 1]);
    }
    return b.append('}').toString();
  }
  static String arr(List<String> xs) { return "[" + String.join(",", xs) + "]"; }
  static int lineOf(String src, int off) {
    if (off <= 0) return 1;
    int line = 1, n = Math.min(off, src.length());
    for (int i = 0; i < n; i++) if (src.charAt(i) == '\n') line++;
    return line;
  }
  static String text(KtExpression e) { return e == null ? "" : trunc(e.getText(), 220); }

  static String stmts(KtBlockExpression b, String src) {
    List<String> out = new ArrayList<>();
    if (b != null) for (KtExpression s : b.getStatements()) out.add(node(s, src));
    return arr(out);
  }
  static String body(KtExpression e, String src) {
    if (e == null) return "null";
    if (e instanceof KtBlockExpression b) return obj("kind", q("BLOCK"), "stmts", stmts(b, src));
    return node(e, src);
  }
  static String call(KtCallExpression c, String explicitRecv, String src) {
    KtExpression callee = c.getCalleeExpression();
    String name = "", recv = explicitRecv == null ? "" : explicitRecv;
    if (callee instanceof KtNameReferenceExpression) name = ((KtNameReferenceExpression) callee).getReferencedName();
    else if (callee instanceof KtDotQualifiedExpression) {
      KtDotQualifiedExpression d = (KtDotQualifiedExpression) callee;
      if (d.getSelectorExpression() instanceof KtNameReferenceExpression)
        name = ((KtNameReferenceExpression) d.getSelectorExpression()).getReferencedName();
      if (explicitRecv == null) recv = text(d.getReceiverExpression());
    }
    List<String> args = new ArrayList<>();
    for (KtValueArgument a : c.getValueArguments()) {
      if (a instanceof KtLambdaArgument) continue;                            // captured as lambda
      if (a.getArgumentExpression() instanceof KtLambdaExpression) continue;  // captured as lambda
      args.add(obj("text", q(trunc(a.getText(), 200)), "expr", node(a.getArgumentExpression(), src)));
    }
    String lam = "null";
    for (KtLambdaArgument la : c.getLambdaArguments()) {
      if (la.getLambdaExpression() != null) lam = body(la.getLambdaExpression().getBodyExpression(), src);
    }
    if (lam.equals("null")) {
      for (KtValueArgument a : c.getValueArguments()) {
        if (a.getArgumentExpression() instanceof KtLambdaExpression) {
          lam = body(((KtLambdaExpression) a.getArgumentExpression()).getBodyExpression(), src);
          break;
        }
      }
    }
    return obj("kind", q("CALL"), "name", q(name), "receiver", q(recv),
               "callee", q(callee == null ? "" : trunc(callee.getText(), 220)),
               "args", arr(args), "lambda", lam, "line", String.valueOf(lineOf(src, c.getTextOffset())));
  }
  static String node(KtExpression e, String src) {
    if (e == null) return "null";
    if (e instanceof KtCallExpression) return call((KtCallExpression) e, null, src);
    if (e instanceof KtDotQualifiedExpression) {
      KtDotQualifiedExpression d = (KtDotQualifiedExpression) e;
      if (d.getSelectorExpression() instanceof KtCallExpression)
        return call((KtCallExpression) d.getSelectorExpression(), text(d.getReceiverExpression()), src);
      return obj("kind", q("DOT"), "receiver", node(d.getReceiverExpression(), src),
                 "selector", node(d.getSelectorExpression(), src), "text", q(text(d)));
    }
    if (e instanceof KtSafeQualifiedExpression) {
      KtSafeQualifiedExpression d = (KtSafeQualifiedExpression) e;
      if (d.getSelectorExpression() instanceof KtCallExpression)
        return call((KtCallExpression) d.getSelectorExpression(),
                    text(d.getReceiverExpression()) + "?", src);
      return obj("kind", q("SAFE_DOT"), "receiver", node(d.getReceiverExpression(), src),
                 "selector", node(d.getSelectorExpression(), src), "text", q(text(d)));
    }
    if (e instanceof KtBinaryExpressionWithTypeRHS) {
      KtBinaryExpressionWithTypeRHS c = (KtBinaryExpressionWithTypeRHS) e;
      return obj("kind", q("CAST"), "op", q(c.getOperationReference().getText()),
                 "expr", node(c.getLeft(), src),
                 "type", q(c.getRight() == null ? "" : c.getRight().getText()));
    }
    if (e instanceof KtNameReferenceExpression) return obj("kind", q("NAME"), "name", q(((KtNameReferenceExpression) e).getReferencedName()));
    if (e instanceof KtParenthesizedExpression) return node(((KtParenthesizedExpression) e).getExpression(), src);
    if (e instanceof KtBinaryExpression) {
      KtBinaryExpression b = (KtBinaryExpression) e;
      return obj("kind", q("BIN"), "op", q(b.getOperationReference().getText()),
                 "left", node(b.getLeft(), src), "right", node(b.getRight(), src), "text", q(text(b)));
    }
    if (e instanceof KtReturnExpression) return obj("kind", q("RETURN"), "expr", node(((KtReturnExpression) e).getReturnedExpression(), src));
    if (e instanceof KtIfExpression) {
      KtIfExpression i = (KtIfExpression) e;
      return obj("kind", q("IF"), "cond", node(i.getCondition(), src),
                 "then", body(i.getThen(), src), "else", body(i.getElse(), src),
                 "line", String.valueOf(lineOf(src, e.getTextOffset())));
    }
    if (e instanceof KtBlockExpression) return obj("kind", q("BLOCK"), "stmts", stmts((KtBlockExpression) e, src));
    if (e instanceof KtWhenExpression) {
      KtWhenExpression w = (KtWhenExpression) e;
      List<String> entries = new ArrayList<>();
      for (KtWhenEntry en : w.getEntries()) {
        List<String> conds = new ArrayList<>();
        for (KtWhenCondition c : en.getConditions()) conds.add(q(trunc(c.getText(), 160)));
        entries.add(obj("conds", arr(conds), "body", body(en.getExpression(), src)));
      }
      return obj("kind", q("WHEN"), "subject", node(w.getSubjectExpression(), src), "entries", arr(entries));
    }
    if (e instanceof KtTryExpression) {
      KtTryExpression t = (KtTryExpression) e;
      List<String> cs = new ArrayList<>();
      for (KtCatchClause c : t.getCatchClauses()) {
        KtParameter p = c.getCatchParameter();
        cs.add(obj("param", q(p == null ? "" : p.getText()), "body", body(c.getCatchBody(), src)));
      }
      return obj("kind", q("TRY"), "body", body(t.getTryBlock(), src), "catches", arr(cs),
                 "finally", body(t.getFinallyBlock() == null ? null : t.getFinallyBlock().getFinalExpression(), src));
    }
    if (e instanceof KtForExpression) {
      KtForExpression f = (KtForExpression) e;
      return obj("kind", q("LOOP"), "for", q(text(f.getLoopRange())), "body", body(f.getBody(), src));
    }
    if (e instanceof KtWhileExpression) {
      KtWhileExpression w = (KtWhileExpression) e;
      return obj("kind", q("LOOP"), "cond", node(w.getCondition(), src), "body", body(w.getBody(), src));
    }
    if (e instanceof KtDoWhileExpression) {
      KtDoWhileExpression w = (KtDoWhileExpression) e;
      return obj("kind", q("LOOP"), "cond", node(w.getCondition(), src), "body", body(w.getBody(), src));
    }
    if (e instanceof KtStringTemplateExpression) return obj("kind", q("STR"), "value", q(trunc(e.getText(), 200)));
    if (e instanceof KtConstantExpression) return obj("kind", q("LIT"), "value", q(e.getText()));
    if (e instanceof KtLambdaExpression) return obj("kind", q("LAMBDA"), "body", body(((KtLambdaExpression) e).getBodyExpression(), src));
    if (e instanceof KtProperty) {
      KtProperty p = (KtProperty) e;
      return obj("kind", q("VAR"), "name", q(p.getName() == null ? "" : p.getName()),
                 "type", q(p.getTypeReference() == null ? "" : p.getTypeReference().getText()),
                 "init", node(p.getInitializer(), src));
    }
    if (e instanceof KtThrowExpression) return obj("kind", q("THROW"), "expr", node(((KtThrowExpression) e).getThrownExpression(), src));
    if (e instanceof KtThisExpression) return obj("kind", q("THIS"), "text", q(text(e)));
    if (e instanceof KtUnaryExpression) {
      KtUnaryExpression u = (KtUnaryExpression) e;
      return obj("kind", q("UNARY"), "op", q(u.getOperationReference().getText()), "expr", node(u.getBaseExpression(), src));
    }
    if (e instanceof KtIsExpression) return obj("kind", q("IS"), "text", q(text(e)));
    if (e instanceof KtObjectLiteralExpression) {
      List<String> mem = new ArrayList<>();
      for (KtDeclaration d : ((KtObjectLiteralExpression) e).getObjectDeclaration().getDeclarations())
        mem.add(decl(d, src));
      return obj("kind", q("OBJ_LITERAL"), "members", arr(mem));
    }
    if (e instanceof KtCollectionLiteralExpression) {
      List<String> xs = new ArrayList<>();
      for (KtExpression x : ((KtCollectionLiteralExpression) e).getInnerExpressions()) xs.add(node(x, src));
      return obj("kind", q("COLLECTION"), "items", arr(xs));
    }
    if (e instanceof KtArrayAccessExpression) return obj("kind", q("INDEX"), "text", q(text(e)));
    return obj("kind", q("TEXT"), "text", q(text(e)), "cls", q(e.getClass().getSimpleName()));
  }
  static String decl(KtDeclaration d, String src) {
    if (d instanceof KtNamedFunction) {
      KtNamedFunction f = (KtNamedFunction) d;
      List<String> ps = new ArrayList<>();
      for (KtParameter p : f.getValueParameters())
        ps.add(obj("name", q(p.getName() == null ? "" : p.getName()),
                   "type", q(p.getTypeReference() == null ? "" : p.getTypeReference().getText())));
      return obj("kind", q("FUN"), "name", q(f.getName() == null ? "" : f.getName()),
                 "receiverType", q(f.getReceiverTypeReference() == null ? "" : f.getReceiverTypeReference().getText().trim()),
                 "params", arr(ps),
                 "returnType", q(f.getTypeReference() == null ? "" : f.getTypeReference().getText()),
                 "body", body(f.getBodyExpression(), src),
                 "line", String.valueOf(lineOf(src, f.getTextOffset())));
    }
    if (d instanceof KtClassOrObject) {
      KtClassOrObject c = (KtClassOrObject) d;
      List<String> supers = new ArrayList<>();
      for (KtSuperTypeListEntry s : c.getSuperTypeListEntries()) supers.add(q(trunc(s.getText(), 120)));
      List<String> mem = new ArrayList<>();
      for (KtDeclaration m : c.getDeclarations()) mem.add(decl(m, src));
      return obj("kind", q(c instanceof KtObjectDeclaration ? "OBJECT" : "CLASS"),
                 "name", q(c.getName() == null ? "" : c.getName()),
                 "supers", arr(supers), "members", arr(mem),
                 "line", String.valueOf(lineOf(src, c.getTextOffset())));
    }
    if (d instanceof KtProperty) {
      KtProperty p = (KtProperty) d;
      return obj("kind", q("PROP"), "name", q(p.getName() == null ? "" : p.getName()),
                 "type", q(p.getTypeReference() == null ? "" : p.getTypeReference().getText()),
                 "init", node(p.getInitializer(), src), "mutable", String.valueOf(p.isVar()));
    }
    return obj("kind", q("OTHER_DECL"), "text", q(text((KtExpression) null)));
  }
  public static void main(String[] args) throws Exception {
    Disposable disposable = Disposer.newDisposable();
    CompilerConfiguration cfg = new CompilerConfiguration();
    KotlinCoreEnvironment env = KotlinCoreEnvironment.createForProduction(
        disposable, cfg, EnvironmentConfigFiles.JVM_CONFIG_FILES);
    PsiFileFactory pff = PsiFileFactory.getInstance(env.getProject());
    List<String> lines = Files.readAllLines(Paths.get(args[0]));
    for (String path : lines) {
      if (path.trim().isEmpty()) continue;
      try {
        String src = new String(Files.readAllBytes(Paths.get(path)), java.nio.charset.StandardCharsets.UTF_8);
        PsiFile pf = pff.createFileFromText(new File(path).getName(), KotlinLanguage.INSTANCE, src);
        List<String> decls = new ArrayList<>();
        for (KtDeclaration d : ((KtFile) pf).getDeclarations()) decls.add(decl(d, src));
        System.out.println(obj("path", q(path), "parse_ok", "true",
            "package", q(((KtFile) pf).getPackageFqName().asString()),
            "declarations", arr(decls), "parser", q("kotlin.psi.detekt.v5")));
      } catch (Throwable t) {
        System.out.println(obj("path", q(path), "parse_ok", "false", "error", q(String.valueOf(t)),
                               "declarations", "[]", "parser", q("kotlin.psi.detekt.v5")));
      }
    }
    Disposer.dispose(disposable);
  }
}
'''


def sha(p):
    return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()


def _ensure_kt_classes():
    classes = KTCACHE / 'classes'
    marker = classes / 'KotlinFacts.class'
    src = KTCACHE / 'KotlinFacts.java'
    want = hashlib.sha256((KOTLIN_FACTS_JAVA + sha(DETEKT)).encode()).hexdigest()
    stamp = KTCACHE / 'classes.src.sha'
    if marker.exists() and stamp.exists() and stamp.read_text() == want:
        return classes
    KTCACHE.mkdir(parents=True, exist_ok=True)
    src.write_text(KOTLIN_FACTS_JAVA)
    classes.mkdir(parents=True, exist_ok=True)
    res = subprocess.run([str(JDK / 'bin/javac'), '-cp', str(DETEKT), '-d', str(classes), str(src)],
                         capture_output=True, text=True, timeout=300)
    assert res.returncode == 0, res.stderr[:2000]
    stamp.write_text(want)
    return classes


def _parser_tag():
    return hashlib.sha256((KOTLIN_FACTS_JAVA + sha(DETEKT)).encode()).hexdigest()[:12]


def kt_facts_for(path):
    """Parse a .kt file to Kotlin PSI facts (cached by source sha256 + parser tag)."""
    p = pathlib.Path(path)
    h = sha(p)
    tag = _parser_tag()
    cf = KTCACHE / f'{h}.{tag}.json'
    if cf.exists():
        return json.loads(cf.read_text())
    classes = _ensure_kt_classes()
    listfile = KTCACHE / f'_batch_{h}.txt'
    listfile.write_text(str(p) + '\n')
    start = time.perf_counter()
    res = subprocess.run([str(JDK / 'bin/java'), '-cp', f'{DETEKT}:{classes}', 'KotlinFacts', str(listfile)],
                         capture_output=True, text=True, timeout=300)
    dur = time.perf_counter() - start
    listfile.unlink()
    if res.returncode != 0:
        raise RuntimeError('KOTLIN_PSI_FAILED:' + res.stderr[:400])
    line = [l for l in res.stdout.splitlines() if l.strip()][0]
    obj = json.loads(line)
    obj['_source_sha256'] = h
    obj['_duration_s'] = dur
    cf.write_text(json.dumps(obj))
    with KTLOG.open('a') as f:
        f.write(json.dumps({'command': [str(JDK / 'bin/java'), '-cp', '<detekt+classes>', 'KotlinFacts', '<file>'],
                            'file': str(p), 'sha256': h, 'exit_code': res.returncode,
                            'duration_s': round(dur, 4), 'parse_ok': obj.get('parse_ok')}) + '\n')
    return obj


def java_facts_for(path):
    """Same JavaFactsDeep parse as javaparse.facts_for, but tolerant of raw control
    characters inside string literals (e.g. the NUL literal in FairEmail Helper.java).
    Shares runs/javacache so identical inputs are never re-parsed."""
    import javaparse as jp
    p = pathlib.Path(path)
    h = hashlib.sha256(p.read_bytes()).hexdigest()
    cf = jp.CACHE / f'{h}.json'
    if cf.exists():
        return json.loads(cf.read_text(), strict=False)
    classes = jp._ensure_classes()
    listfile = jp.CACHE / f'_batch_{h}.txt'
    listfile.write_text(str(p) + '\n')
    start = time.perf_counter()
    res = subprocess.run([str(jp.JDK / 'bin/java'), '-cp', str(classes), 'JavaFactsDeep', str(listfile)],
                         capture_output=True, text=True, timeout=300)
    dur = time.perf_counter() - start
    listfile.unlink()
    assert res.returncode == 0, res.stderr[:500]
    line = [l for l in res.stdout.splitlines() if l.strip()][0]
    obj = json.loads(line, strict=False)
    obj['_source_sha256'] = h
    obj['_duration_s'] = dur
    cf.write_text(json.dumps(obj))
    with jp.RUNLOG.open('a') as f:
        f.write(json.dumps({'command': [str(jp.JDK / 'bin/java'), '-cp', str(classes), 'JavaFactsDeep', '<file>'],
                            'file': str(p), 'sha256': h, 'exit_code': res.returncode,
                            'duration_s': dur, 'parse_ok': obj.get('parse_ok')}) + '\n')
    return obj


# ---------------------------------------------------------------- AST walking

def iter_nodes(node):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from iter_nodes(v)
    elif isinstance(node, list):
        for v in node:
            yield from iter_nodes(v)


def calls_in(node):
    return [n for n in iter_nodes(node) if n.get('kind') == 'CALL']


def call_args(call):
    return [a.get('text', '') for a in (call.get('args') or [])]


def walk_with_path(node, path=None):
    """Yield (node, ancestors) for every dict node, ancestors outermost-first."""
    if path is None:
        path = []
    if isinstance(node, dict):
        yield node, list(path)
        path.append(node)
        for v in node.values():
            yield from walk_with_path(v, path)
        path.pop()
    elif isinstance(node, list):
        path.append(node)
        for v in node:
            yield from walk_with_path(v, path)
        path.pop()


def functions_index(facts_list):
    """Index Kotlin functions by (class, name), (receiverType, name) and (None, name)."""
    idx = {}

    def add(key, fn):
        idx.setdefault(key, []).append(fn)

    def walk_decls(decls, cls):
        for d in decls:
            if d.get('kind') == 'FUN':
                add((cls, d['name']), d)
                if d.get('receiverType'):
                    add((d['receiverType'], d['name']), d)
                add((None, d['name']), d)
            elif d.get('kind') in ('CLASS', 'OBJECT'):
                walk_decls(d.get('members') or [], d.get('name') or '')

    for f in facts_list:
        walk_decls(f.get('declarations') or [], None)
    return idx


def resolve_function(idx, name, receiver=''):
    """Resolve a call to a declared function: class-qualified, then receiver-type
    (extension), then unique top-level name. Ambiguity returns None."""
    receiver = (receiver or '').strip()
    if receiver:
        cand = idx.get((receiver, name)) or []
        if len(cand) == 1:
            return cand[0]
        short = receiver.split('.')[-1].rstrip('()').strip()
        cand = idx.get((short, name)) or []
        if len(cand) == 1:
            return cand[0]
    cand = idx.get((None, name)) or []
    if len(cand) == 1:
        return cand[0]
    return None
