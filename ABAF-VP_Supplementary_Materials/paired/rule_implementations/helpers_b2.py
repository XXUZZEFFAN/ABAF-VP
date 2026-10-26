"""B2 family driver: counterexamples, actual double-side runs, scoring.

Subcommands (all writes stay inside this family's owned paths):
  counterexamples  -> runs/B2/counterexample_src/, checks/B2_counterexamples.json
  retest           -> runs/B2/<FP>-<side>.json                      (one receipt per side)
  score            -> data/alignment_fragments/B2.csv, progress/B2_report.json
                      (scoring is the only step that reads reference states)

Checkers never receive expected answers: `run_counterexamples` compares the returned
observation with the expected class only after verify() returns, and `retest` writes
receipts before `score` opens target_contracts.jsonl.
"""
import csv
import hashlib
import json
import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import rules_b2

V5 = pathlib.Path(__file__).resolve().parents[1]
VERS = V5.parent
ROOT = V5.parents[2]
WS = ROOT / 'ABAF_VP_完整实验方案_2026-10-11/workspace'
SNAP = WS / 'p2_pair_selection/snapshots'
CONTRACTS = VERS / 'exp3_paired_validation_v1/data/target_contracts.jsonl'
V3 = VERS / 'exp3_paired_validation_v3/analysis/pair_results.csv'
RULE_VERSION = 'v5.rule.b2.1'
BINDING_VERSION = 'v5.binding.b2'
FAMILY = 'B2'
CHECKER_PATH = pathlib.Path(rules_b2.__file__)

PAIRS = [
    {'slot': 'FP-16', 'task': 'FT-016', 'kind': 'REAL', 'project': 'cgeo/cgeo',
     'top1': 'LINT-033:ParcelCreator', 'rule': 'PARCEL_OBTAIN_WITHOUT_RECYCLE',
     'rel': 'tests/src/cgeo/geocaching/ImageTest.java', 'method': 'testParcel',
     'cfg': {}, 'object': 'ImageTest.testParcel() 的 parcel',
     'public': 'FT-016公开任务描述(DroidLeaks: android.os.Parcel leak in ImageTest.java::testParcel)',
     'rationale': 'ParcelCreator只要求Parcelable声明CREATOR，与obtain()后未recycle的对象池泄漏不是同一命题；公开任务直接要求查该资源的acquisition与缺失的close/release/recycle'},
    {'slot': 'FP-17', 'task': 'FT-017', 'kind': 'REAL', 'project': 'k9mail/k-9',
     'top1': 'SEMGREP_MOBSFSCAN-006:weak_cipher', 'rule': 'PFD_PIPE_ACQUIRED_NOT_CLOSED',
     'rel': 'plugins/openpgp-api-library/src/org/openintents/openpgp/util/OpenPgpApi.java',
     'method': 'executeApi',
     'cfg': {'types': ['ParcelFileDescriptor'], 'acquisition_callees': ['pipeFrom'],
             'release_methods': ['close']},
     'object': 'OpenPgpApi.executeApi() 的 input (line 222 pipeFrom)',
     'public': 'FT-017公开任务描述(DroidLeaks: ParcelFileDescriptor leak in OpenPgpApi.java::executeApi @line 222)',
     'rationale': 'weak_cipher是加密算法强度检查，与文件描述符生命周期无关；公开任务锁定pipeFrom在line 222产生的ParcelFileDescriptor，要求正常与异常返回路径都关闭'},
    {'slot': 'FP-35', 'task': 'FT-035', 'kind': 'REAL', 'project': 'syncthing/syncthing-android',
     'top1': 'SEMGREP_MOBSFSCAN-001:aes_ecb_mode', 'rule': 'SU_PIPE_LAST_WRITE_NOT_FLUSHED',
     'rel': 'app/src/main/java/com/nutomic/syncthingandroid/service/SyncthingRunnable.java',
     'method': 'setupAndLaunch',
     'cfg': {'stream_types': ['DataOutputStream'], 'source_methods': ['getOutputStream'],
             'write_methods': ['write', 'writeBytes', 'writeUTF', 'writeChars', 'writeInt',
                               'print', 'println', 'append'],
             'flush_methods': ['flush'], 'close_implies_flush': True},
     'object': 'SyncthingRunnable.setupAndLaunch() 的 suOut (su 进程 stdin)',
     'public': 'FT-035公开任务描述(Root-mode startup writes an exec command to the su process but returns before flushing the command stream)',
     'rationale': 'aes_ecb_mode是加密模式检查，与子进程管道写出无关；公开任务直接描述write exec后未flush即return，不变量为命令写入后须flush'},
]


def sha(p):
    p = pathlib.Path(p)
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None


# ---------------------------------------------------------------- counterexamples

def _src(rel, text):
    p = V5 / 'runs/B2/counterexample_src' / rel
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(text)
    return p


def _case(cases, name, rule, path, method, cfg, want, klass):
    got = rules_b2.verify(rule, {'java_file': path}, {'method': method}, cfg)
    cases.append({'name': name, 'family': FAMILY, 'rule_id': rule,
                  'counterexample_class': klass, 'expected': want,
                  'actual': got['observation'], 'reason': got['reason'],
                  'passed': got['observation'] == want})


PARCEL_RULE = 'PARCEL_OBTAIN_WITHOUT_RECYCLE'
PFD_RULE = 'PFD_PIPE_ACQUIRED_NOT_CLOSED'
FLUSH_RULE = 'SU_PIPE_LAST_WRITE_NOT_FLUSHED'


def _parcel_src(body, throws=''):
    return f'''package t;
import android.os.Parcel;
public class ParcelUse {{
    public void roundTrip(){throws} {{
{body}
    }}
}}
'''


def _pfd_cfg():
    return {'types': ['ParcelFileDescriptor'], 'acquisition_callees': ['pipeFrom'],
            'release_methods': ['close']}


def _pfd_src(body):
    return f'''package t;
import android.os.ParcelFileDescriptor;
public class OpenPgpApiLike {{
    public Object executeApi(Object is, Object os) throws Exception {{
{body}
    }}
}}
'''


def _flush_src(body):
    return f'''package t;
import java.io.DataOutputStream;
public class Launcher {{
    private boolean mUseRoot;
    public Process setupAndLaunch(Object env) throws Exception {{
{body}
    }}
}}
'''


def run_counterexamples():
    cases = []
    # ---- PARCEL_OBTAIN_WITHOUT_RECYCLE
    _case(cases, 'parcel_obtain_no_recycle', PARCEL_RULE,
          _src('b2/parcel_buggy.java', _parcel_src(
              '        Parcel p = Parcel.obtain();\n'
              '        p.setDataPosition(0);')), 'roundTrip', {},
          'PRESENT', 'defect_present')
    _case(cases, 'parcel_obtain_recycled', PARCEL_RULE,
          _src('b2/parcel_fixed.java', _parcel_src(
              '        Parcel p = Parcel.obtain();\n'
              '        p.setDataPosition(0);\n'
              '        p.recycle();')), 'roundTrip', {},
          'ABSENT', 'defect_repaired')
    _case(cases, 'parcel_recycle_in_finally', PARCEL_RULE,
          _src('b2/parcel_finally.java', _parcel_src(
              '        Parcel p = Parcel.obtain();\n'
              '        try {\n'
              '            p.setDataPosition(0);\n'
              '        } finally {\n'
              '            p.recycle();\n'
              '        }')), 'roundTrip', {},
          'ABSENT', 'defect_repaired_exception_path')
    _case(cases, 'parcel_recycle_normal_path_only', PARCEL_RULE,
          _src('b2/parcel_normal_path_only.java', _parcel_src(
              '        Parcel p = Parcel.obtain();\n'
              '        try {\n'
              '            p.setDataPosition(0);\n'
              '            p.recycle();\n'
              '        } catch (RuntimeException e) {\n'
              '            throw e;\n'
              '        }', throws=' throws Exception')), 'roundTrip', {},
          'PRESENT', 'exception_path_not_released')
    _case(cases, 'parcel_second_object_leaked', PARCEL_RULE,
          _src('b2/parcel_two_objects.java', _parcel_src(
              '        Parcel a = Parcel.obtain();\n'
              '        Parcel b = Parcel.obtain();\n'
              '        a.recycle();')), 'roundTrip', {},
          'PRESENT', 'wrong_object_sibling_recycled_only')
    _case(cases, 'parcel_non_recycle_call', PARCEL_RULE,
          _src('b2/parcel_unrelated_call.java', _parcel_src(
              '        Parcel p = Parcel.obtain();\n'
              '        p.setDataPosition(0);\n'
              '        p.close();')), 'roundTrip', {},
          'PRESENT', 'unrelated_modification')

    # ---- PFD_PIPE_ACQUIRED_NOT_CLOSED
    cfg = _pfd_cfg()
    _case(cases, 'pfd_input_unclosed_sibling_closed', PFD_RULE,
          _src('b2/pfd_buggy.java', _pfd_src(
              '        try {\n'
              '            ParcelFileDescriptor input = ParcelFileDescriptorUtil.pipeFrom(is);\n'
              '            ParcelFileDescriptor output = ParcelFileDescriptorUtil.pipeTo(os);\n'
              '            Object result = execute(input, output);\n'
              '            output.close();\n'
              '            return result;\n'
              '        } catch (Exception e) {\n'
              '            return null;\n'
              '        }')), 'executeApi', cfg,
          'PRESENT', 'defect_present')
    _case(cases, 'pfd_input_closed_in_finally', PFD_RULE,
          _src('b2/pfd_fixed.java', _pfd_src(
              '        ParcelFileDescriptor input = null;\n'
              '        try {\n'
              '            input = ParcelFileDescriptorUtil.pipeFrom(is);\n'
              '            ParcelFileDescriptor output = ParcelFileDescriptorUtil.pipeTo(os);\n'
              '            Object result = execute(input, output);\n'
              '            output.close();\n'
              '            return result;\n'
              '        } catch (Exception e) {\n'
              '            return null;\n'
              '        } finally {\n'
              '            if (input != null) {\n'
              '                input.close();\n'
              '            }\n'
              '        }')), 'executeApi', cfg,
          'ABSENT', 'defect_repaired_exception_path')
    _case(cases, 'pfd_close_on_normal_path_only', PFD_RULE,
          _src('b2/pfd_normal_path_only.java', _pfd_src(
              '        try {\n'
              '            ParcelFileDescriptor input = ParcelFileDescriptorUtil.pipeFrom(is);\n'
              '            Object result = execute(input, null);\n'
              '            input.close();\n'
              '            return result;\n'
              '        } catch (Exception e) {\n'
              '            return null;\n'
              '        }')), 'executeApi', cfg,
          'PRESENT', 'exception_path_not_released')
    _case(cases, 'pfd_other_object_closed', PFD_RULE,
          _src('b2/pfd_wrong_object.java', _pfd_src(
              '        ParcelFileDescriptor input = ParcelFileDescriptorUtil.pipeFrom(is);\n'
              '        ParcelFileDescriptor output = ParcelFileDescriptorUtil.pipeTo(os);\n'
              '        Object result = execute(input, output);\n'
              '        output.close();\n'
              '        return result;')), 'executeApi', cfg,
          'PRESENT', 'wrong_object_sibling_closed_only')
    _case(cases, 'pfd_try_with_resources', PFD_RULE,
          _src('b2/pfd_twr.java', _pfd_src(
              '        try (ParcelFileDescriptor input = ParcelFileDescriptorUtil.pipeFrom(is)) {\n'
              '            return execute(input, null);\n'
              '        }')), 'executeApi', cfg,
          'UNKNOWN', 'unsupported_construct_reports_unknown')

    # ---- SU_PIPE_LAST_WRITE_NOT_FLUSHED
    cfg = {}
    _case(cases, 'su_write_flushed_before_last_write', FLUSH_RULE,
          _src('b2/flush_buggy.java', _flush_src(
              '        if (mUseRoot) {\n'
              '            Process process = new ProcessBuilder("su").start();\n'
              '            DataOutputStream suOut = new DataOutputStream(process.getOutputStream());\n'
              '            suOut.writeBytes("export A=1\\n");\n'
              '            suOut.flush();\n'
              '            suOut.writeBytes("exec sync\\n");\n'
              '            return process;\n'
              '        } else {\n'
              '            return new ProcessBuilder("sync").start();\n'
              '        }')), 'setupAndLaunch', cfg,
          'PRESENT', 'defect_present')
    _case(cases, 'su_flush_after_last_write', FLUSH_RULE,
          _src('b2/flush_fixed.java', _flush_src(
              '        if (mUseRoot) {\n'
              '            Process process = new ProcessBuilder("su").start();\n'
              '            DataOutputStream suOut = new DataOutputStream(process.getOutputStream());\n'
              '            suOut.writeBytes("export A=1\\n");\n'
              '            suOut.flush();\n'
              '            suOut.writeBytes("exec sync\\n");\n'
              '            suOut.flush();\n'
              '            return process;\n'
              '        } else {\n'
              '            return new ProcessBuilder("sync").start();\n'
              '        }')), 'setupAndLaunch', cfg,
          'ABSENT', 'defect_repaired')
    _case(cases, 'su_never_flushed', FLUSH_RULE,
          _src('b2/flush_none.java', _flush_src(
              '        if (mUseRoot) {\n'
              '            Process process = new ProcessBuilder("su").start();\n'
              '            DataOutputStream suOut = new DataOutputStream(process.getOutputStream());\n'
              '            suOut.writeBytes("exec sync\\n");\n'
              '            return process;\n'
              '        } else {\n'
              '            return new ProcessBuilder("sync").start();\n'
              '        }')), 'setupAndLaunch', cfg,
          'PRESENT', 'defect_present_no_flush_at_all')
    _case(cases, 'su_flush_other_stream', FLUSH_RULE,
          _src('b2/flush_wrong_stream.java', _flush_src(
              '        Process process = new ProcessBuilder("su").start();\n'
              '        Process other = new ProcessBuilder("cat").start();\n'
              '        DataOutputStream suOut = new DataOutputStream(process.getOutputStream());\n'
              '        DataOutputStream logOut = new DataOutputStream(other.getOutputStream());\n'
              '        suOut.writeBytes("exec sync\\n");\n'
              '        logOut.flush();\n'
              '        return process;')), 'setupAndLaunch', cfg,
          'PRESENT', 'wrong_object_sibling_flushed_only')
    _case(cases, 'flush_unbound_stream', FLUSH_RULE,
          _src('b2/flush_unbound.java', _flush_src(
              '        java.io.FileOutputStream f = new java.io.FileOutputStream("x");\n'
              '        DataOutputStream out = new DataOutputStream(f);\n'
              '        out.writeBytes("hello\\n");\n'
              '        return null;')), 'setupAndLaunch', cfg,
          'UNKNOWN', 'not_the_target_object')

    failed = [c for c in cases if not c['passed']]
    by_class = {}
    for c in cases:
        by_class.setdefault(c['rule_id'], {}).setdefault(c['counterexample_class'], 0)
        by_class[c['rule_id']][c['counterexample_class']] += 1
        by_class[c['rule_id']].setdefault('_passed', 0)
        by_class[c['rule_id']]['_passed'] += int(c['passed'])
    out = {'all_passed': not failed, 'count': len(cases), 'failed': [c['name'] for c in failed],
           'by_rule': by_class,
           'class_legend': ['defect_present', 'defect_repaired', 'exception_path_not_released',
                            'wrong_object_sibling_*', 'unrelated_modification',
                            'unsupported_construct_reports_unknown', 'not_the_target_object'],
           'cases': cases}
    (V5 / 'checks').mkdir(exist_ok=True)
    (V5 / 'checks/B2_counterexamples.json').write_text(
        json.dumps(out, ensure_ascii=False, indent=2))
    print(json.dumps({'all_passed': not failed, 'count': len(cases),
                      'failed': [c['name'] for c in failed]}, ensure_ascii=False))
    return not failed


# ---------------------------------------------------------------- double-side runs

def _paths(pair, side):
    base = SNAP / pair['slot'] / side
    return {'java_file': base / pair['rel']}


def run_retest(only=None):
    outdir = V5 / 'runs/B2'
    outdir.mkdir(parents=True, exist_ok=True)
    rows = []
    for pair in PAIRS:
        if only and pair['slot'] not in only:
            continue
        for side in ('buggy', 'fixed'):
            inputs = _paths(pair, side)
            start = time.perf_counter()
            try:
                result = rules_b2.verify(pair['rule'], inputs, {'method': pair['method']},
                                        pair['cfg'])
                exit_status = 0
            except Exception as e:  # never guess on a crash
                result = {'observation': 'UNKNOWN', 'scope': pair['rule'], 'evidence': [],
                          'reason': 'CHECKER_CRASH:' + repr(e), 'duration_s': 0.0}
                exit_status = 1
            dur = time.perf_counter() - start
            receipt = {
                'pair_slot': pair['slot'], 'task_id': pair['task'], 'side': side,
                'kind': pair['kind'], 'family': FAMILY, 'rule_id': pair['rule'],
                'rule_version': RULE_VERSION, 'binding': {'method': pair['method']},
                'rule_config': pair['cfg'], 'observation': result['observation'],
                'scope': result['scope'], 'reason': result['reason'],
                'evidence': result['evidence'],
                'input_sha256': {k: sha(v) for k, v in inputs.items()},
                'command': [sys.executable, str(V5 / 'src/helpers_b2.py'), 'retest',
                            pair['slot'], side],
                'exit_status': exit_status, 'duration_s': round(dur, 4),
                'checker': 'rules_b2', 'checker_sha256': sha(CHECKER_PATH),
                'method': 'B4 v2加目标规则补正',
                'scoring_reference_read_by_checker': False}
            (outdir / f"{pair['slot']}-{side}.json").write_text(
                json.dumps(receipt, ensure_ascii=False, indent=2))
            rows.append({k: receipt[k] for k in ('pair_slot', 'side', 'rule_id',
                                                 'observation', 'reason', 'duration_s',
                                                 'exit_status')})
            print(pair['slot'], side, receipt['rule_id'], result['observation'],
                  result['reason'])
    (V5 / 'runs/B2/sides.jsonl').write_text(
        '\n'.join(json.dumps(r, ensure_ascii=False) for r in rows) + '\n')


# ---------------------------------------------------------------- scoring

def run_score():
    refs = {c['pair_slot']: c['reference']
            for c in map(json.loads, CONTRACTS.read_text().splitlines())}
    v3 = {r['pair_slot']: r for r in csv.DictReader(V3.open())}
    ce = json.loads((V5 / 'checks/B2_counterexamples.json').read_text())
    results, align_rows = [], []
    for pair in PAIRS:
        sides = {}
        for side in ('buggy', 'fixed'):
            sides[side] = json.loads(
                (V5 / 'runs/B2' / f"{pair['slot']}-{side}.json").read_text())
        obs = {s: sides[s]['observation'] for s in sides}
        ref = refs[pair['slot']]
        no_unknown = 'UNKNOWN' not in (obs['buggy'], obs['fixed'])
        if not no_unknown:
            cls = 'UNRESOLVED'
        elif obs['buggy'] == ref['buggy'] and obs['fixed'] == ref['fixed']:
            cls = 'MATCHED'
        else:
            cls = 'MISMATCHED'
        status = {'MATCHED': 'B2完成(MATCHED,双侧观测与参考一致)',
                  'UNRESOLVED': 'B2未决(UNKNOWN:' + ';'.join(
                      f"{s}={sides[s]['reason']}" for s in sides if sides[s]['observation'] == 'UNKNOWN') + ')',
                  'MISMATCHED': ('B2不符(观测%s/%s,参考%s/%s)' % (
                      obs['buggy'], obs['fixed'], ref['buggy'], ref['fixed']))}[cls]
        results.append({
            'pair_slot': pair['slot'], 'task_id': pair['task'], 'kind': pair['kind'],
            'project': pair['project'], '原Top1': pair['top1'], '补正规则': pair['rule'],
            'target_object': pair['object'], 'obs_buggy': obs['buggy'],
            'obs_fixed': obs['fixed'], 'reference_buggy': ref['buggy'],
            'reference_fixed': ref['fixed'], 'result_class': cls,
            'result_class_v3': v3[pair['slot']]['result_class'],
            'is_new_success': cls == 'MATCHED' and v3[pair['slot']]['result_class'] != 'MATCHED',
            'reason_buggy': sides['buggy']['reason'],
            'reason_fixed': sides['fixed']['reason'],
            'duration_s': round(sides['buggy']['duration_s'] + sides['fixed']['duration_s'], 4),
            'receipts': [f'runs/B2/{pair["slot"]}-buggy.json',
                         f'runs/B2/{pair["slot"]}-fixed.json']})
        align_rows.append({
            'pair_slot': pair['slot'], 'task_id': pair['task'], 'kind': pair['kind'],
            'project': pair['project'], '原Top1': pair['top1'],
            '补正规则': pair['rule'],
            '目标文件/方法/组件': f"{pair['rel']}::{pair['method']}() ({pair['object']})",
            '对应理由': pair['rationale'], '公开来源': pair['public'],
            '目标绑定版本': BINDING_VERSION, '实现状态': status})

    fieldnames = ['pair_slot', 'task_id', 'kind', 'project', '原Top1', '补正规则',
                  '目标文件/方法/组件', '对应理由', '公开来源', '目标绑定版本', '实现状态']
    (V5 / 'data/alignment_fragments').mkdir(parents=True, exist_ok=True)
    with (V5 / 'data/alignment_fragments/B2.csv').open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(align_rows)

    matched = [r for r in results if r['result_class'] == 'MATCHED']
    report = {
        'family': FAMILY, 'batch': 'B', 'version': RULE_VERSION,
        'binding_version': BINDING_VERSION, 'date': '2026-10-17',
        'method': 'B4 v2加目标规则补正',
        'checker': 'src/rules_b2.py', 'checker_sha256': sha(CHECKER_PATH),
        'pairs': results,
        'counterexamples': {'all_passed': ce['all_passed'], 'count': ce['count'],
                            'failed': ce['failed'], 'by_rule': ce['by_rule'],
                            'file': 'checks/B2_counterexamples.json'},
        'summary': {'pairs': len(results), 'matched': len(matched),
                    'new_success': sum(1 for r in results if r['is_new_success']),
                    'real_matched': sum(1 for r in matched if r['kind'] == 'REAL'),
                    'unresolved': [r['pair_slot'] for r in results
                                   if r['result_class'] == 'UNRESOLVED'],
                    'mismatched': [r['pair_slot'] for r in results
                                   if r['result_class'] == 'MISMATCHED']},
        'rule_selection': {
            'basis': '公开任务描述 + 公开源码特征；未使用参考标签/修复差异/预期PRESENT-ABSENT',
            'candidate_library': 'exp1_recommendation_v2/data/public/plans.jsonl (176条)',
            'candidate_scan': {
                'LINT-028:Recycle': {'proposition': 'MISMATCH', 'for_pair': 'FP-16',
                                     'why': '该候选机制关键词为 typedarray/cursor recycle；lint Recycle 针对 TypedArray 的 recycle，Parcel.obtain()/recycle() 生命周期不在其命题内'},
                'LINT-033:ParcelCreator': {'proposition': 'MISMATCH', 'for_pair': 'FP-16',
                                           'why': '只要求 Parcelable 声明 CREATOR，与对象池 Parcel 未回收无关(原Top1即此条)'},
                'PMD-003:CloseResource': {'proposition': 'ADJACENT_NOT_EXECUTABLE',
                                          'for_pair': 'FP-17',
                                          'why': '命题为 AutoCloseable 用完即关(含异常路径)，方向一致；但执行需类型解析与 Android 类路径，快照无构建类路径，且其为文件级规则、无 executeApi/line 222 同对象绑定，故仅复用命题并以 v5 AST 检查器实现'},
                'SPOTBUGS-023/024:OS_OPEN_STREAM*': {'proposition': 'ADJACENT_NOT_EXECUTABLE',
                                                    'for_pair': 'FP-17',
                                                    'why': '输入模式为 BYTECODE_CLASSES，任务制品为源码；无方法级对象绑定'},
                'flush': {'proposition': 'NO_CANDIDATE', 'for_pair': 'FP-35',
                          'why': '176候选的机制关键词中无任何 flush/子进程管道写出类规则，需新建'}},
            'chosen': {p['slot']: {'rule_id': p['rule'], 'public_source': p['public'],
                                   'binding': f"{p['rel']}::{p['method']}()",
                                   'rule_config': p['cfg']} for p in PAIRS}},
        'limitations': [
            'JavaFactsDeep 不序列化 try-with-resources 资源声明：此类构造返回 UNKNOWN'
            '(TRY_WITH_RESOURCES_NOT_SERIALISED)，不判为已修复',
            '并发/多线程时序不作证明；判定为静态全退出路径属性',
            'PFD 规则的异常路径采用“try 内可能已获取”的保守继承，只会更严格，不会放宽为 ABSENT'],
        'scoring_reference_read_at': 'score step only (helpers_b2.py score)',
        'checkers_receive_expected_answer': False,
    }
    (V5 / 'progress/B2_report.json').write_text(
        json.dumps(report, ensure_ascii=False, indent=2))
    print(json.dumps(report['summary'] | {'counterexamples': report['counterexamples']},
                     ensure_ascii=False, indent=1))


def main(argv):
    cmd = argv[1] if len(argv) > 1 else ''
    if cmd == 'counterexamples':
        return 0 if run_counterexamples() else 1
    if cmd == 'retest':
        only = argv[2:3] or None
        run_retest(only)
        return 0
    if cmd == 'score':
        run_score()
        return 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv))
