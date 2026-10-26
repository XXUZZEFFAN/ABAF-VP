"""B3 batch tooling: counterexample fixtures, actual double-side runs, scoring.

Commands
--------
    python src/helpers_b3.py counterexamples   # fixture suite -> checks/b3_counterexamples.json
    python src/helpers_b3.py run-pairs         # 7 pairs x 2 sides -> runs/B3/*.json
    python src/helpers_b3.py score             # scoring phase only (reads references)

Checkers never receive expected answers: fixtures below carry their expectation only
in this driver, and scoring reads the v1 target contracts after all runs are frozen.
"""
import csv
import hashlib
import json
import pathlib
import shutil
import sys
import time

V5 = pathlib.Path(__file__).resolve().parents[1]
ROOT = V5.parents[2]
WS = ROOT / 'ABAF_VP_完整实验方案_2026-10-11/workspace'
SNAP = WS / 'p2_pair_selection/snapshots'
GHERA = WS / 'p0_inventory/ghera_src'
CONTRACTS = V5.parent / 'exp3_paired_validation_v1/data/target_contracts.jsonl'
V3 = V5.parent / 'exp3_paired_validation_v3/analysis/pair_results.csv'
sys.path.insert(0, str(V5 / 'src'))
import rules_b3  # noqa: E402

RULE_VERSION = 'v5.rule.b3.1'
FAMILY = 'B3'
FIXROOT = V5 / 'runs' / FAMILY / 'counterexamples'

WINDOW_CFG = {'secure_flag': 'FLAG_SECURE', 'flag_setters': ['addFlags', 'setFlags'],
              'base_name_prefix': 'PassphraseRequired'}
PROVIDER_CFG = {'sink_methods': ['insert', 'update', 'delete', 'query', 'write',
                                 'getWritableDatabase', 'getReadableDatabase',
                                 'openFile', 'openAssetFile'],
                'sink_types': ['FileOutputStream', 'FileWriter', 'SQLiteDatabase']}
EXTRA_CFG = {'extra_getters': ['getStringExtra', 'getIntExtra', 'getBooleanExtra',
                               'getParcelableExtra', 'getSerializableExtra',
                               'getCharSequenceExtra', 'getStringArrayListExtra',
                               'getBundleExtra']}
STORAGE_CFG = {
    'external_dir_methods': ['getExternalFilesDir', 'getExternalCacheDir',
                             'getExternalStorageDirectory', 'getExternalStoragePublicDirectory'],
    'internal_dir_methods': ['getFilesDir', 'getCacheDir', 'getDir', 'getDatabasePath'],
    'stream_types': ['FileOutputStream', 'FileWriter', 'BufferedWriter', 'OutputStreamWriter'],
    'sensitive_sources': ['openRawResource', 'getContentResolver', 'getText', 'getPassword'],
    'propagators': ['read', 'getBytes', 'toString'],
    'write_methods': ['write', 'writeBytes', 'append']}
RUNTIME_CFG = {'sensitive_methods': ['startActivity', 'sendBroadcast', 'startService',
                                    'insert', 'update', 'delete']}
CLIP_CFG = {'clip_method': 'setPrimaryClip', 'sensitive_getters': ['getText', 'getPassword']}


def sha(p):
    p = pathlib.Path(p)
    return hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None


def tree_sha(root):
    h = hashlib.sha256()
    for p in sorted(pathlib.Path(root).rglob('*.java')):
        h.update(str(p.relative_to(root)).encode())
        h.update(sha(p).encode())
    return h.hexdigest()


# ------------------------------------------------------------------ fixtures
JAVA = {
    'PassphraseRequiredActivity': '''package org.demo;
public interface PassphraseRequiredActivity { void onMasterSecretCleared(); }
''',
    'PassphraseRequiredMixin.plain': '''package org.demo;
public class PassphraseRequiredMixin {
  public void onResume(PassphraseRequiredActivity activity) {
    activity.onMasterSecretCleared();
  }
}
''',
    'PassphraseRequiredMixin.secure': '''package org.demo;
import android.view.WindowManager;
public class PassphraseRequiredMixin {
  public void onResume(PassphraseRequiredActivity activity) {
    initializeScreenshotSecurity(activity);
  }
  private void initializeScreenshotSecurity(PassphraseRequiredActivity activity) {
    activity.getWindow().addFlags(WindowManager.LayoutParams.FLAG_SECURE);
  }
}
''',
    'PassphraseRequiredBase': '''package org.demo;
import android.app.Activity;
public class PassphraseRequiredBase extends Activity implements PassphraseRequiredActivity {
  private final PassphraseRequiredMixin delegate = new PassphraseRequiredMixin();
  @Override
  protected void onResume() {
    super.onResume();
    delegate.onResume(this);
  }
  @Override
  public void onMasterSecretCleared() { }
}
''',
    'ContactsScreen.inherit': '''package org.demo;
public class ContactsScreen extends PassphraseRequiredBase { }
''',
    'ContactsScreen.own': '''package org.demo;
import android.view.WindowManager;
public class ContactsScreen extends PassphraseRequiredBase {
  @Override
  protected void onResume() {
    super.onResume();
    getWindow().addFlags(WindowManager.LayoutParams.FLAG_SECURE);
  }
}
''',
    'SettingsScreen': '''package org.demo;
public class SettingsScreen extends PassphraseRequiredBase { }
''',
    'HomeScreen': '''package org.demo;
import android.app.Activity;
public class HomeScreen extends Activity { }
''',
    'DemoProvider': '''package org.demo;
import android.content.ContentProvider;
import android.content.ContentValues;
import android.database.Cursor;
import android.net.Uri;
import android.os.Bundle;
import java.io.FileOutputStream;
public class DemoProvider extends ContentProvider {
  public boolean onCreate() { return true; }
  public Cursor query(Uri uri, String[] p, String s, String[] a, String o) { return null; }
  public String getType(Uri uri) { return null; }
  public Uri insert(Uri uri, ContentValues v) { return uri; }
  public int delete(Uri uri, String s, String[] a) { return 0; }
  public int update(Uri uri, ContentValues v, String s, String[] a) { return 0; }
  public Bundle call(String method, String arg, Bundle extras) {
    try {
      FileOutputStream out = new FileOutputStream(getContext().getFilesDir() + "/backup");
      out.write(1);
    } catch (Exception e) { }
    return null;
  }
}
''',
    'ExtraPresent': '''package org.demo;
import android.app.Activity;
import android.content.Intent;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;
import android.widget.TextView;
public class MainActivity extends Activity {
  protected void onCreate(Bundle b) { super.onCreate(b); }
  protected void onResume() {
    super.onResume();
    Button button = (Button) findViewById(1);
    button.setOnClickListener(new View.OnClickListener() {
      public void onClick(View v) {
        TextView textView = (TextView) findViewById(2);
        Intent intent = getIntent();
        String a = intent.getStringExtra("s1");
        String b = intent.getStringExtra("s2");
        textView.setText("total length:" + Integer.toString(a.length() + b.length()));
      }
    });
  }
}
''',
    'ExtraRepaired': '''package org.demo;
import android.app.Activity;
import android.content.Intent;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;
import android.widget.TextView;
public class MainActivity extends Activity {
  protected void onCreate(Bundle b) { super.onCreate(b); }
  protected void onResume() {
    super.onResume();
    Button button = (Button) findViewById(1);
    button.setOnClickListener(new View.OnClickListener() {
      public void onClick(View v) {
        TextView textView = (TextView) findViewById(2);
        Intent intent = getIntent();
        if (intent.getExtras() != null) {
          String a = intent.getStringExtra("s1");
          String b = intent.getStringExtra("s2");
          try {
            textView.setText("total:" + Integer.toString(a.length() + b.length()));
          } catch (NullPointerException e) {
            textView.setText("missing");
          }
        }
      }
    });
  }
}
''',
    'ExtraBranch': '''package org.demo;
import android.app.Activity;
import android.content.Intent;
import android.os.Bundle;
import android.widget.TextView;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    TextView textView = (TextView) findViewById(2);
    Intent intent = getIntent();
    String a = intent.getStringExtra("s1");
    String b = intent.getStringExtra("s2");
    if (a != null) { textView.setText(a.trim()); }
    textView.setText(b.trim());
  }
}
''',
    'ExtraEarlyExit': '''package org.demo;
import android.app.Activity;
import android.content.Intent;
import android.os.Bundle;
import android.widget.TextView;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    TextView textView = (TextView) findViewById(2);
    Intent intent = getIntent();
    String a = intent.getStringExtra("s1");
    if (a == null) { return; }
    textView.setText(a.trim());
  }
}
''',
    'ExtraWrongObject': '''package org.demo;
import android.app.Activity;
import android.content.Intent;
import android.os.Bundle;
import android.widget.TextView;
public class MainActivity extends Activity {
  protected void onResume() { super.onResume(); }
}
class Helper {
  void read(Intent intent, TextView textView) {
    String a = intent.getStringExtra("s1");
    textView.setText(a.trim());
  }
}
''',
    'StoragePresent': '''package org.demo;
import android.app.Activity;
import android.os.Bundle;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    File file = new File(getExternalFilesDir(null), "ssn_bkup.jpg");
    try {
      InputStream is = getResources().openRawResource(1);
      FileOutputStream os = new FileOutputStream(file);
      byte[] data = new byte[is.available()];
      is.read(data);
      os.write(data);
      is.close();
      os.close();
    } catch (Exception e) { }
  }
}
''',
    'StorageRepaired': '''package org.demo;
import android.app.Activity;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    File file = new File(getFilesDir(), "ssn_bkup.jpg");
    try {
      InputStream is = getResources().openRawResource(1);
      FileOutputStream os = new FileOutputStream(file);
      byte[] data = new byte[is.available()];
      is.read(data);
      os.write(data);
    } catch (Exception e) { }
  }
}
''',
    'StorageConstant': '''package org.demo;
import android.app.Activity;
import java.io.File;
import java.io.FileOutputStream;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    File file = new File(getExternalFilesDir(null), "status.txt");
    try {
      FileOutputStream os = new FileOutputStream(file);
      byte[] data = new byte[] {1, 2, 3};
      os.write(data);
    } catch (Exception e) { }
  }
}
''',
    'StorageAlias': '''package org.demo;
import android.app.Activity;
import java.io.File;
import java.io.FileOutputStream;
import java.io.InputStream;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    File dir = getExternalFilesDir(null);
    try {
      File file = new File(dir, "ssn_bkup.jpg");
      InputStream is = getResources().openRawResource(1);
      FileOutputStream os = new FileOutputStream(file);
      byte[] data = new byte[is.available()];
      is.read(data);
      os.write(data);
    } catch (Exception e) { }
  }
}
''',
    'ServiceCheck': '''package org.demo;
import android.app.Service;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.os.IBinder;
public class MyService extends Service {
  public int onStartCommand(Intent intent, int flags, int startId) {
    if (checkCallingOrSelfPermission("org.demo.PERM") == PackageManager.PERMISSION_GRANTED) {
      startActivity(new Intent(this, SensitiveActivity.class));
    }
    return 1;
  }
  public IBinder onBind(Intent intent) { return null; }
}
''',
    'ServiceEnforce': '''package org.demo;
import android.app.Service;
import android.content.Intent;
import android.os.IBinder;
public class MyService extends Service {
  public int onStartCommand(Intent intent, int flags, int startId) {
    try {
      enforceCallingOrSelfPermission("org.demo.PERM", "denied");
      startActivity(new Intent(this, SensitiveActivity.class));
    } catch (SecurityException e) { }
    return 1;
  }
  public IBinder onBind(Intent intent) { return null; }
}
''',
    'ClipboardPresent': '''package org.demo;
import android.app.Activity;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.os.Bundle;
import android.view.View;
import android.widget.Button;
import android.widget.EditText;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    Button copyPass = (Button) findViewById(1);
    copyPass.setOnClickListener(new View.OnClickListener() {
      public void onClick(View v) {
        ClipboardManager clipboard = (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
        ClipData clip = ClipData.newPlainText("Password", copyData());
        clipboard.setPrimaryClip(clip);
      }
    });
  }
  private String copyData() {
    EditText et = (EditText) findViewById(2);
    return et.getText().toString();
  }
}
''',
    'ClipboardRepaired': '''package org.demo;
import android.app.Activity;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.view.View;
import android.widget.Button;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    Button copyPass = (Button) findViewById(1);
    copyPass.setOnClickListener(new View.OnClickListener() {
      public void onClick(View v) {
        ClipboardManager clipboard = (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
        ClipData clip = ClipData.newPlainText("Password", "DummyPass");
        clipboard.setPrimaryClip(clip);
      }
    });
  }
}
''',
    'ClipboardWrongObject': '''package org.demo;
import android.app.Activity;
import android.os.Bundle;
import android.widget.EditText;
import android.widget.TextView;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    TextView textView = (TextView) findViewById(1);
    EditText et = (EditText) findViewById(2);
    textView.setText(et.getText().toString());
  }
}
''',
    'ClipboardAlias': '''package org.demo;
import android.app.Activity;
import android.content.ClipData;
import android.content.ClipboardManager;
import android.content.Context;
import android.widget.EditText;
public class MainActivity extends Activity {
  protected void onResume() {
    super.onResume();
    EditText et = (EditText) findViewById(2);
    String value = et.getText().toString();
    ClipboardManager clipboard = (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
    ClipData clip = ClipData.newPlainText("Password", value);
    clipboard.setPrimaryClip(clip);
  }
}
''',
}

MANIFEST = '''<?xml version="1.0" encoding="utf-8"?>
<manifest xmlns:android="http://schemas.android.com/apk/res/android" package="org.demo">
  <permission android:name="org.demo.PERM"{perm_level} />
  <uses-permission android:name="org.demo.PERM" />
  <application>
    <provider android:name=".DemoProvider" android:authorities="org.demo.provider"{provider}/>
    <service android:name=".MyService"{service} />
  </application>
</manifest>
'''


def _manifest(perm_level='', provider=' android:exported="true"',
              service=' android:exported="true"'):
    return MANIFEST.format(perm_level=perm_level, provider=provider, service=service)


def _write(base, files):
    if base.exists():
        shutil.rmtree(base)
    for rel, content in files.items():
        p = base / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content)


def _window_tree(name, mixin_key, contacts_key, extra=None):
    base = FIXROOT / name
    files = {
        'src/org/demo/PassphraseRequiredActivity.java': JAVA['PassphraseRequiredActivity'],
        'src/org/demo/PassphraseRequiredMixin.java': JAVA[mixin_key],
        'src/org/demo/PassphraseRequiredBase.java': JAVA['PassphraseRequiredBase'],
        'src/org/demo/ContactsScreen.java': JAVA[contacts_key],
        'src/org/demo/SettingsScreen.java': JAVA['SettingsScreen'],
    }
    files.update(extra or {})
    _write(base, files)
    return base / 'src'


def _single_tree(name, java_key, manifest=None):
    base = FIXROOT / name
    files = {'app/src/main/java/org/demo/MainActivity.java': JAVA[java_key]}
    if manifest is not None:
        files['app/src/main/AndroidManifest.xml'] = manifest
    _write(base, files)
    return base


def _provider_tree(name, java_key, manifest):
    base = FIXROOT / name
    _write(base, {'app/src/main/java/org/demo/DemoProvider.java': JAVA[java_key],
                  'app/src/main/AndroidManifest.xml': manifest})
    return base


def _service_tree(name, java_key, manifest):
    base = FIXROOT / name
    _write(base, {'app/src/main/java/org/demo/MyService.java': JAVA[java_key],
                  'app/src/main/AndroidManifest.xml': manifest})
    return base


def _window_case(name, tree, expected, klass):
    return {'name': name, 'rule_id': 'WINDOW_FLAG_SECURE_COVERAGE',
            'counterexample_class': klass, 'expected': expected,
            'inputs': {'source_root': tree},
            'binding': {'protected_interface': 'PassphraseRequiredActivity',
                        'mixin_class': 'PassphraseRequiredMixin', 'lifecycle': 'onResume'},
            'cfg': WINDOW_CFG}


def _file_case(name, rule_id, base, expected, klass, method, cfg, component='MainActivity'):
    return {'name': name, 'rule_id': rule_id, 'counterexample_class': klass,
            'expected': expected,
            'inputs': {'java_file': base / ('app/src/main/java/org/demo/%s.java' % component),
                       'manifest': base / 'app/src/main/AndroidManifest.xml'},
            'binding': {'method': method}, 'cfg': cfg}


def build_counterexamples():
    cases = []
    cases.append(_window_case('window_uncovered', _window_tree(
        'window_uncovered', 'PassphraseRequiredMixin.plain', 'ContactsScreen.inherit'),
        'PRESENT', 'defect_present'))
    cases.append(_window_case('window_mixin_secure', _window_tree(
        'window_mixin_secure', 'PassphraseRequiredMixin.secure', 'ContactsScreen.inherit'),
        'ABSENT', 'defect_repaired'))
    cases.append(_window_case('window_partial_override', _window_tree(
        'window_partial_override', 'PassphraseRequiredMixin.plain', 'ContactsScreen.own'),
        'PRESENT', 'branch_partial_coverage'))
    cases.append(_window_case('window_unrelated_files', _window_tree(
        'window_unrelated_files', 'PassphraseRequiredMixin.plain', 'ContactsScreen.inherit',
        {'src/org/demo/HomeScreen.java': JAVA['HomeScreen'],
         'src/org/demo/Empty.java': 'package org.demo;\nclass Empty { }\n'}),
        'PRESENT', 'unrelated_modification'))
    # wrong-object variant: no passphrase-protected screen at all
    base = FIXROOT / 'window_no_protected_screen'
    _write(base, {
        'src/org/demo/PassphraseRequiredActivity.java': JAVA['PassphraseRequiredActivity'],
        'src/org/demo/PassphraseRequiredMixin.java': JAVA['PassphraseRequiredMixin.plain'],
        'src/org/demo/HomeScreen.java': JAVA['HomeScreen']})
    cases.append({'name': 'window_no_protected_screen', 'rule_id': 'WINDOW_FLAG_SECURE_COVERAGE',
                  'counterexample_class': 'wrong_object', 'expected': 'UNKNOWN',
                  'inputs': {'source_root': base / 'src'},
                  'binding': {'protected_interface': 'PassphraseRequiredActivity',
                              'mixin_class': 'PassphraseRequiredMixin', 'lifecycle': 'onResume'},
                  'cfg': WINDOW_CFG})

    cases.append(_file_case('provider_present', 'PROVIDER_CALL_OPERATION_PERMISSION',
                            _provider_tree('provider_present', 'DemoProvider',
                                           _manifest(provider=' android:exported="true"')),
                            'PRESENT', 'defect_present', 'call', PROVIDER_CFG,
                            component='DemoProvider'))
    cases.append(_file_case('provider_permission', 'PROVIDER_CALL_OPERATION_PERMISSION',
                            _provider_tree('provider_permission', 'DemoProvider',
                                           _manifest(perm_level=' android:protectionLevel="signature"',
                                                     provider=' android:exported="true"'
                                                              ' android:permission="org.demo.PERM"')),
                            'ABSENT', 'defect_repaired', 'call', PROVIDER_CFG,
                            component='DemoProvider'))
    cases.append(_file_case('provider_writeperm_only', 'PROVIDER_CALL_OPERATION_PERMISSION',
                            _provider_tree('provider_writeperm_only', 'DemoProvider',
                                           _manifest(provider=' android:exported="true"'
                                                              ' android:writePermission="org.demo.PERM"')),
                            'PRESENT', 'wrong_value_not_repair', 'call', PROVIDER_CFG,
                            component='DemoProvider'))
    cases.append(_file_case('provider_not_exported', 'PROVIDER_CALL_OPERATION_PERMISSION',
                            _provider_tree('provider_not_exported', 'DemoProvider',
                                           _manifest(provider=' android:exported="false"')),
                            'ABSENT', 'wrong_object', 'call', PROVIDER_CFG,
                            component='DemoProvider'))

    cases.append(_file_case('extra_present', 'INTENT_EXTRA_UNGUARDED_DEREFERENCE',
                            _single_tree('extra_present', 'ExtraPresent'),
                            'PRESENT', 'defect_present', 'onResume', EXTRA_CFG))
    cases.append(_file_case('extra_repaired', 'INTENT_EXTRA_UNGUARDED_DEREFERENCE',
                            _single_tree('extra_repaired', 'ExtraRepaired'),
                            'ABSENT', 'defect_repaired', 'onResume', EXTRA_CFG))
    cases.append(_file_case('extra_branch_guard', 'INTENT_EXTRA_UNGUARDED_DEREFERENCE',
                            _single_tree('extra_branch_guard', 'ExtraBranch'),
                            'PRESENT', 'branch_partial_guard', 'onResume', EXTRA_CFG))
    cases.append(_file_case('extra_early_exit', 'INTENT_EXTRA_UNGUARDED_DEREFERENCE',
                            _single_tree('extra_early_exit', 'ExtraEarlyExit'),
                            'ABSENT', 'branch_early_exit_guard', 'onResume', EXTRA_CFG))
    cases.append(_file_case('extra_wrong_method', 'INTENT_EXTRA_UNGUARDED_DEREFERENCE',
                            _single_tree('extra_wrong_method', 'ExtraWrongObject'),
                            'UNKNOWN', 'wrong_object', 'onResume', EXTRA_CFG))

    cases.append(_file_case('storage_present', 'EXTERNAL_STORAGE_SENSITIVE_WRITE',
                            _single_tree('storage_present', 'StoragePresent'),
                            'PRESENT', 'defect_present', 'onResume', STORAGE_CFG))
    cases.append(_file_case('storage_internal', 'EXTERNAL_STORAGE_SENSITIVE_WRITE',
                            _single_tree('storage_internal', 'StorageRepaired'),
                            'ABSENT', 'defect_repaired', 'onResume', STORAGE_CFG))
    cases.append(_file_case('storage_constant', 'EXTERNAL_STORAGE_SENSITIVE_WRITE',
                            _single_tree('storage_constant', 'StorageConstant'),
                            'ABSENT', 'wrong_value_not_repair', 'onResume', STORAGE_CFG))
    cases.append(_file_case('storage_alias', 'EXTERNAL_STORAGE_SENSITIVE_WRITE',
                            _single_tree('storage_alias', 'StorageAlias'),
                            'PRESENT', 'alias_and_exception_path', 'onResume', STORAGE_CFG))

    for api_rule, java_key, api in (
            ('CHECK_CALLING_OR_SELF_PERMISSION_SELF_GRANTED', 'ServiceCheck',
             'checkCallingOrSelfPermission'),
            ('ENFORCE_CALLING_OR_SELF_PERMISSION_SELF_GRANTED', 'ServiceEnforce',
             'enforceCallingOrSelfPermission')):
        tag = 'check' if 'CHECK' in api_rule else 'enforce'
        cfg = dict(RUNTIME_CFG, runtime_api=api)
        cases.append(_file_case('%s_present' % tag, api_rule,
                                _service_tree('%s_present' % tag, java_key,
                                              _manifest(service=' android:exported="true"')),
                                'PRESENT', 'defect_present', 'onStartCommand', cfg,
                                component='MyService'))
        cases.append(_file_case('%s_signature' % tag, api_rule,
                                _service_tree('%s_signature' % tag, java_key,
                                              _manifest(perm_level=' android:protectionLevel="signature"',
                                                        service=' android:exported="true"'
                                                                ' android:permission="org.demo.PERM"')),
                                'ABSENT', 'defect_repaired', 'onStartCommand', cfg,
                                component='MyService'))
        cases.append(_file_case('%s_normal_perm' % tag, api_rule,
                                _service_tree('%s_normal_perm' % tag, java_key,
                                              _manifest(service=' android:exported="true"'
                                                                ' android:permission="org.demo.PERM"')),
                                'PRESENT', 'wrong_value_not_repair', 'onStartCommand', cfg,
                                component='MyService'))
        cases.append(_file_case('%s_not_exported' % tag, api_rule,
                                _service_tree('%s_not_exported' % tag, java_key,
                                              _manifest(service=' android:exported="false"')),
                                'ABSENT', 'wrong_object', 'onStartCommand', cfg,
                                component='MyService'))

    cases.append(_file_case('clipboard_present', 'CLIPBOARD_SENSITIVE_PRIMARY_CLIP',
                            _single_tree('clipboard_present', 'ClipboardPresent'),
                            'PRESENT', 'defect_present', 'onResume', CLIP_CFG))
    cases.append(_file_case('clipboard_constant', 'CLIPBOARD_SENSITIVE_PRIMARY_CLIP',
                            _single_tree('clipboard_constant', 'ClipboardRepaired'),
                            'ABSENT', 'defect_repaired', 'onResume', CLIP_CFG))
    cases.append(_file_case('clipboard_wrong_object', 'CLIPBOARD_SENSITIVE_PRIMARY_CLIP',
                            _single_tree('clipboard_wrong_object', 'ClipboardWrongObject'),
                            'UNKNOWN', 'wrong_object', 'onResume', CLIP_CFG))
    cases.append(_file_case('clipboard_alias', 'CLIPBOARD_SENSITIVE_PRIMARY_CLIP',
                            _single_tree('clipboard_alias', 'ClipboardAlias'),
                            'PRESENT', 'alias', 'onResume', CLIP_CFG))
    return cases


def run_counterexamples():
    FIXROOT.mkdir(parents=True, exist_ok=True)
    cases = build_counterexamples()
    results = []
    for case in cases:
        start = time.perf_counter()
        try:
            out = rules_b3.verify(case['rule_id'], case['inputs'], case['binding'], case['cfg'])
            actual, reason = out['observation'], out['reason']
        except Exception as e:  # fixture/checker bug must surface, not be guessed away
            actual, reason = 'CRASH', repr(e)
        results.append({'name': case['name'], 'family': FAMILY, 'rule_id': case['rule_id'],
                        'counterexample_class': case['counterexample_class'],
                        'expected': case['expected'], 'actual': actual,
                        'reason': reason, 'passed': actual == case['expected'],
                        'duration_s': round(time.perf_counter() - start, 4)})
        print('%-28s %-42s exp=%-7s got=%-7s %s' % (
            case['name'], case['rule_id'], case['expected'], actual,
            'PASS' if actual == case['expected'] else 'FAIL'))
    by_rule = {}
    for r in results:
        row = by_rule.setdefault(r['rule_id'], {'total': 0, 'passed': 0, 'classes': []})
        row['total'] += 1
        row['passed'] += int(r['passed'])
        row['classes'].append(r['counterexample_class'])
    summary = {'family': FAMILY, 'all_passed': all(r['passed'] for r in results),
               'count': len(results), 'by_rule': by_rule,
               'classes_covered': sorted({r['counterexample_class'] for r in results}),
               'cases': results}
    out_path = V5 / 'checks' / 'b3_counterexamples.json'
    out_path.write_text(json.dumps(summary, ensure_ascii=False, indent=2))
    print(json.dumps({'count': summary['count'], 'all_passed': summary['all_passed'],
                      'by_rule': {k: '%d/%d' % (v['passed'], v['total'])
                                  for k, v in by_rule.items()}}, ensure_ascii=False, indent=1))
    return summary


# --------------------------------------------------------------------- pairs
def _ghera(slot, rel, side):
    return GHERA / rel / ('Benign' if side == 'buggy' else 'Secure')


PAIRS = [
    {'slot': 'FP-11', 'task': 'FT-011', 'kind': 'REAL',
     'rule': 'WINDOW_FLAG_SECURE_COVERAGE',
     'base': lambda side: SNAP / 'FP-11' / side,
     'binding': {'protected_interface': 'PassphraseRequiredActivity',
                 'mixin_class': 'PassphraseRequiredMixin', 'lifecycle': 'onResume'},
     'cfg': WINDOW_CFG,
     'inputs': lambda base: {'source_root': base},
     'target': 'src/org/thoughtcrime/securesms/PassphraseRequiredMixin.onResume + '
               '13 PassphraseRequiredSherlock* 界面继承链'},
    {'slot': 'FP-37', 'task': 'FT-037', 'kind': 'BENCHMARK',
     'rule': 'PROVIDER_CALL_OPERATION_PERMISSION',
     'base': lambda side: _ghera('FP-37', 'ICC/WeakChecksOnDynamicInvocation-DataInjection-Lean', side),
     'binding': {'method': 'call'}, 'cfg': PROVIDER_CFG,
     'inputs': lambda base: {'java_file': base / 'app/src/main/java/edu/ksu/cs/benign/FIleContentProvider.java',
                             'manifest': base / 'app/src/main/AndroidManifest.xml'},
     'target': 'FIleContentProvider.call + manifest <provider> 权限属性'},
    {'slot': 'FP-38', 'task': 'FT-038', 'kind': 'BENCHMARK',
     'rule': 'INTENT_EXTRA_UNGUARDED_DEREFERENCE',
     'base': lambda side: _ghera('FP-38', 'ICC/UnhandledException-DOS-Lean', side),
     'binding': {'method': 'onResume'}, 'cfg': EXTRA_CFG,
     'inputs': lambda base: {'java_file': base / 'app/src/main/java/edu/ksu/cs/benign/MainActivity.java'},
     'target': 'MainActivity.onResume（含 onClick 匿名监听）'},
    {'slot': 'FP-48', 'task': 'FT-048', 'kind': 'BENCHMARK',
     'rule': 'EXTERNAL_STORAGE_SENSITIVE_WRITE',
     'base': lambda side: _ghera('FP-48', 'Storage/ExternalStorage-InformationLeak-Lean', side),
     'binding': {'method': 'onResume'}, 'cfg': STORAGE_CFG,
     'inputs': lambda base: {'java_file': base / 'app/src/main/java/edu/ksu/cs/benign/MainActivity.java'},
     'target': 'MainActivity.onResume 文件写入目标目录'},
    {'slot': 'FP-51', 'task': 'FT-051', 'kind': 'BENCHMARK',
     'rule': 'CHECK_CALLING_OR_SELF_PERMISSION_SELF_GRANTED',
     'base': lambda side: _ghera('FP-51', 'System/CheckCallingOrSelfPermission-PrivilegeEscalation-Lean', side),
     'binding': {'method': 'onStartCommand'},
     'cfg': dict(RUNTIME_CFG, runtime_api='checkCallingOrSelfPermission'),
     'inputs': lambda base: {'java_file': base / 'app/src/main/java/edu/ksu/cs/benign/MyService.java',
                             'manifest': base / 'app/src/main/AndroidManifest.xml'},
     'target': 'MyService.onStartCommand + manifest <service>/<permission>'},
    {'slot': 'FP-52', 'task': 'FT-052', 'kind': 'BENCHMARK',
     'rule': 'ENFORCE_CALLING_OR_SELF_PERMISSION_SELF_GRANTED',
     'base': lambda side: _ghera('FP-52', 'System/EnforceCallingOrSelfPermission-PrivilegeEscalation-Lean', side),
     'binding': {'method': 'onStartCommand'},
     'cfg': dict(RUNTIME_CFG, runtime_api='enforceCallingOrSelfPermission'),
     'inputs': lambda base: {'java_file': base / 'app/src/main/java/edu/ksu/cs/benign/MyService.java',
                             'manifest': base / 'app/src/main/AndroidManifest.xml'},
     'target': 'MyService.onStartCommand + manifest <service>/<permission>'},
    {'slot': 'FP-53', 'task': 'FT-053', 'kind': 'BENCHMARK',
     'rule': 'CLIPBOARD_SENSITIVE_PRIMARY_CLIP',
     'base': lambda side: _ghera('FP-53', 'System/ClipboardUse-InformationExposure-Lean', side),
     'binding': {'method': 'onResume'}, 'cfg': CLIP_CFG,
     'inputs': lambda base: {'java_file': base / 'app/src/main/java/edu/ksu/cs/benign/MainActivity.java'},
     'target': 'MainActivity.onResume（含 onClick）setPrimaryClip 内容来源'},
]

CHECKER_SHA = hashlib.sha256(pathlib.Path(rules_b3.__file__).read_bytes()).hexdigest()


def run_pairs():
    outdir = V5 / 'runs' / FAMILY
    outdir.mkdir(parents=True, exist_ok=True)
    rows = []
    for pair in PAIRS:
        for side in ('buggy', 'fixed'):
            base = pair['base'](side)
            inputs = pair['inputs'](base)
            if 'source_root' in inputs:
                inputs['source_tree_sha256'] = tree_sha(inputs['source_root'])
            binding = dict(pair['binding'])
            if 'source_root' in inputs:
                binding['source_root'] = str(inputs['source_root'])
            start = time.perf_counter()
            try:
                result = rules_b3.verify(pair['rule'], inputs, binding, pair['cfg'])
                exit_status = 0
            except Exception as e:
                result = {'observation': 'UNKNOWN', 'scope': pair['rule'], 'evidence': [],
                          'reason': 'CHECKER_CRASH:' + repr(e), 'duration_s': 0.0}
                exit_status = 1
            dur = time.perf_counter() - start
            hashes = {}
            for k, v in inputs.items():
                if isinstance(v, pathlib.Path) and pathlib.Path(v).is_file():
                    hashes[k] = sha(v)
                elif k == 'source_tree_sha256':
                    hashes['source_tree'] = v
            receipt = {
                'pair_slot': pair['slot'], 'task_id': pair['task'], 'side': side,
                'kind': pair['kind'], 'family': FAMILY, 'rule_id': pair['rule'],
                'rule_version': RULE_VERSION, 'binding': binding, 'rule_config': pair['cfg'],
                'observation': result['observation'], 'scope': result['scope'],
                'reason': result['reason'], 'evidence': result['evidence'],
                'input_sha256': hashes,
                'command': [sys.executable, str(V5 / 'src/helpers_b3.py'), 'run-pairs'],
                'exit_status': exit_status, 'duration_s': round(dur, 4),
                'checker': 'rules_b3.verify', 'checker_sha256': CHECKER_SHA,
                'method': 'B4 v2加目标规则补正',
                'scoring_reference_read_by_checker': False,
            }
            (outdir / ('%s-%s.json' % (pair['slot'], side))).write_text(
                json.dumps(receipt, ensure_ascii=False, indent=2))
            rows.append({'pair_slot': pair['slot'], 'side': side, 'rule_id': pair['rule'],
                         'observation': result['observation'], 'reason': result['reason'],
                         'duration_s': round(dur, 4), 'exit_status': exit_status})
            print(pair['slot'], side, pair['rule'], result['observation'], result['reason'],
                  '%.3fs' % dur)
    (outdir / 'sides.jsonl').write_text(
        '\n'.join(json.dumps(r, ensure_ascii=False) for r in rows) + '\n')


# -------------------------------------------------------------------- scoring
def score():
    refs = {c['pair_slot']: c['reference']
            for c in map(json.loads, CONTRACTS.read_text().splitlines())}
    v3 = {r['pair_slot']: r for r in csv.DictReader(V3.open())}
    evidence_scope = {
        'FP-11': ('defect_itself', '覆盖不变量即目标缺陷机制：每个需口令保护界面经自身或基类/mixin '
                                   'onResume 应用 FLAG_SECURE；未覆盖界面即截屏泄露面。'),
        'FP-37': ('defect_itself', 'provider 整体权限缺失使导出 provider 的 call() 数据操作可被任意应用触发；'
                                   'read/writePermission 不作用于 call 入口。'),
        'FP-38': ('defect_itself', 'extra 派生值在组件入口路径被解引用且无 null 分支/NPE 捕获，'
                                   '即外部 extra 触发的未捕获 NPE（DoS）。'),
        'FP-48': ('defect_itself', '敏感数据写入 getExternalFilesDir 外部目录，应用失去文件访问控制。'),
        'FP-51': ('defect_itself', '应用自持该权限（非 signature 保护级 + uses-permission）使 '
                                   'checkCallingOrSelfPermission 对外部调用方恒通过，且 service 无系统级权限。'),
        'FP-52': ('defect_itself', 'enforceCallingOrSelfPermission 同样受“调用方或自身”语义支配，'
                                   '自身持有普通权限时外部调用方不被拦截；service 无系统级权限。'),
        'FP-53': ('defect_itself', 'setPrimaryClip 的值来自敏感 EditText/本地读取方法，写入全设备可读剪贴板。'),
    }
    rows = []
    for pair in PAIRS:
        slot = pair['slot']
        obs, receipts, reasons = {}, {}, {}
        for side in ('buggy', 'fixed'):
            rec = json.loads((V5 / 'runs' / FAMILY / ('%s-%s.json' % (slot, side))).read_text())
            obs[side] = rec['observation']
            reasons[side] = rec['reason']
            receipts[side] = 'runs/%s/%s-%s.json' % (FAMILY, slot, side)
        ref = refs[slot]
        scope, why = evidence_scope[slot]
        unknown = 'UNKNOWN' in (obs['buggy'], obs['fixed'])
        agrees = obs['buggy'] == ref['buggy'] and obs['fixed'] == ref['fixed']
        if scope != 'defect_itself':
            cls = 'PROPERTY_SUPPORT'
        elif unknown:
            cls = 'UNRESOLVED'
        elif agrees:
            cls = 'MATCHED'
        else:
            cls = 'MISMATCHED'
        rows.append({'pair_slot': slot, 'task_id': pair['task'], 'kind': pair['kind'],
                     'project': 'signalapp/Signal-Android' if pair['kind'] == 'REAL' else 'Ghera-benchmark',
                     '原Top1': None, 'rule_id': pair['rule'],
                     'obs_buggy': obs['buggy'], 'obs_fixed': obs['fixed'],
                     'reference_buggy': ref['buggy'], 'reference_fixed': ref['fixed'],
                     'result_class': cls, 'result_class_v3': v3[slot]['result_class'],
                     'is_new_success': cls == 'MATCHED' and v3[slot]['result_class'] != 'MATCHED',
                     'evidence_scope': scope, 'evidence_scope_reason': why,
                     'reason_buggy': reasons['buggy'], 'reason_fixed': reasons['fixed'],
                     'receipts': receipts})
    align = {r['pair_slot']: r for r in csv.DictReader((V5 / 'data/alignment_43.csv').open())}
    targets = {p['slot']: p['target'] for p in PAIRS}
    frag = V5 / 'data' / 'alignment_fragments'
    frag.mkdir(parents=True, exist_ok=True)
    status_text = {'MATCHED': 'B3完成(MATCHED,双侧观测与参考一致)',
                   'UNRESOLVED': 'B3未决(UNRESOLVED)',
                   'MISMATCHED': 'B3不一致(MISMATCHED)',
                   'PROPERTY_SUPPORT': 'B3仅相关属性(PROPERTY_SUPPORT,不计成功)',
                   'NOT_APPLICABLE': 'B3不适用(NOT_APPLICABLE)'}
    with (frag / 'B3.csv').open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=['pair_slot', 'task_id', 'kind', 'project', '原Top1',
                                          '补正规则', '目标文件/方法/组件', '对应理由',
                                          '公开来源', '目标绑定版本', '实现状态'])
        w.writeheader()
        for row in rows:
            base = align[row['pair_slot']]
            w.writerow({
                'pair_slot': row['pair_slot'], 'task_id': row['task_id'],
                'kind': row['kind'], 'project': row['project'],
                '原Top1': base['原Top1'], '补正规则': row['rule_id'],
                '目标文件/方法/组件': targets[row['pair_slot']],
                '对应理由': ('%s 原Top1=%s 与目标命题不对应；%s'
                             % (row['rule_id'], base['原Top1'], row['evidence_scope_reason'])),
                '公开来源': 'FT-%s公开任务描述;快照源码(%s)' % (
                    row['task_id'].split('-')[1], row['project']),
                '目标绑定版本': 'v5.binding.b3',
                '实现状态': status_text[row['result_class']],
            })
    report = {
        'version': 'exp3_rule_alignment_v5', 'family': FAMILY, 'batch': 'B3',
        'method': 'B4 v2加目标规则补正', 'date': '2026-10-17',
        'rule_version': RULE_VERSION,
        'pairs': {r['pair_slot']: {
            'rule_id': r['rule_id'], 'result_class': r['result_class'],
            'obs': [r['obs_buggy'], r['obs_fixed']],
            'reference': [r['reference_buggy'], r['reference_fixed']],
            'external_evidence_scope': r['evidence_scope'],
            'is_new_success': r['is_new_success'], 'kind': r['kind'],
            'receipts': r['receipts']} for r in rows},
        'summary': {
            'matched': sum(r['result_class'] == 'MATCHED' for r in rows),
            'unresolved': sum(r['result_class'] == 'UNRESOLVED' for r in rows),
            'mismatched': sum(r['result_class'] == 'MISMATCHED' for r in rows),
            'property_support': sum(r['result_class'] == 'PROPERTY_SUPPORT' for r in rows),
            'not_applicable': sum(r['result_class'] == 'NOT_APPLICABLE' for r in rows),
            'new_successes': sum(r['is_new_success'] for r in rows),
            'new_real_successes': sum(r['is_new_success'] and r['kind'] == 'REAL' for r in rows),
            'matched_slots': [r['pair_slot'] for r in rows if r['result_class'] == 'MATCHED'],
        },
        'counterexamples': json.loads((V5 / 'checks/b3_counterexamples.json').read_text()),
        'scoring_reference_read_at': 'scoring phase only (helpers_b3.score)',
        'checkers_receive_expected_answer': False,
        'note': 'FP-51/52 审计文本写“未判断返回值”，但公开 Benign 源码实际判断了返回值；'
                '缺陷来自应用自持默认保护级权限使该运行时自检对外部调用方恒通过（公开任务描述即为该语义），'
                '规则按源码事实实现，不按审计文字。',
    }
    with (V5 / 'runs' / FAMILY / 'pair_results.csv').open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    (V5 / 'progress').mkdir(exist_ok=True)
    (V5 / 'progress/b3_report.json').write_text(json.dumps(report, ensure_ascii=False, indent=2))
    print(json.dumps(report['summary'], ensure_ascii=False, indent=1))
    for r in rows:
        print(r['pair_slot'], r['obs_buggy'], r['obs_fixed'],
              'ref', r['reference_buggy'], r['reference_fixed'], r['result_class'])


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    if cmd == 'counterexamples':
        run_counterexamples()
    elif cmd == 'run-pairs':
        run_pairs()
    elif cmd == 'score':
        score()
    else:
        raise SystemExit('usage: helpers_b3.py {counterexamples|run-pairs|score}')
