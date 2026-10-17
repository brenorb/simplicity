"""Bind a forced local-source build to every project object loaded by its roots.

This supplements, never replaces, full contracts/assumptions and coqchk. The
candidate must already have an independently recorded successful make -B run.
No cached object without a corresponding COQC line is accepted as source-built.
"""
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('forced_closure_support', HERE / 'elements-count/support.py')
s = importlib.util.module_from_spec(sp)
sp.loader.exec_module(s)


def objects(work, expected):
    for name, row in expected.items():
        p = work / 'Coq' / name
        if (s.sha(p.read_bytes()) != row['source_sha256'] or
                s.sha(p.with_suffix('.vo').read_bytes()) != row['object_sha256']):
            raise ValueError('source/object changed: ' + name)


def snapshot(folder, roots):
    if (folder / 'SOURCE-CLOSURE.json').exists():
        raise ValueError('source-closure receipt already exists')
    receipt = folder / 'RUN.json'
    r = json.loads(receipt.read_text())
    work = Path(r['candidate'])
    if not r.get('force_rebuilt_entire_local_closure'):
        raise ValueError('explicit forced-rebuild provenance required')
    build = r['commands']['build']
    if build['exit_code'] != 0 or '-B' not in build['command']:
        raise ValueError('successful make -B required')
    log = (folder / 'build.log').read_bytes()
    if s.sha(log) != build['log_sha256']:
        raise ValueError('forced build log differs')
    compiled = re.findall(r'^COQC (\S+\.v)$', log.decode(), re.M)
    if not compiled or len(compiled) != len(set(compiled)):
        raise ValueError('missing or duplicate local compilation trace')
    if any(not re.fullmatch(r'[A-Za-z_][\w]*(?:\.[A-Za-z_][\w]*)+', m) for m in roots):
        raise ValueError('invalid root module')
    before, index = s.input_map(), s.index_hash()
    if before != r['main_inputs'] or index != r['staged_patch_sha256']:
        raise ValueError('current inputs or staging differ')
    command = ['bash', 'build-jets.sh', '--coqtop', '-quiet']
    result = subprocess.run(command, input='Require ' + ' '.join(roots) + '.\nPrint Libraries.\n',
        cwd=work / 'Coq', env=s.ENV, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=60)
    if result.returncode or re.search(r'(?m)^(?:Error|Anomaly):', result.stdout):
        raise ValueError('cannot inspect loaded libraries')
    modules = re.findall(r'^  ((?:C|Simplicity|Util)\.[A-Za-z0-9_.]+)$', result.stdout, re.M)
    loaded = {m.replace('.', '/') + '.v' for m in modules}
    if not loaded or not set(m.replace('.', '/') + '.v' for m in roots) <= loaded:
        raise ValueError('incomplete root/library inventory')
    if loaded != set(compiled):
        raise ValueError('forced/local-loaded closure differs: ' + repr({
            'not_recompiled': sorted(loaded - set(compiled)),
            'not_loaded': sorted(set(compiled) - loaded)}))
    bound = {name: {'source_sha256': s.sha((work / 'Coq' / name).read_bytes()),
                   'object_sha256': s.sha((work / 'Coq' / name).with_suffix('.vo').read_bytes())}
             for name in sorted(loaded)}
    if s.input_map() != before or s.index_hash() != index:
        raise ValueError('library inspection changed inputs/index')
    out = dict(candidate=str(work), roots=roots, local_module_count=len(bound),
        forced_build=build, compile_sha256=s.sha(receipt.read_bytes()),
        compiled_and_loaded_local_modules=bound, original_inputs_sha256=s.sha(json.dumps(before, sort_keys=True).encode()),
        staged_patch_sha256=index, tool_sha256=s.sha(Path(__file__).read_bytes()),
        library_query=dict(command=command, exit_code=result.returncode,
                           log_sha256=s.sha(result.stdout.encode())),
        recursive_kernel_check=False, normal_acceptance=False, coverage_added=0)
    s.changed({folder / 'SOURCE-CLOSURE.json': json.dumps(out, indent=2) + '\n',
               folder / 'loaded-libraries.log': result.stdout})
    print('Bound all ' + str(len(bound)) + ' loaded local sources/objects to successful forced compilation', flush=True)


def kernel(folder):
    if (folder / 'SOURCE-KERNEL-RUN.json').exists():
        raise ValueError('source-bound kernel already launched; inspect original process')
    r = json.loads((folder / 'SOURCE-CLOSURE.json').read_text())
    work = Path(r['candidate'])
    objects(work, r['compiled_and_loaded_local_modules'])
    if (s.sha((folder / 'RUN.json').read_bytes()) != r['compile_sha256'] or
            r['tool_sha256'] != s.sha(Path(__file__).read_bytes()) or
            r['staged_patch_sha256'] != s.index_hash()):
        raise ValueError('source-closure identity differs')
    before = s.input_map()
    command = [sys.executable, '-B', str(folder / 'verify.py'), 'kernel', str(work)]
    launch = dict(command=command, source_closure_sha256=s.sha((folder / 'SOURCE-CLOSURE.json').read_bytes()),
                  recursive_kernel_check=False)
    s.changed({folder / 'SOURCE-KERNEL-RUN.json': json.dumps(launch, indent=2) + '\n'})
    result = subprocess.run(command, cwd=s.REPO, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=4000)
    s.changed({folder / 'source-kernel-driver.log': result.stdout.decode()})
    if result.returncode:
        raise ValueError('source-bound kernel failed; preserve terminal and inspect log')
    checked = json.loads((folder / 'CHECKED.json').read_text())
    if not checked['recursive_kernel_check']:
        raise ValueError('no successful recursive kernel receipt')
    objects(work, r['compiled_and_loaded_local_modules'])
    if s.input_map() != before or r['staged_patch_sha256'] != s.index_hash():
        raise ValueError('source-bound kernel changed inputs/index')
    r.update(recursive_kernel_check=True, kernel_checked_sha256=s.sha((folder / 'CHECKED.json').read_bytes()),
             source_kernel_launch_sha256=s.sha((folder / 'SOURCE-KERNEL-RUN.json').read_bytes()),
             driver_exit_code=result.returncode, driver_log_sha256=s.sha(result.stdout))
    s.changed({folder / 'SOURCE-CHECKED.json': json.dumps(r, indent=2) + '\n'})
    print('Complete forced-source local closure recursively kernel-checked', flush=True)


if __name__ == '__main__':
    if len(sys.argv) >= 4 and sys.argv[1] == 'snapshot':
        snapshot(Path(sys.argv[2]).resolve(), sys.argv[3:])
    elif len(sys.argv) == 3 and sys.argv[1] == 'kernel':
        kernel(Path(sys.argv[2]).resolve())
    else:
        raise ValueError('usage: verify-forced-closure.py snapshot FOLDER ROOT... | kernel FOLDER')
