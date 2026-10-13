"""Read-only post-installation and, when present, terminal acceptance checks."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check():
    installed = json.loads((HERE / 'INSTALLATION.json').read_text())
    prepared = json.loads((HERE / 'PREPARATION.json').read_text())
    meta = json.loads((HERE / 'ASSEMBLY.json').read_text())
    run = json.loads((HERE / 'AUDIT-RUN.json').read_text())
    if not installed['main_installation'] or installed['full_acceptance']:
        raise ValueError('installation receipt confused with acceptance')
    for name, value in prepared['snapshots_sha256'].items():
        if sha(REPO / 'Coq' / name) != value:
            raise ValueError('installed registry/snapshot drift: ' + name)
    for name, value in meta['source_sha256'].items():
        if sha(REPO / name) != value:
            raise ValueError('nullable source drift')
    for name, value in meta['main_index_sha256'].items():
        data = subprocess.check_output(['git', 'show', ':Coq/' + name], cwd=REPO)
        if hashlib.sha256(data).hexdigest() != value:
            raise ValueError('preexisting staging changed')
    data = subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)
    if hashlib.sha256(data).hexdigest() != meta['main_staged_patch_sha256']:
        raise ValueError('preexisting staged patch changed')
    spec = importlib.util.spec_from_file_location('nullable_post_inputs', REPO / 'Coq/jet-audit-inputs.py')
    inputs = importlib.util.module_from_spec(spec); spec.loader.exec_module(inputs)
    if inputs.fingerprint(REPO / 'Coq', REPO) != run['audit_input_sha256']:
        raise ValueError('audit input changed after launch')
    terminal = HERE / 'ACCEPTANCE.json'
    accepted = False
    if terminal.exists():
        receipt = json.loads(terminal.read_text())
        if receipt['exit_code'] != 0 or receipt['audit_input_sha256'] != run['audit_input_sha256']:
            raise ValueError('invalid terminal acceptance')
        if sha(Path(receipt['log'])) != receipt['log_sha256']:
            raise ValueError('acceptance log drift')
        candidate = Path(meta['candidate'])
        for name, field in [('new_contracts.v', 'new_deep_driver_sha256'),
                            ('new_contracts.out', 'new_deep_report_sha256')]:
            if sha(candidate / name) != receipt[field]:
                raise ValueError('fully expanded nullable record evidence drift')
        text = Path(receipt['log']).read_text()
        if not text.rstrip().endswith('all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, four ASTs)'):
            raise ValueError('incomplete acceptance log')
        accepted = True
    result = {'main_installation': True, 'index_preserved': True,
              'reviewed_snapshots_match': True, 'audit_inputs_frozen': True,
              'coverage': '361/533', 'coverage_added': 0, 'full_main_acceptance': accepted}
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    check()
