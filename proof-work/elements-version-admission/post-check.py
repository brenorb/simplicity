"""Verify installed evidence and, if present, the full terminal acceptance."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
spec = importlib.util.spec_from_file_location('version_post', HERE / 'admission.py')
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)


def check():
    installed = json.loads((HERE / 'INSTALLATION.json').read_text())
    meta = json.loads((HERE / 'ASSEMBLY.json').read_text())
    run = json.loads((HERE / 'AUDIT-RUN.json').read_text())
    if not installed['main_installation'] or installed['normal_main_acceptance']:
        raise ValueError('installation confused with acceptance')
    for name, value in installed['snapshots_sha256'].items():
        if gate.patch.sha((REPO / 'Coq' / name).read_bytes()) != value:
            raise ValueError('installed snapshot drift: ' + name)
    gate.provenance()
    for name, value in meta['main_index_sha256'].items():
        if gate.patch.sha(subprocess.check_output(['git', 'show', ':Coq/' + name], cwd=REPO)) != value:
            raise ValueError('original index changed')
    if gate.patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=REPO)) != meta['main_staged_patch_sha256']:
        raise ValueError('original staged patch changed')
    inputs = gate.load('version_post_inputs', REPO / 'Coq/jet-audit-inputs.py')
    if inputs.fingerprint(REPO / 'Coq', REPO) != run['audit_input_sha256']:
        raise ValueError('audit inputs changed')
    accepted = False
    if (HERE / 'ACCEPTANCE.json').exists():
        receipt = json.loads((HERE / 'ACCEPTANCE.json').read_text())
        if receipt['exit_code'] != 0 or receipt['audit_input_sha256'] != run['audit_input_sha256']:
            raise ValueError('nonterminal/changed acceptance')
        log = Path(receipt['log'])
        if gate.patch.sha(log.read_bytes()) != receipt['log_sha256'] or not log.read_text().rstrip().endswith(
                'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'):
            raise ValueError('incomplete or changed acceptance log')
        for name, value in receipt['fresh_evidence_sha256'].items():
            if gate.patch.sha((Path(meta['candidate']) / name).read_bytes()) != value:
                raise ValueError('fresh closure evidence drift')
        accepted = True
    result = {'coverage': '362/533', 'new_jet': 'simplicity_version', 'index_preserved': True,
              'inputs_frozen': True, 'normal_main_acceptance': accepted}
    print(json.dumps(result, indent=2))
    return result


if __name__ == '__main__':
    check()
