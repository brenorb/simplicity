"""Check installed getter snapshots/index and a terminal normal receipt."""
import importlib.util
import json
from pathlib import Path
import subprocess

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('getter_post',HERE/'admission.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)


def check():
    run=json.loads((HERE/'AUDIT-RUN.json').read_text());installed=json.loads((HERE/'INSTALLATION.json').read_text())
    meta=json.loads((HERE/'ASSEMBLY.json').read_text())
    gate.provenance()
    for path,value in installed['snapshots_sha256'].items():
        if gate.base.patch.sha((gate.base.MAIN/path).read_bytes())!=value:raise ValueError('getter registry/snapshot drift')
    if gate.base.patch.sha(subprocess.check_output(['git','diff','--cached','--binary'],cwd=gate.REPO))!=meta['main_staged_patch_sha256']:
        raise ValueError('original staged patch changed')
    inputs=gate.base.load('getter_post_inputs',gate.base.MAIN/'jet-audit-inputs.py')
    if inputs.fingerprint(gate.base.MAIN,gate.REPO)!=run['audit_input_sha256']:raise ValueError('main audit inputs changed')
    accepted=False
    if (HERE/'ACCEPTANCE.json').exists():
        terminal=json.loads((HERE/'ACCEPTANCE.json').read_text());log=Path(terminal['log'])
        if terminal['exit_code'] or terminal['audit_input_sha256']!=run['audit_input_sha256']:
            raise ValueError('nonterminal/changed receipt')
        if gate.base.patch.sha(log.read_bytes())!=terminal['log_sha256'] or not log.read_text().rstrip().endswith(
                'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'):
            raise ValueError('incomplete full acceptance log')
        accepted=True
    print(json.dumps({'index_preserved':True,'inputs_frozen':True,'coverage':'364/533','full_main_acceptance':accepted},indent=2))
    return accepted


if __name__=='__main__':check()
