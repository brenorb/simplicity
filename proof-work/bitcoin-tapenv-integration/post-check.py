"""Check an accepted getter baseline plus the exact caller-support additions."""
import importlib.util
import json
from pathlib import Path
import subprocess
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('tapenv_post',HERE/'review.py')
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)


def check():
    meta=json.loads((HERE/'ASSEMBLY.json').read_text());installed=json.loads((HERE/'INSTALLATION.json').read_text())
    receipt=json.loads((HERE/'REVIEW.json').read_text());work=Path(meta['candidate'])
    result,files=gate.review(work)
    if not installed['main_installation'] or installed['normal_registration']:raise ValueError('installation scope changed')
    for path,text in files.items():
        if path.read_text()!=text:raise ValueError('imported caller source drift')
    for path,value in receipt['evidence_sha256'].items():
        if gate.stage.patch.sha((work/path).read_bytes())!=value:raise ValueError('caller proof evidence drift')
    accepted=json.loads((HERE.parent/'elements-getters-integration/ACCEPTANCE.json').read_text());log=Path(accepted['log'])
    if accepted['exit_code'] or not accepted['full_main_acceptance'] or gate.stage.patch.sha(log.read_bytes())!=accepted['log_sha256']:
        raise ValueError('getter baseline receipt drift')
    spec=importlib.util.spec_from_file_location('tapenv_post_inputs',gate.stage.REPO/'Coq/jet-audit-inputs.py')
    inputs=importlib.util.module_from_spec(spec);spec.loader.exec_module(inputs)
    root=(gate.stage.REPO/'Coq').resolve();added={p.resolve() for p in files};original=Path.rglob
    def rglob(self,pattern):
        paths=original(self,pattern)
        return (p for p in paths if p.resolve() not in added) if self.resolve()==root else paths
    with patch.object(Path,'rglob',rglob):previous=inputs.fingerprint(root,gate.stage.REPO)
    if previous!=accepted['audit_input_sha256']:raise ValueError('changes beyond the exact checked caller support')
    staged=gate.stage.patch.sha(subprocess.check_output(['git','diff','--cached','--binary'],cwd=gate.stage.REPO))
    if staged!=installed['preexisting_staged_patch_sha256'] or staged!=accepted['preexisting_staged_patch_sha256']:
        raise ValueError('original index changed')
    print(json.dumps({'historical_getters_full_acceptance':True,'builder_independent_kernel_check':True,
                      'only_checked_additive_delta':True,'index_preserved':True,'coverage':'364/533',
                      'current_whole_worktree_full_acceptance':False,'current_input_sha256':inputs.fingerprint(root,gate.stage.REPO)},indent=2))


if __name__=='__main__':check()
