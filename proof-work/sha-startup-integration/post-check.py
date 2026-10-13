"""Verify the historical accepted baseline plus exactly the SHA additions.

The current worktree has two separate verification receipts, not one new
repository-wide --accept receipt. No normal audit input filter is modified.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('startup_post_review', HERE / 'review.py')
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)


def check():
    meta = json.loads((HERE / 'ASSEMBLY.json').read_text())
    installed = json.loads((HERE / 'INSTALLATION.json').read_text())
    terminal = json.loads((HERE / 'REVIEW.json').read_text())
    candidate = Path(meta['candidate']).resolve()
    result, sources = gate.review(candidate)
    if not installed['main_installation'] or installed['normal_registry_admission'] or installed['coverage_added']:
        raise ValueError('startup installation scope drift')
    for target, content in sources.items():
        if target.read_text() != content: raise ValueError('installed SHA source drift')
    for name, value in terminal['evidence_sha256'].items():
        if gate.stage.patch.sha((candidate / name).read_bytes()) != value:
            raise ValueError('fresh SHA proof evidence drift')
    version = HERE.parent / 'elements-version-admission'
    accepted = json.loads((version / 'ACCEPTANCE.json').read_text())
    log = Path(accepted['log'])
    if (accepted['exit_code'] or not accepted['full_main_acceptance']
            or gate.stage.patch.sha(log.read_bytes()) != accepted['log_sha256']
            or not log.read_text().rstrip().endswith('all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)')):
        raise ValueError('historical Version acceptance evidence drift')
    inputs = gate.stage.load('startup_post_inputs', gate.stage.REPO / 'Coq/jet-audit-inputs.py')
    original = Path.rglob
    coq = (gate.stage.REPO / 'Coq').resolve()
    new_paths = {p.resolve() for p in sources}
    # Reconstruct the historical input list only for this post-check, after
    # verifying all excluded files are the exact independently checked import.
    def rglob(self, pattern):
        paths = original(self, pattern)
        return (p for p in paths if p.resolve() not in new_paths) if self.resolve() == coq else paths
    with patch.object(Path, 'rglob', rglob):
        previous = inputs.fingerprint(coq, gate.stage.REPO)
    if previous != accepted['audit_input_sha256']:
        raise ValueError('inputs changed beyond the thirteen checked SHA additions')
    staged = gate.stage.patch.sha(subprocess.check_output(['git', 'diff', '--cached', '--binary'], cwd=gate.stage.REPO))
    if staged != accepted['preexisting_staged_patch_sha256'] or staged != installed['preexisting_staged_patch_sha256']:
        raise ValueError('original staging changed')
    print(json.dumps({'historical_Version_full_acceptance': True, 'SHA_independent_kernel_check': True,
                      'only_checked_additive_source_delta': True, 'index_preserved': True,
                      'current_input_sha256': inputs.fingerprint(coq, gate.stage.REPO),
                      'current_whole_worktree_full_acceptance': False, 'coverage': '362/533'}, indent=2))


if __name__ == '__main__': check()
