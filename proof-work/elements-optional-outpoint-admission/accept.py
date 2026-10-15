"""Accept the eleven-getter candidate only after its predecessor is accepted/installed."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
PRED = HERE.parent / 'elements-digest-getters-admission'
spec = importlib.util.spec_from_file_location('digest_accept_review', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
gate, support = review.gate, review.support
work = Path(sys.argv[1]).resolve()
if not (PRED / 'ACCEPTANCE.json').exists() or not (PRED / 'INSTALLATION.json').exists():
    raise ValueError('predecessor full acceptance and guarded source installation must complete before this audit starts')
post = support.load('digest_accept_predecessor_postcheck', PRED / 'post-check.py')
state = post.check()
if (state['coverage'] != '386/533' or state['staged_patch_preserved'] is not True or
        state['source_identical_to_accepted_candidate'] is not True or
        support.inputs.fingerprint(gate.MAIN, gate.REPO) != gate.PRED_REVIEW['candidate_input_sha256']):
    raise ValueError('installed predecessor/source/index is not verified')
review.review(work)
r = json.loads((work / 'REVIEW.json').read_text())
if r['full_acceptance'] is not False or r['review']['coverage_added'] != 11:
    raise ValueError('review confused with full acceptance')
for n, h in r['tools_sha256'].items():
    if support.sha((HERE / n).read_bytes()) != h:
        raise ValueError('review tool drift')
for n, h in r['evidence_sha256'].items():
    if support.sha((work / n).read_bytes()) != h:
        raise ValueError('reviewed terminal/object evidence drift')
before = support.inputs.fingerprint(work / 'Coq', work)
if before != r['candidate_input_sha256']:
    raise ValueError('reviewed eleven-getter source changed')
if (work / 'AUDIT-RUN.json').exists():
    raise ValueError('audit already launched; inspect the existing handle/terminal evidence')
command = ['bash', 'check-jets.sh', '--accept']
launch = {'candidate': str(work), 'command': command, 'audit_input_sha256': before,
          'review_sha256': support.sha((work / 'REVIEW.json').read_bytes()), 'driver_sha256': support.sha(Path(__file__).read_bytes()),
          'predecessor_acceptance_sha256': support.sha((PRED / 'ACCEPTANCE.json').read_bytes()),
          'predecessor_installation_sha256': support.sha((PRED / 'INSTALLATION.json').read_bytes()),
          'log': str(work / 'acceptance.log'), 'full_acceptance': False}
gate.write(work / 'AUDIT-RUN.json', launch)
gate.write(HERE / 'AUDIT-RUN.json', launch)
start = time.monotonic()
with (work / 'acceptance.log').open('wb') as output:
    result = subprocess.run(command, cwd=work / 'Coq', env=dict(support.ENV, JOBS='2'), stdout=output, stderr=subprocess.STDOUT, timeout=10800)
terminal = {**launch, 'exit_code': result.returncode, 'seconds': time.monotonic() - start,
            'log_sha256': support.sha((work / 'acceptance.log').read_bytes())}
gate.write(work / 'TERMINAL.json', terminal)
gate.write(HERE / 'TERMINAL.json', terminal)
if result.returncode:
    raise ValueError('eleven-getter acceptance failed; see ' + str(work / 'acceptance.log'))
marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
if not (work / 'acceptance.log').read_text().rstrip().endswith(marker) or support.inputs.fingerprint(work / 'Coq', work) != before:
    raise ValueError('missing full marker or candidate source drift')
review.review(work)
terminal.update(full_acceptance=True, coverage='397/533')
gate.write(work / 'ACCEPTANCE.json', terminal)
gate.write(HERE / 'ACCEPTANCE.json', terminal)
print('Full isolated eleven-getter acceptance passed: 397/533; source-only main installation still required', flush=True)
