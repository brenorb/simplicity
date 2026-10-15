"""Run the reviewed seven-jet candidate's complete unmodified acceptance."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('seven_accept_review', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
gate, support = review.gate, review.support
work = Path(sys.argv[1]).resolve()
review.review(work)
r = json.loads((work / 'REVIEW.json').read_text())
if r['full_acceptance'] is not False or r['review']['coverage_added'] != 7:
    raise ValueError('preparation confused with full acceptance')
for name, digest in r['tools_sha256'].items():
    if support.sha((HERE / name).read_bytes()) != digest:
        raise ValueError('review tool drift')
for name, digest in r['evidence_sha256'].items():
    if support.sha((work / name).read_bytes()) != digest:
        raise ValueError('checked report/object drift')
before = support.inputs.fingerprint(work / 'Coq', work)
if before != r['candidate_input_sha256']:
    raise ValueError('reviewed source changed')
command = ['bash', 'check-jets.sh', '--accept']
launch = {'candidate': str(work), 'command': command, 'audit_input_sha256': before,
          'review_sha256': support.sha((work / 'REVIEW.json').read_bytes()), 'driver_sha256': support.sha(Path(__file__).read_bytes()),
          'log': str(work / 'acceptance.log'), 'full_acceptance': False}
if (work / 'AUDIT-RUN.json').exists():
    raise ValueError('acceptance already launched: inspect its existing handle/terminal evidence')
gate.write(work / 'AUDIT-RUN.json', launch)
gate.write(HERE / 'AUDIT-RUN.json', launch)
start = time.monotonic()
with (work / 'acceptance.log').open('wb') as log:
    result = subprocess.run(command, cwd=work / 'Coq', env=dict(support.ENV, JOBS='2'), stdout=log, stderr=subprocess.STDOUT, timeout=10800)
terminal = {**launch, 'exit_code': result.returncode, 'seconds': time.monotonic() - start,
            'log_sha256': support.sha((work / 'acceptance.log').read_bytes())}
gate.write(work / 'TERMINAL.json', terminal)
gate.write(HERE / 'TERMINAL.json', terminal)
if result.returncode:
    raise ValueError('seven-jet acceptance failed: ' + str(work / 'acceptance.log'))
marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
if not (work / 'acceptance.log').read_text().rstrip().endswith(marker) or support.inputs.fingerprint(work / 'Coq', work) != before:
    raise ValueError('missing full marker or source drift')
review.review(work)
terminal.update(full_acceptance=True, coverage='378/533')
gate.write(work / 'ACCEPTANCE.json', terminal)
gate.write(HERE / 'ACCEPTANCE.json', terminal)
print('Full isolated seven-jet acceptance passed: 378/533; main unchanged', flush=True)
