"""Run complete reviewed direct-getter acceptance without update/skip flags."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('direct_accept_review', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
gate, support = review.gate, review.support
work = Path(sys.argv[1]).resolve()
review.review(work)
record = json.loads((work / 'REVIEW.json').read_text())
if record['full_acceptance'] is not False:
    raise ValueError('preparation/review confused with acceptance')
for name, digest in record['tools_sha256'].items():
    if support.sha((HERE / name).read_bytes()) != digest:
        raise ValueError('review tool drift')
for name, digest in record['evidence_sha256'].items():
    if support.sha((work / name).read_bytes()) != digest:
        raise ValueError('reviewed terminal/object evidence drift')
before = support.inputs.fingerprint(work / 'Coq', work)
if before != record['candidate_input_sha256']:
    raise ValueError('reviewed direct-getter source drift')
command = ['bash', 'check-jets.sh', '--accept']
launch = {'candidate': str(work), 'command': command, 'audit_input_sha256': before,
          'review_sha256': support.sha((work / 'REVIEW.json').read_bytes()),
          'driver_sha256': support.sha(Path(__file__).read_bytes()),
          'log': str(work / 'acceptance.log'), 'full_acceptance': False}
gate.write(work / 'AUDIT-RUN.json', launch)
gate.write(HERE / 'AUDIT-RUN.json', launch)
start = time.monotonic()
with (work / 'acceptance.log').open('wb') as output:
    result = subprocess.run(command, cwd=work / 'Coq', env=dict(support.ENV, JOBS='2'),
                            stdout=output, stderr=subprocess.STDOUT, timeout=10800)
terminal = {**launch, 'exit_code': result.returncode, 'seconds': time.monotonic() - start,
            'log_sha256': support.sha((work / 'acceptance.log').read_bytes())}
gate.write(work / 'TERMINAL.json', terminal)
gate.write(HERE / 'TERMINAL.json', terminal)
if result.returncode:
    raise ValueError('direct-getter acceptance failed; see ' + str(work / 'acceptance.log'))
marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
if not (work / 'acceptance.log').read_text().rstrip().endswith(marker):
    raise ValueError('missing full acceptance marker')
if support.inputs.fingerprint(work / 'Coq', work) != before:
    raise ValueError('candidate source changed during acceptance')
review.review(work)
terminal.update(full_acceptance=True, coverage='371/533')
gate.write(work / 'ACCEPTANCE.json', terminal)
gate.write(HERE / 'ACCEPTANCE.json', terminal)
print('Full isolated direct-getter acceptance passed: 371/533; main unchanged', flush=True)
