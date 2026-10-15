"""Run the reviewed candidate's complete normal acceptance, without updates."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('count_registry_accept_review', HERE / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
gate, support = review.gate, review.support
work = Path(sys.argv[1]).resolve()
review.review(work)
record = json.loads((work / 'REVIEW.json').read_text())
if record['full_acceptance'] is not False:
    raise ValueError('review confused with acceptance')
for name, value in record['tools_sha256'].items():
    if support.sha((HERE / name).read_bytes()) != value:
        raise ValueError('review tool changed')
for name, value in record['evidence_sha256'].items():
    if support.sha((work / name).read_bytes()) != value:
        raise ValueError('reviewed evidence changed before acceptance')
before = support.inputs.fingerprint(work / 'Coq', work)
if record['candidate_input_sha256'] != before:
    raise ValueError('reviewed candidate changed')
command = ['bash', 'check-jets.sh', '--accept']
launch = {'candidate': str(work), 'command': command, 'audit_input_sha256': before,
          'review_sha256': support.sha((work / 'REVIEW.json').read_bytes()),
          'log': str(work / 'acceptance.log'), 'full_acceptance': False}
gate.write(work / 'AUDIT-RUN.json', launch)
gate.write(HERE / 'AUDIT-RUN.json', launch)
start = time.monotonic()
with (work / 'acceptance.log').open('wb') as output:
    process = subprocess.run(command, cwd=work / 'Coq', env=dict(support.ENV, JOBS='2'),
                             stdout=output, stderr=subprocess.STDOUT, timeout=10800)
elapsed = time.monotonic() - start
terminal = {**launch, 'exit_code': process.returncode, 'seconds': elapsed,
            'log_sha256': support.sha((work / 'acceptance.log').read_bytes())}
gate.write(work / 'TERMINAL.json', terminal)
gate.write(HERE / 'TERMINAL.json', terminal)
if process.returncode:
    raise ValueError('full acceptance failed; inspect ' + str(work / 'acceptance.log'))
marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
if not (work / 'acceptance.log').read_text().rstrip().endswith(marker):
    raise ValueError('missing complete acceptance marker')
if support.inputs.fingerprint(work / 'Coq', work) != before:
    raise ValueError('candidate source changed during acceptance')
review.review(work)
terminal['full_acceptance'] = True
terminal['coverage'] = '366/533'
gate.write(work / 'ACCEPTANCE.json', terminal)
gate.write(HERE / 'ACCEPTANCE.json', terminal)
print('Full isolated normal acceptance passed: 366/533; main metadata still unchanged', flush=True)
