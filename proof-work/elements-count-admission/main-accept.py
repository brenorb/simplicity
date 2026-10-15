"""Complete actual-main acceptance after the reviewed source-only installation."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('count_main_accept_precheck', HERE / 'post-check.py')
post = importlib.util.module_from_spec(spec)
spec.loader.exec_module(post)
post.check()
gate = post.gate
ledger = json.loads((HERE / 'INSTALLATION.json').read_text())
work = Path(ledger['candidate'])
fingerprint = gate.support.inputs.fingerprint(gate.MAIN, gate.REPO)
command = ['bash', 'check-jets.sh', '--accept']
log = work / 'main-acceptance.log'
launch = {'command': command, 'log': str(log), 'audit_input_sha256': fingerprint,
          'actual_main_acceptance': False}
gate.write(HERE / 'MAIN-AUDIT-RUN.json', launch)
start = time.monotonic()
with log.open('wb') as output:
    result = subprocess.run(command, cwd=gate.MAIN, env=dict(gate.support.ENV, JOBS='2'),
                            stdout=output, stderr=subprocess.STDOUT, timeout=10800)
terminal = {**launch, 'exit_code': result.returncode, 'seconds': time.monotonic() - start,
            'log_sha256': gate.support.sha(log.read_bytes())}
gate.write(HERE / 'MAIN-TERMINAL.json', terminal)
if result.returncode:
    raise ValueError('actual-main acceptance failed; inspect ' + str(log))
marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
if not log.read_text().rstrip().endswith(marker):
    raise ValueError('incomplete main acceptance log')
if gate.support.inputs.fingerprint(gate.MAIN, gate.REPO) != fingerprint:
    raise ValueError('main inputs changed during acceptance')
post.check()
terminal['actual_main_acceptance'] = True
gate.write(HERE / 'MAIN-ACCEPTANCE.json', terminal)
post.check()
