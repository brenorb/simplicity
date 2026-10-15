"""Once-only actual-main 402 acceptance after guarded source integration."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_actual_main', HERE / 'integration.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)


def main():
    if (HERE / 'MAIN-AUDIT-RUN.json').exists():
        raise ValueError('actual-main audit already launched; inspect its existing handle/terminal receipt')
    if g.check()['actual_main_acceptance'] is not False:
        raise ValueError('actual-main 402 was already accepted')
    ledger = g.read(HERE / 'INSTALLATION.json')
    work = Path(ledger['candidate'])
    fingerprint = g.s.inputs.fingerprint(g.g.MAIN, g.g.REPO)
    log = work / 'main-acceptance.log'
    launch = dict(command=g.COMMAND, log=str(log), audit_input_sha256=fingerprint,
        installation_sha256=g.s.sha((HERE / 'INSTALLATION.json').read_bytes()),
        driver_sha256=g.s.sha(Path(__file__).read_bytes()), actual_main_acceptance=False)
    g.s.changed({HERE / 'MAIN-AUDIT-RUN.json': json.dumps(launch, indent=2) + '\n'})
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(g.COMMAND, cwd=g.g.MAIN, env=dict(g.s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=g.s.sha(log.read_bytes()))
    g.s.changed({HERE / 'MAIN-TERMINAL.json': json.dumps(terminal, indent=2) + '\n'})
    if result.returncode:
        raise ValueError('actual-main 402 acceptance failed; see ' + str(log))
    if not log.read_text().rstrip().endswith(g.MARKER) or g.s.inputs.fingerprint(g.g.MAIN, g.g.REPO) != fingerprint:
        raise ValueError('incomplete marker or changed actual-main inputs')
    g.check()
    terminal['actual_main_acceptance'] = True
    g.s.changed({HERE / 'MAIN-ACCEPTANCE.json': json.dumps(terminal, indent=2) + '\n'})
    print(json.dumps(g.check(), indent=2))


if __name__ == '__main__':
    main()
