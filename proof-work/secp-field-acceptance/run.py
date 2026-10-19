"""Run complete normal gates on the isolated candidate; never fake acceptance.

Generation may update only the three explicitly permitted snapshots. Review
must precede a separate --accept run with no update or no-build flags.
"""
import importlib.util
import json
import os
from pathlib import Path
import signal
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('field_acceptance_preparation', HERE / 'prepare.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
s = p.s
SNAPSHOTS = ['jet_assumptions.expected', 'jet_contracts.expected', 'jet_coqchk_axioms.expected']


def identity(updating=False):
    r = json.loads((HERE / 'PREPARATION.json').read_text())
    work, base = Path(r['candidate']), Path(r['parent_candidate'])
    if (work == base or work == p.REPO or p.REPO in work.parents or work.is_symlink() or
            r['prepare_sha256'] != s.sha((HERE / 'prepare.py').read_bytes()) or
            r['main_inputs'] != s.input_map() or r['staged_patch_sha256'] != s.index_hash() or
            r['parent_input_sha256'] != s.inputs.fingerprint(base / 'Coq', base) or
            r['parent_checked_sha256'] != s.sha((HERE.parent / 'secp-field-integration/CHECKED.json').read_bytes())):
        raise ValueError('candidate, parent or checkout input identity differs')
    for name, row in r['changed_inputs'].items():
        if s.sha((work / name).read_bytes()) != row['after']:
            raise ValueError('prepared support/registry input changed: ' + name)
    if not updating:
        receipt = HERE / 'GENERATED.json'
        wanted = json.loads(receipt.read_text())['input_sha256'] if receipt.exists() else r['input_sha256']
        if s.inputs.fingerprint(work / 'Coq', work) != wanted:
            raise ValueError('candidate source/snapshot fingerprint differs')
    return work, r


def run_logged(work, command, phase, timeout=7200):
    log = work / (phase + '.log')
    env = dict(s.ENV, JOBS='2')
    # Own process group: a real deadline stops this job's descendants only.
    # The returned tool/session handle remains the preferred observation API.
    with log.open('wb') as out:
        proc = subprocess.Popen(command, cwd=work / 'Coq', env=env, stdout=out,
            stderr=subprocess.STDOUT, start_new_session=True)
        s.changed({HERE / (phase.upper() + '-PROCESS.json'): json.dumps(dict(
            pid=proc.pid, candidate=str(work), command=command, terminal=False,
            timeout_seconds=timeout), indent=2) + '\n'})
        try:
            code = proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.wait(timeout=15)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.wait()
            code = proc.returncode
            terminal = dict(pid=proc.pid, candidate=str(work), command=command,
                terminal=True, exit_code=code, timed_out=True, log_sha256=s.sha(log.read_bytes()))
            s.changed({HERE / (phase.upper() + '-PROCESS.json'): json.dumps(terminal, indent=2) + '\n'})
            raise ValueError('normal gate reached its real deadline; terminal evidence preserved')
    row = dict(command=command, exit_code=code, log_sha256=s.sha(log.read_bytes()))
    s.changed({HERE / (phase.upper() + '-PROCESS.json'): json.dumps(dict(pid=proc.pid,
        candidate=str(work), terminal=True, **row), indent=2) + '\n'})
    if code:
        raise ValueError('normal gate failed; see ' + str(log))
    return row


def generate():
    work, r = identity()
    if (HERE / 'GENERATE-LAUNCH.json').exists():
        raise ValueError('generation already launched; inspect its exact live/terminal handle')
    before = s.inputs.fingerprint(work / 'Coq', work, updating=True)
    command = ['bash', 'check-jets.sh', '--update-expected']
    s.changed({HERE / 'GENERATE-LAUNCH.json': json.dumps(dict(candidate=str(work), command=command,
        preparation_sha256=s.sha((HERE / 'PREPARATION.json').read_bytes()),
        verifier_sha256=s.sha(Path(__file__).read_bytes()), non_snapshot_input_sha256=before,
        complete=False, accepted=False), indent=2) + '\n'})
    row = run_logged(work, command, 'generate')
    identity(updating=True)
    if s.inputs.fingerprint(work / 'Coq', work, updating=True) != before:
        raise ValueError('a non-snapshot input changed during normal generation')
    result = dict(candidate=str(work), generation=row,
        launch_sha256=s.sha((HERE / 'GENERATE-LAUNCH.json').read_bytes()),
        non_snapshot_input_sha256=before, input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        snapshots={n: s.sha((work / 'Coq/C' / n).read_bytes()) for n in SNAPSHOTS},
        snapshot_generation_complete=True, snapshot_review_complete=False,
        accepted=False, accepted_coverage_added=0)
    s.changed({HERE / 'GENERATED.json': json.dumps(result, indent=2) + '\n',
        HERE / 'generate.log': (work / 'generate.log').read_text()})
    print('Full normal snapshot generation passed; review and separate --accept are still required', flush=True)


def accept():
    work, r = identity()
    generated = json.loads((HERE / 'GENERATED.json').read_text())
    review = json.loads((HERE / 'REVIEWED.json').read_text())
    if (not review['review_complete'] or review['generated_sha256'] != s.sha((HERE / 'GENERATED.json').read_bytes()) or
            review['input_sha256'] != generated['input_sha256']):
        raise ValueError('exact generated snapshots have not passed review')
    if (HERE / 'ACCEPT-LAUNCH.json').exists():
        raise ValueError('acceptance already launched; inspect its exact live/terminal handle')
    command = ['bash', 'check-jets.sh', '--accept']
    s.changed({HERE / 'ACCEPT-LAUNCH.json': json.dumps(dict(candidate=str(work), command=command,
        reviewed_sha256=s.sha((HERE / 'REVIEWED.json').read_bytes()),
        verifier_sha256=s.sha(Path(__file__).read_bytes()), complete=False), indent=2) + '\n'})
    row = run_logged(work, command, 'accept')
    identity()
    result = dict(candidate=str(work), acceptance=row,
        input_sha256=generated['input_sha256'],
        reviewed_sha256=s.sha((HERE / 'REVIEWED.json').read_bytes()),
        accepted=True, candidate_registration_delta=1, checkout_accepted_coverage_added=0)
    s.changed({HERE / 'ACCEPTED.json': json.dumps(result, indent=2) + '\n',
        HERE / 'accept.log': (work / 'accept.log').read_text()})
    print('Full normal --accept passed in the isolated candidate; checkout promotion is separate', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 2 or sys.argv[1] not in {'generate', 'accept', 'check'}:
        raise SystemExit('usage: run.py generate|accept|check')
    if sys.argv[1] == 'check':
        work, r = identity()
        print('Exact candidate, parent and checkout inputs match: ' + str(work))
    else:
        {'generate': generate, 'accept': accept}[sys.argv[1]]()
