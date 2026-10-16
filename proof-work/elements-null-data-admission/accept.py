"""Full isolated419 acceptance, only after independent normal-delta review."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('null_data_419_review', HERE / 'review.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
g, s = v.g, v.s
MARKER = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'


def reviewed(work):
    r = json.loads((HERE / 'REVIEW.json').read_text())
    if (r != json.loads((work / 'REVIEW.json').read_text()) or
        r['review'] != v.review(work) or r['full_acceptance'] is not False or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes()) or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('normal419 review scope/identity/source differs')
    for n, h in r['tools_sha256'].items():
        if s.sha((HERE / n).read_bytes()) != h:
            raise ValueError('normal419 review tool changed')
    for n, h in r['evidence_sha256'].items():
        if s.sha((work / n).read_bytes()) != h:
            raise ValueError('normal419 reviewed evidence changed')
    expected = {
        'coverage': [sys.executable, '-B', 'jet-coverage.py'],
        'coverage-tests': [sys.executable, '-B', 'test-jet-coverage.py'],
        'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
        'null-data-source': [sys.executable, '-B', g.GUARDS[0], str(work)],
        'null-data-negative': [sys.executable, '-B', g.GUARDS[1], str(work)],
        'evidence-tests': [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)]}
    if set(r['checks']) != set(expected):
        raise ValueError('incomplete independent normal419 review')
    for n, command in expected.items():
        row = r['checks'][n]
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha((work / (n + '.log')).read_bytes())):
            raise ValueError('review command/exit/log differs')
    return r


def main(work):
    if (HERE / 'AUDIT-RUN.json').exists() or (work / 'AUDIT-RUN.json').exists():
        raise ValueError('audit already launched; inspect existing handle/receipt')
    r = reviewed(work)
    command = ['bash', 'check-jets.sh', '--accept']
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    log = work / 'acceptance.log'
    launch = dict(candidate=str(work), command=command, audit_input_sha256=fingerprint,
        review_sha256=s.sha((HERE / 'REVIEW.json').read_bytes()),
        source_review_sha256=s.sha((g.SOURCE / 'SOURCE-REVIEW.json').read_bytes()),
        predecessor_main_acceptance_sha256=s.sha((g.PRED / 'MAIN-ACCEPTANCE.json').read_bytes()),
        coverage_before='418/533', coverage_added=1, staged_patch_sha256=s.index_hash(),
        driver_sha256=s.sha(Path(__file__).read_bytes()), log=str(log), full_acceptance=False)
    for p in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        g.write(p, launch)
    print('Launching full isolated419 acceptance; main remains accepted418', flush=True)
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(command, cwd=work / 'Coq', env=dict(s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=s.sha(log.read_bytes()))
    for p in [work / 'TERMINAL.json', HERE / 'TERMINAL.json']:
        g.write(p, terminal)
    if result.returncode:
        raise ValueError('isolated419 full audit failed; inspect ' + str(log))
    if (not log.read_text().rstrip().endswith(MARKER) or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint or reviewed(work) != r or
        s.index_hash() != launch['staged_patch_sha256']):
        raise ValueError('incomplete full marker or changed reviewed source/evidence/index')
    terminal.update(full_acceptance=True, coverage='419/533')
    for p in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(p, terminal)
    print('Isolated419 full acceptance passed; main installation still separate', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
