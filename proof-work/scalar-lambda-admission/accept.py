"""Full combined420 audit over actual accepted418 and two reviewed deltas.

The separate419 audit keeps its own outcome. No intermediate419 installation
or successful terminal is invented or required by this whole-tree audit.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lambda_combined_normal_review', HERE / 'review.py')
v = importlib.util.module_from_spec(sp)
sp.loader.exec_module(v)
g, s = v.g, v.s
MARKER = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
BASELINE = HERE.parent / 'elements-txid-admission'


def baseline():
    post = g.load('lambda_combined_actual418', BASELINE / 'integration.py')
    state = post.check()
    if (state['coverage'] != '418/533' or state['actual_main_acceptance'] is not True or
        state['source_identical_to_accepted_candidate'] is not True or state['staged_patch_preserved'] is not True):
        raise ValueError('exact actual-main418 acceptance required')
    return dict(main_acceptance_sha256=s.sha((BASELINE / 'MAIN-ACCEPTANCE.json').read_bytes()),
                installation_sha256=s.sha((BASELINE / 'INSTALLATION.json').read_bytes()))


def reviewed(work):
    predecessor = g.load('lambda_combined_reviewed419', g.PRED / 'accept.py').reviewed(g.BASE_TREE)
    if predecessor != g.PRED_REVIEW:
        raise ValueError('reviewed419 source/evidence changed')
    r = json.loads((HERE / 'REVIEW.json').read_text())
    if (r != json.loads((work / 'REVIEW.json').read_text()) or r['review'] != v.review(work) or
        r['full_acceptance'] is not False or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes()) or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['review_engine_sha256'] != s.sha(v.REVIEW_ENGINE.read_bytes()) or
        r['candidate_input_sha256'] != s.inputs.fingerprint(work / 'Coq', work)):
        raise ValueError('normal420 review/source/engine identity differs')
    for n, h in r['tools_sha256'].items():
        if s.sha((HERE / n).read_bytes()) != h:
            raise ValueError('normal420 review tool changed')
    for n, h in r['evidence_sha256'].items():
        if s.sha((work / n).read_bytes()) != h:
            raise ValueError('normal420 reviewed evidence changed')
    expected = {
        'coverage': [sys.executable, '-B', 'jet-coverage.py'],
        'coverage-tests': [sys.executable, '-B', 'test-jet-coverage.py'],
        'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
        'lambda-source': [sys.executable, '-B', g.GUARDS[0], '--repo', str(g.REPO), '--coq', str(work / 'Coq')],
        'lambda-negative': [sys.executable, '-B', g.GUARDS[1], str(g.REPO), str(work / 'Coq')],
        'evidence-tests': [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)]}
    if set(r['checks']) != set(expected):
        raise ValueError('incomplete six-stage normal420 review')
    for n, command in expected.items():
        row = r['checks'][n]
        if (row['command'] != command or row['exit_code'] != 0 or
            row['log_sha256'] != s.sha((work / (n + '.log')).read_bytes())):
            raise ValueError('normal420 review command/exit/log differs')
    return {g.PRED.name: s.sha((g.PRED / 'REVIEW.json').read_bytes()),
            HERE.name: s.sha((HERE / 'REVIEW.json').read_bytes())}


def main(work):
    if (HERE / 'AUDIT-RUN.json').exists() or (work / 'AUDIT-RUN.json').exists():
        raise ValueError('combined420 audit already launched; inspect existing handle/receipt')
    before = baseline()
    chain = reviewed(work)
    command = ['bash', 'check-jets.sh', '--accept']
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    log = work / 'acceptance.log'
    launch = dict(candidate=str(work), command=command, audit_input_sha256=fingerprint,
        review_chain_sha256=chain, baseline_main_acceptance_sha256=before['main_acceptance_sha256'],
        baseline_installation_sha256=before['installation_sha256'],
        coverage_before='418/533', coverage_added=2, predecessor_isolated_acceptance_required=False,
        staged_patch_sha256=s.index_hash(), driver_sha256=s.sha(Path(__file__).read_bytes()),
        log=str(log), full_acceptance=False)
    for p in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        g.write(p, launch)
    print('Launching full combined420 acceptance; actual main remains accepted418', flush=True)
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(command, cwd=work / 'Coq', env=dict(s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=s.sha(log.read_bytes()))
    for p in [work / 'TERMINAL.json', HERE / 'TERMINAL.json']:
        g.write(p, terminal)
    if result.returncode:
        raise ValueError('combined420 full audit failed; inspect ' + str(log))
    if (not log.read_text().rstrip().endswith(MARKER) or
        s.inputs.fingerprint(work / 'Coq', work) != fingerprint or baseline() != before or
        reviewed(work) != chain or s.index_hash() != launch['staged_patch_sha256']):
        raise ValueError('incomplete marker or changed source/review/baseline/index')
    terminal.update(full_acceptance=True, coverage='420/533')
    for p in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(p, terminal)
    print('Combined420 full acceptance passed; guarded main installation still required', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
