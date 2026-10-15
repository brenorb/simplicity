"""Full 402 audit only after real 401 acceptance and guarded installation."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lbtc_accept_review', HERE / 'review.py')
review = importlib.util.module_from_spec(sp)
sp.loader.exec_module(review)
g, s = review.g, review.s


def preflight(work):
    if (work / 'AUDIT-RUN.json').exists():
        raise ValueError('audit already launched; inspect its existing handle and terminal evidence')
    if not (g.PRED / 'ACCEPTANCE.json').exists() or not (g.PRED / 'INSTALLATION.json').exists():
        raise ValueError('real full 401 acceptance and guarded installation must finish before this audit starts')
    post = g.load('lbtc_accepted_predecessor', g.PRED / 'integration.py')
    state = post.check()
    if (state['coverage'] != '401/533' or state['staged_patch_preserved'] is not True or
        state['source_identical_to_accepted_candidate'] is not True or
        state['reviewed_nullable_128_preserved'] is not True or
        s.inputs.fingerprint(g.MAIN, g.REPO) != g.PRED_REVIEW['candidate_input_sha256']):
        raise ValueError('accepted 401 predecessor/source/index is not verified')
    review.review(work)
    r = json.loads((work / 'REVIEW.json').read_text())
    if (r['full_acceptance'] is not False or r['review']['coverage_added'] != 1 or
        r['review']['inherited_proof_changes'] != 0 or
        r['preparation_engine_sha256'] != s.sha(g.PREPARE_ENGINE.read_bytes()) or
        r['assembly_sha256'] != s.sha((work / 'ASSEMBLY.json').read_bytes()) or
        r['preparation_sha256'] != s.sha((work / 'PREPARATION.json').read_bytes())):
        raise ValueError('review binding/scope differs or was confused with acceptance')
    for n, h in r['tools_sha256'].items():
        if s.sha((HERE / n).read_bytes()) != h:
            raise ValueError('review tool drift')
    for n, h in r['evidence_sha256'].items():
        if s.sha((work / n).read_bytes()) != h:
            raise ValueError('reviewed source/object/terminal evidence drift')
    if s.inputs.fingerprint(work / 'Coq', work) != r['candidate_input_sha256']:
        raise ValueError('reviewed 402 candidate source changed')
    return r


def main(work):
    r = preflight(work)
    command = ['bash', 'check-jets.sh', '--accept']
    log = work / 'acceptance.log'
    before = s.inputs.fingerprint(work / 'Coq', work)
    launch = dict(candidate=str(work), command=command, audit_input_sha256=before,
        review_sha256=s.sha((work / 'REVIEW.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()),
        predecessor_acceptance_sha256=s.sha((g.PRED / 'ACCEPTANCE.json').read_bytes()),
        predecessor_installation_sha256=s.sha((g.PRED / 'INSTALLATION.json').read_bytes()),
        log=str(log), full_acceptance=False)
    for p in [work / 'AUDIT-RUN.json', HERE / 'AUDIT-RUN.json']:
        g.write(p, launch)
    start = time.monotonic()
    with log.open('wb') as out:
        result = subprocess.run(command, cwd=work / 'Coq', env=dict(s.ENV, JOBS='2'),
                                stdout=out, stderr=subprocess.STDOUT, timeout=10800)
    terminal = dict(launch, exit_code=result.returncode, seconds=time.monotonic()-start,
                    log_sha256=s.sha(log.read_bytes()))
    for p in [work / 'TERMINAL.json', HERE / 'TERMINAL.json']:
        g.write(p, terminal)
    if result.returncode:
        raise ValueError('402 acceptance failed; see ' + str(log))
    marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
    if not log.read_text().rstrip().endswith(marker) or s.inputs.fingerprint(work / 'Coq', work) != before:
        raise ValueError('missing complete marker or changed candidate inputs')
    review.review(work)
    terminal.update(full_acceptance=True, coverage='402/533')
    for p in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(p, terminal)
    print('Full isolated 402 acceptance passed; guarded main installation still required', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
