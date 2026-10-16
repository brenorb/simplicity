"""Full combined417 audit: one reviewed six-module delta over installed, accepted415.

This audits the entire exact tree, not just the last issuance delta. Installation must additionally wait for actual-main415 and this full result.
"""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import time

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASELINE = HERE.parent / 'elements-issuance-amount-admission'
BATCHES = [('elements-token-admission', 2, 'token')]


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


review = load('issuance_combined_review', HERE / 'review.py')
g, s = review.g, review.s


def baseline():
    if not (BASELINE / 'ACCEPTANCE.json').exists() or not (BASELINE / 'INSTALLATION.json').exists():
        raise ValueError('real isolated415 acceptance and guarded installation required')
    post = load('issuance_combined_baseline', BASELINE / 'integration.py')
    state = post.check()
    if (state['coverage'] != '415/533' or state['staged_patch_preserved'] is not True or
        state['source_identical_to_accepted_candidate'] is not True):
        raise ValueError('exact installed415 source and staging not verified')
    return post


def review_chain(work):
    # Independent review can precede installation of415. Positive full launch
    # still requires baseline() first, which validates its real acceptance and
    # installation. Bind the chain to the same exact reviewed415 source.
    chain = {}
    previous = json.loads((BASELINE / 'REVIEW.json').read_text())['candidate_input_sha256']
    if (BASELINE / 'ACCEPTANCE.json').exists():
        if json.loads((BASELINE / 'ACCEPTANCE.json').read_text())['audit_input_sha256'] != previous:
            raise ValueError('accepted/reviewed415 source differs')
    for folder, added, prefix in BATCHES:
        here = HERE.parent / folder
        verifier = load('combined_' + prefix, here / 'review.py')
        candidate = Path(json.loads((here / 'ASSEMBLY.json').read_text())['candidate'])
        if folder == HERE.name and candidate != work:
            raise ValueError('wrong final combined candidate')
        if not (here / 'REVIEW.json').is_file() or not (candidate / 'REVIEW.json').is_file():
            raise ValueError('completed six-stage review required: ' + folder)
        verifier.review(candidate)
        r = json.loads((candidate / 'REVIEW.json').read_text())
        meta = json.loads((candidate / 'ASSEMBLY.json').read_text())
        if ((candidate / 'REVIEW.json').read_bytes() != (here / 'REVIEW.json').read_bytes() or r['full_acceptance'] is not False or
            r['review']['coverage_added'] != added or r['review']['inherited_proof_changes'] != 0 or
            meta['predecessor_input_sha256'] != previous or
            r['candidate_input_sha256'] != s.inputs.fingerprint(candidate / 'Coq', candidate) or
            r['preparation_engine_sha256'] != s.sha(verifier.g.PREPARE_ENGINE.read_bytes()) or
            r['assembly_sha256'] != s.sha((candidate / 'ASSEMBLY.json').read_bytes()) or
            r['preparation_sha256'] != s.sha((candidate / 'PREPARATION.json').read_bytes())):
            raise ValueError('reviewed chain scope/source/provenance differs: ' + folder)
        if hasattr(verifier, 'REVIEW_ENGINE'):
            if r['review_engine_sha256'] != s.sha(verifier.REVIEW_ENGINE.read_bytes()):
                raise ValueError('shared review engine changed')
        for n, h in r['tools_sha256'].items():
            if s.sha((here / n).read_bytes()) != h:
                raise ValueError('reviewed tool changed')
        for n, h in r['evidence_sha256'].items():
            if s.sha((candidate / n).read_bytes()) != h:
                raise ValueError('reviewed object/report evidence changed')
        python = sys.executable
        expected = {
            'coverage': [python, '-B', 'jet-coverage.py'],
            'coverage-tests': [python, '-B', 'test-jet-coverage.py'],
            'normal-contract-comparison': ['bash', 'audit-jet-contracts.sh'],
            prefix + '-source': [python, '-B', verifier.g.GUARDS[0], str(candidate)],
            prefix + '-negative': [python, '-B', verifier.g.GUARDS[1], str(candidate)],
            'evidence-tests': [python, '-B', str(here / 'test-review.py'), str(candidate)]}
        if set(r['checks']) != set(expected):
            raise ValueError('incomplete six-stage review')
        for n, command in expected.items():
            row = r['checks'][n]
            actual = row['command'][:]
            if command[0] == python and actual:
                if Path(actual[0]).resolve() == Path(python).resolve():
                    actual[0] = python
            if (actual != command or row['exit_code'] != 0 or
                row['log_sha256'] != s.sha((candidate / (n + '.log')).read_bytes())):
                raise ValueError('review command/exit/log differs: ' + n)
        previous = r['candidate_input_sha256']
        chain[folder] = s.sha((here / 'REVIEW.json').read_bytes())
    if sum(n for _, n, _ in BATCHES) != 2:
        raise ValueError('wrong combined coverage delta')
    return chain


def preflight(work):
    if (work / 'AUDIT-RUN.json').exists() or (HERE / 'AUDIT-RUN.json').exists():
        raise ValueError('combined audit already launched; inspect its existing handle')
    baseline()
    return review_chain(work)


def main(work):
    chain = preflight(work)
    command = ['bash', 'check-jets.sh', '--accept']
    fingerprint = s.inputs.fingerprint(work / 'Coq', work)
    log = work / 'acceptance.log'
    launch = dict(candidate=str(work), command=command, audit_input_sha256=fingerprint,
        review_chain_sha256=chain, coverage_before='415/533', coverage_added=2,
        baseline_acceptance_sha256=s.sha((BASELINE / 'ACCEPTANCE.json').read_bytes()),
        baseline_installation_sha256=s.sha((BASELINE / 'INSTALLATION.json').read_bytes()),
        driver_sha256=s.sha(Path(__file__).read_bytes()), log=str(log), full_acceptance=False)
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
        raise ValueError('combined417 audit failed; see ' + str(log))
    marker = 'all jet acceptance checks passed (build, kernel, reviewed snapshots, negative tests, five ASTs)'
    if not log.read_text().rstrip().endswith(marker) or s.inputs.fingerprint(work / 'Coq', work) != fingerprint:
        raise ValueError('incomplete acceptance marker or changed source')
    baseline()
    if review_chain(work) != chain:
        raise ValueError('reviewed delta chain changed during audit')
    terminal.update(full_acceptance=True, coverage='417/533')
    for p in [work / 'ACCEPTANCE.json', HERE / 'ACCEPTANCE.json']:
        g.write(p, terminal)
    print('Combined417 full acceptance passed; guarded main installation still required', flush=True)


if __name__ == '__main__':
    main(Path(sys.argv[1]).resolve())
