"""Independent normal420 delta review; initialized lambda remains explicit."""
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('lambda_normal_admission', HERE / 'admission.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
REVIEW_ENGINE = HERE.parent / 'normal-delta-review-v4.py'
engine = g.load('lambda_explicit_dependency_review', REVIEW_ENGINE)
CONFIG = SimpleNamespace(**dict(vars(g), NEW_RESULTS=116, NEW_DEFINITIONS=32,
    CLOSED_RESULTS=g.PR['closed_results'],
    SCOPE_FIELDS=dict(selected_canonical_lambda_source_review_complete=True,
        initialized_global_entry_and_preservation_explicit=True, actual_init_fresh_call_witness=True,
        public_endpoint_inherited_assumptions=8, new_axioms=0, c_evaluator_setup_proved=False)))


def review(work):
    return engine.review(CONFIG, work)


def finish(work):
    if (work / 'REVIEW.json').exists():
        raise ValueError('review already recorded; inspect existing receipt')
    result, checks = review(work), {}
    for stem, command in [
        ('coverage', [sys.executable, '-B', 'jet-coverage.py']),
        ('coverage-tests', [sys.executable, '-B', 'test-jet-coverage.py']),
        ('normal-contract-comparison', ['bash', 'audit-jet-contracts.sh']),
        ('lambda-source', [sys.executable, '-B', g.GUARDS[0], '--repo', str(g.REPO), '--coq', str(work / 'Coq')]),
        ('lambda-negative', [sys.executable, '-B', g.GUARDS[1], str(g.REPO), str(work / 'Coq')]),
        ('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]:
        checks[stem] = s.run(work, command, stem, 1800)
    if review(work) != result:
        raise ValueError('normal delta changed during review')
    record = dict(review=result, checks=checks, assembly_sha256=s.sha((work / 'ASSEMBLY.json').read_bytes()),
        preparation_sha256=s.sha((work / 'PREPARATION.json').read_bytes()),
        preparation_engine_sha256=s.sha(g.PREPARE_ENGINE.read_bytes()),
        review_engine_sha256=s.sha(REVIEW_ENGINE.read_bytes()),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
                      ['admission.py', 'coverage-fixtures.py', 'review.py', 'test-review.py']},
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        evidence_sha256={str(p.relative_to(work)): s.sha(p.read_bytes()) for p in work.rglob('*')
            if p.is_file() and p.suffix in ['.log', '.vo']}, full_acceptance=False)
    g.write(work / 'REVIEW.json', record)
    g.write(HERE / 'REVIEW.json', record)
    print('Normal initialized-lambda delta reviewed; full combined acceptance and integration remain required', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['review', 'finish']:
        raise ValueError('usage: review.py review|finish PRIVATE_TREE')
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'finish':
        finish(work)
    else:
        print(json.dumps(review(work), indent=2))
