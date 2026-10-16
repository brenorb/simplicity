"""Independent normal467 delta review; a prepared snapshot is not acceptance."""
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('elements_context_normal_admission', HERE / 'admission.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
REVIEW_ENGINE = HERE.parent / 'normal-delta-review-v6.py'
engine = g.load('normal467_explicit_guard_review', REVIEW_ENGINE)
CONFIG = SimpleNamespace(**dict(vars(g), NEW_RESULTS=123, NEW_DEFINITIONS=15,
    CLOSED_RESULTS=g.PR['closed_results'], SCOPE_FIELDS=dict(
        canonical_sha_source_reviews_complete=True, whole_c_sha_startup_endpoints=18,
        named_startup_state_and_actual_initial_memory=True, public_endpoint_inherited_assumptions=8,
        new_axioms=0, conditional_memcpy_endpoints=17, newly_registered_support_modules=9, formal_host_library_equivalence=False)))


def review(work):
    return engine.review(CONFIG, work)


def finish(work):
    if (work / 'REVIEW.json').exists():
        raise ValueError('normal467 review already recorded; inspect existing evidence')
    before, index = s.input_map(), s.index_hash()
    result, checks = review(work), {}
    commands = [
        ('coverage', [sys.executable, '-B', 'jet-coverage.py']),
        ('coverage-tests', [sys.executable, '-B', 'test-jet-coverage.py']),
        ('normal-contract-comparison', ['bash', 'audit-jet-contracts.sh']),
    ]
    for folder in g.SOURCE_FOLDERS:
        commands += [(folder + '-positive', [sys.executable, '-B', folder + '/check-source.py', str(work)]),
                     (folder + '-negative', [sys.executable, '-B', folder + '/test-source.py', str(work)])]
    commands += [('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]
    for stem, command in commands:
        checks[stem] = s.run(work, command, stem, 1800)
        print('Passed normal467 ' + stem, flush=True)
    if review(work) != result or s.input_map() != before or s.index_hash() != index:
        raise ValueError('normal467 source/main/index changed during review')
    record = dict(review=result, checks=checks, assembly_sha256=s.sha((work / 'ASSEMBLY.json').read_bytes()),
        preparation_sha256=s.sha((work / 'PREPARATION.json').read_bytes()),
        preparation_engine_sha256=s.sha(g.PREPARE_ENGINE.read_bytes()),
        review_engine_sha256=s.sha(REVIEW_ENGINE.read_bytes()),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in
            ['admission.py', 'coverage-boundary.py', 'coverage-fixtures.py', 'review.py', 'test-review.py']},
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        evidence_sha256={str(p.relative_to(work)): s.sha(p.read_bytes()) for p in work.rglob('*')
            if p.is_file() and p.suffix in ['.log', '.vo']}, full_acceptance=False)
    g.write(work / 'REVIEW.json', record)
    g.write(HERE / 'REVIEW.json', record)
    s.changed({HERE / (n + '.log'): (work / (n + '.log')).read_text() for n in checks})
    print('Normal467 eighteen-jet SHA startup delta independently reviewed; real full acceptance/integration remain', flush=True)


if __name__ == '__main__':
    if len(sys.argv) != 3 or sys.argv[1] not in ['review', 'finish']:
        raise ValueError('usage: review.py review|finish PRIVATE_TREE')
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'finish':
        finish(work)
    else:
        print(json.dumps(review(work), indent=2))
