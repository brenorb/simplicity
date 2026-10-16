"""Independent normal419 delta review; no installation or acceptance implied."""
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('null_data_normal_admission', HERE / 'admission.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
REVIEW_ENGINE = HERE.parent / 'normal-delta-review-v3.py'
engine = g.load('null_data_explicit_review_engine', REVIEW_ENGINE)
ENDPOINT = 'C.jet_elements_null_data_literal.elements_output_null_datum_literal_bitmachine_spec'
CONFIG = SimpleNamespace(**vars(g), NEW_RESULTS=144, NEW_DEFINITIONS=103,
    CLOSED_RESULTS=[n for n, ds in g.PR['dependencies'].items() if not ds], ENDPOINTS=[ENDPOINT],
    SCOPE_FIELDS=dict(canonical_null_data_source_review_complete=True,
        domain='represented-separated Bit Machine frames; not arbitrary overlapping buffers',
        caller_environment_construction_proved=False, formal_host_library_equivalence=False))


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
        ('null-data-source', [sys.executable, '-B', g.GUARDS[0], str(work)]),
        ('null-data-negative', [sys.executable, '-B', g.GUARDS[1], str(work)]),
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
    print('Normal419 null-data delta reviewed; full acceptance and installation remain required', flush=True)


if __name__ == '__main__':
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'review':
        print(json.dumps(review(work), indent=2))
    elif sys.argv[1] == 'finish':
        finish(work)
    else:
        raise ValueError('usage: review.py review|finish PRIVATE_TREE')
