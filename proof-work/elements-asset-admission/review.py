"""Independent 410 review using an explicit-configuration shared engine."""
import importlib.util
import json
from pathlib import Path
import sys
from types import SimpleNamespace

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('legacy_admission_gate', HERE / 'admission.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
s = g.s
REVIEW_ENGINE = HERE.parent / 'normal-delta-review-v2.py'
engine = g.load('legacy_explicit_review_engine', REVIEW_ENGINE)


def main_fingerprint(inputs):
    choices = [(g.PRED_META['main_inputs'], g.PRED_META['main_input_sha256']),
               (g.PRED_META['baseline_inputs'], g.PRED_META['predecessor_input_sha256']),
               (g.baseline_inputs(), g.PRED_REVIEW['candidate_input_sha256']),
               (g.parent.parent.baseline_inputs(), g.parent.parent.PRED_REVIEW['candidate_input_sha256'])]
    for table, fingerprint in choices:
        if inputs == table:
            return fingerprint
    raise ValueError('unknown historical main checkpoint')


CONFIG = SimpleNamespace(**vars(g), NEW_RESULTS=9, NEW_DEFINITIONS=6,
    CLOSED_RESULTS=g.PR['closed_results'], ENDPOINTS=g.PR['endpoints'], main_fingerprint=main_fingerprint,
    SCOPE_FIELDS=dict(packed_field_projection_reviewed=True, caller_environment_construction_proved=False))


def review(work):
    return engine.review(CONFIG, work)


def finish(work):
    if (work / 'REVIEW.json').exists():
        raise ValueError('review already completed; inspect its existing receipt')
    result, checks = review(work), {}
    for stem, command in [
        ('coverage', [sys.executable, '-B', 'jet-coverage.py']),
        ('coverage-tests', [sys.executable, '-B', 'test-jet-coverage.py']),
        ('normal-contract-comparison', ['bash', 'audit-jet-contracts.sh']),
        ('asset-source', [sys.executable, '-B', 'elements-asset-literal/check-source.py', str(work)]),
        ('asset-negative', [sys.executable, '-B', 'elements-asset-literal/test-source.py', str(work)]),
        ('evidence-tests', [sys.executable, '-B', str(HERE / 'test-review.py'), str(work)])]:
        checks[stem] = s.run(work, command, stem, 1800)
    review(work)
    record = dict(review=result, checks=checks, assembly_sha256=s.sha((work / 'ASSEMBLY.json').read_bytes()),
        preparation_sha256=s.sha((work / 'PREPARATION.json').read_bytes()),
        preparation_engine_sha256=s.sha(g.PREPARE_ENGINE.read_bytes()),
        review_engine_sha256=s.sha(REVIEW_ENGINE.read_bytes()),
        tools_sha256={n: s.sha((HERE / n).read_bytes()) for n in ['admission.py', 'review.py', 'test-review.py']},
        candidate_input_sha256=s.inputs.fingerprint(work / 'Coq', work),
        evidence_sha256={str(p.relative_to(work)): s.sha(p.read_bytes()) for p in work.rglob('*')
            if p.is_file() and p.suffix in ['.log', '.vo']}, full_acceptance=False)
    g.write(work / 'REVIEW.json', record)
    g.write(HERE / 'REVIEW.json', record)
    print('Three asset getter normal deltas reviewed; full acceptance and integration remain required', flush=True)


if __name__ == '__main__':
    work = Path(sys.argv[2]).resolve()
    if sys.argv[1] == 'review':
        print(json.dumps(review(work), indent=2))
    elif sys.argv[1] == 'finish':
        finish(work)
    else:
        raise ValueError('usage: review.py review|finish PRIVATE_TREE')
