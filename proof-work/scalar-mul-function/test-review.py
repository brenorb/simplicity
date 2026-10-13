"""In-memory corruption fixtures; no proof or audit-input edits."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('boundary_review', archive / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
common = review.load('boundary_test_common', archive.parent / 'scalar-mul/review.py')
manifest = json.loads((archive / 'manifest.json').read_text())
receipt = json.loads((archive / 'REVIEW.json').read_text())
work = Path(manifest['scratch'])
tests = 0


def rejects(fn):
    global tests
    try:
        fn()
    except ValueError:
        tests += 1
        return
    raise AssertionError('corrupt evidence was accepted')


def corrupt(field, value):
    changed = copy.deepcopy(receipt)
    changed[field] = value
    review.terminal(changed)


rejects(lambda: corrupt('full_acceptance', True))
rejects(lambda: corrupt('checkout_coverage_added', 1))
rejects(lambda: corrupt('public_jet_equivalence', True))
rejects(lambda: corrupt('square_shared_input_alias', True))
failed = copy.deepcopy(receipt)
failed['build']['exit_code'] = 1
rejects(lambda: review.terminal(failed))
entry = copy.deepcopy(manifest['modules'][2])
entry['results'].pop()
rejects(lambda: review.inventory((archive / (entry['file'] + '.source')).read_text(), entry))
report = (work / 'boundary_contracts.out').read_text()
markers = [('TYPE', e['module'] + '.' + n) for e in manifest['modules'] for n in e['results']]
markers += [('DEF', e['module'] + '.' + n) for e in manifest['modules'] for n in e['definitions']]
rejects(lambda: review.contracts(report + '...', markers))
rejects(lambda: review.contracts(report.replace('BOUNDARY_TYPE', 'MISSING_TYPE', 1), markers))
deps = (work / 'boundary_assumptions.out').read_text()
expected = review.dependencies(manifest['modules'])
review.assumptions(deps, expected)
rejects(lambda: review.assumptions(deps.replace('Closed under the global context',
                                               'Axioms:\nFabricated.premise : Prop', 1), expected))
rejects(lambda: review.assumptions(deps.replace('JET_ASSUMPTIONS', 'MISSING_ASSUMPTIONS', 1), expected))
kernel = (work / 'boundary_kernel.log').read_text()
axioms = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
rejects(lambda: common.kernel(kernel.replace('CONTEXT SUMMARY', 'MISSING SUMMARY'), axioms))
rejects(lambda: common.kernel(kernel.replace('unsafe (co)fixpoints: <none>', 'unsafe (co)fixpoints: bad'), axioms))
assert review.review()['results'] == 16
print(f'{tests} negative fixtures rejected; complete caller function evidence passes')
