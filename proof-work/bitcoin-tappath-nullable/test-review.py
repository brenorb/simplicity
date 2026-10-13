"""In-memory evidence corruption checks; never edits a proof or receipt."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('nullable_review', archive / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
common = review.load('nullable_test_common', archive.parent / 'scalar-mul/review.py')
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
failed = copy.deepcopy(receipt)
failed['build']['exit_code'] = 1
rejects(lambda: review.terminal(failed))
entry = copy.deepcopy(manifest['modules'][1])
entry['results'].pop()
rejects(lambda: review.inventory((archive / (entry['file'] + '.source')).read_text(), entry))
report = (work / 'final_contracts.out').read_text()
markers = [('TYPE', e['module'] + '.' + n) for e in manifest['modules'] for n in e['results']]
markers += [('DEF', e['module'] + '.' + n) for e in manifest['modules'] for n in e['definitions']]
rejects(lambda: review.contracts(report + '...', markers))
rejects(lambda: review.contracts(report.replace('NULLABLE_TYPE', 'MISSING_TYPE', 1), markers))
deps = (work / 'final_assumptions.out').read_text()
expected = {}
inherited = {'ClassicalDedekindReals.sig_forall_dec', 'ClassicalDedekindReals.sig_not_dec',
             'Classical_Prop.classic', 'FunctionalExtensionality.functional_extensionality_dep'}
for entry in manifest['modules']:
    for name in entry['results']:
        expected[entry['module'] + '.' + name] = (
            set() if name in {'bitcoin_tappath_empty_cells', 'bitcoin_tappath_empty_sem'} else
            inherited | ({'Events.external_functions_sem', 'Events.inline_assembly_sem'}
                         if name.endswith('_local_spec') else set()))
review.assumptions(deps, expected)
rejects(lambda: review.assumptions(deps.replace('Closed under the global context',
                                               'Axioms:\nFabricated.premise : Prop', 1), expected))
rejects(lambda: review.assumptions(deps.replace('JET_ASSUMPTIONS', 'MISSING_ASSUMPTIONS', 1), expected))
kernel = (work / 'final_kernel.log').read_text()
axioms = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
rejects(lambda: common.kernel(kernel.replace('CONTEXT SUMMARY', 'MISSING SUMMARY'), axioms))
rejects(lambda: common.kernel(kernel.replace('unsafe (co)fixpoints: <none>', 'unsafe (co)fixpoints: bad'), axioms))
assert review.review()['results'] == 9
print(f'{tests} negative fixtures rejected; nullable proof evidence passes')
