"""In-memory negative fixtures; never edit a proof or acceptance snapshot."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('literal_review', archive / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
common = review.load('literal_test_common', archive.parent / 'scalar-mul/review.py')
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


for field in ['full_acceptance', 'public_jet_equivalence', 'public_reader_calls_composed',
              'public_wrapper_cleanup', 'second_operand_freeable_postcondition', 'square_shared_input_alias']:
    rejects(lambda field=field: corrupt(field, True))
rejects(lambda: corrupt('checkout_coverage_added', 1))
rejects(lambda: corrupt('writer_entry_representation_derived', False))
failed = copy.deepcopy(receipt)
failed['kernel']['exit_code'] = 1
rejects(lambda: review.terminal(failed))
entry = copy.deepcopy(manifest['modules'][5])
entry['results'].pop()
rejects(lambda: review.inventory((archive / (entry['file'] + '.source')).read_text(), entry))
report = (work / 'public_contracts.out').read_text()
markers = [('TYPE', entry['module'] + '.' + name) for entry in manifest['modules'] for name in entry['results']]
markers += [('DEF', entry['module'] + '.' + name) for entry in manifest['modules'] for name in entry['definitions']]
rejects(lambda: review.contracts(report + '...', markers))
rejects(lambda: review.contracts(report.replace('PUBLIC_CHAIN_TYPE', 'MISSING_TYPE', 1), markers))
deps = (work / 'public_assumptions.out').read_text()
expected = review.dependencies(manifest['modules'])
review.assumptions(deps, expected)
rejects(lambda: review.assumptions(deps.replace('Closed under the global context',
                                               'Axioms:\nFabricated.execution : Prop', 1), expected))
rejects(lambda: review.assumptions(deps.replace('JET_ASSUMPTIONS', 'MISSING_ASSUMPTIONS', 1), expected))
kernel = (work / 'public_kernel_600.log').read_text()
axioms = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
rejects(lambda: common.kernel(kernel.replace('CONTEXT SUMMARY', 'MISSING SUMMARY'), axioms))
rejects(lambda: common.kernel(kernel.replace('unsafe (co)fixpoints: <none>', 'unsafe (co)fixpoints: bad'), axioms))
assert review.review()['results'] == 17
print(f'{tests} negative fixtures rejected; literal multiplication/write evidence passes')
