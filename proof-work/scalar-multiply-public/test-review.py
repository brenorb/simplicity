"""Reject corrupt proof-candidate evidence in memory, without source edits."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('multiply_review', archive / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
common = review.load('multiply_test_common', archive.parent / 'scalar-mul/review.py')
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


for field in ['complete_original_public_function', 'public_reader_calls_composed',
              'public_wrapper_entry_copy_return_free', 'both_operand_freeable_postcondition_derived',
              'literal_canonical_output_encoding', 'public_c_to_literal_contract']:
    rejects(lambda field=field: corrupt(field, False))
rejects(lambda: corrupt('full_acceptance', True))
rejects(lambda: corrupt('checkout_coverage_added', 1))
rejects(lambda: corrupt('square_shared_input_alias', True))
rejects(lambda: corrupt('checked_public_candidates', 29))
failed = copy.deepcopy(receipt)
failed['kernel']['exit_code'] = 1
rejects(lambda: review.terminal(failed))
entry = copy.deepcopy(manifest['modules'][-1])
entry['results'].pop()
rejects(lambda: review.inventory((archive / (entry['file'] + '.source')).read_text(), entry))
report = (work / 'multiply_final_contracts.out').read_text()
markers = [('TYPE', entry['module'] + '.' + name) for entry in manifest['modules'] for name in entry['results']]
markers += [('DEF', entry['module'] + '.' + name) for entry in manifest['modules'] for name in entry['definitions']]
markers += [('DEF', name) for name in manifest['critical_definitions']]
rejects(lambda: review.contracts(report + '...', markers))
rejects(lambda: review.contracts(report.replace('MULTIPLY_TYPE', 'MISSING_TYPE', 1), markers))
deps = (work / 'multiply_final_assumptions.out').read_text()
expected = review.dependencies(manifest['modules'])
review.assumptions(deps, expected)
rejects(lambda: review.assumptions(deps.replace('Closed under the global context',
                                               'Axioms:\nFabricated.free : Prop', 1), expected))
rejects(lambda: review.assumptions(deps.replace('JET_ASSUMPTIONS', 'MISSING_ASSUMPTIONS', 1), expected))
kernel = (work / 'multiply_kernel.log').read_text()
axioms = sorted((Path(manifest['dependency_coq']) / 'C/jet_coqchk_axioms.expected').read_text().split())
rejects(lambda: common.kernel(kernel.replace('CONTEXT SUMMARY', 'MISSING SUMMARY'), axioms))
rejects(lambda: common.kernel(kernel.replace('unsafe (co)fixpoints: <none>', 'unsafe (co)fixpoints: bad'), axioms))
assert review.review()['checked_public_candidates'] == 1
print(f'{tests} negative fixtures rejected; complete public multiplication evidence passes')
