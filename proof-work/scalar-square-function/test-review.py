"""Negative receipt/report fixtures run in memory only."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('square_function_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text())
work = Path(manifest['scratch'])
results = [entry['module'] + '.' + name for entry in manifest['modules'] for name in entry['results']]
definitions = [entry['module'] + '.' + name for entry in manifest['modules'] for name in entry['definitions']]
expected = [('TYPE', name) for name in results] + [('DEF', name) for name in definitions]
report = (work / 'square_function_contracts.out').read_text()
review.contracts(report, expected)
count = 0


def rejected(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted evidence accepted')


for bad in [report + '...', report.replace('SQUARE_FUNCTION_TYPE ' + results[0], 'SQUARE_FUNCTION_TYPE wrong'),
            report + 'SQUARE_FUNCTION_DEF unexpected\n', report.replace('SQUARE_FUNCTION_TYPE ' + results[0], '', 1)]:
    rejected(lambda bad=bad: review.contracts(bad, expected))
entry = manifest['modules'][0]
source = (archive / (entry['file'] + '.source')).read_text(); review.inventory(source, entry)
for bad in [source.replace('Lemma scalar_square_inputs_valid', 'Lemma wrong', 1),
            source + '\nDefinition unexpected := 0.\n']:
    rejected(lambda bad=bad: review.inventory(bad, entry))
normal = review.load('square_function_assumptions_test', archive.parent / 'scalar-multiply-integration/review-normal.py')
assumptions = (work / 'square_function_assumptions.out').read_text()
assert normal.assumptions(assumptions) == review.expected_dependencies(results)
for bad in [assumptions + 'JET_ASSUMPTIONS pending\n',
            assumptions + 'JET_ASSUMPTIONS ' + results[0] + '\nClosed under the global context\n',
            'Axioms:\nnew_axiom : True\n' + assumptions,
            assumptions.replace('Events.external_functions_sem\n', 'new_axiom\n', 1)]:
    rejected(lambda bad=bad: normal.assumptions(bad))

valid = json.loads((archive / 'REVIEW.json').read_text()); review.terminal(valid)
for key, value in [('public_jet_equivalence', True), ('full_acceptance', True),
                   ('checkout_coverage_added', 1), ('scalar_mul_function_entry_alloc_free', False),
                   ('actual_r_equals_a_equals_b', False)]:
    bad = copy.deepcopy(valid); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
for key in ['build', 'assumptions', 'contracts', 'kernel']:
    bad = copy.deepcopy(valid); bad[key]['exit_code'] = None
    rejected(lambda bad=bad: review.terminal(bad))
print(f'square function review: positive fixtures and {count} corruption fixtures passed; no inputs changed')
