"""Corrupt helper reports in memory; never mutate audit inputs."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('square_review_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec)
spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text())
work = Path(manifest['scratch'])
results = [entry['module'] + '.' + name for entry in manifest['modules'] for name in entry['results']]
definitions = [entry['module'] + '.' + name for entry in manifest['modules'] for name in entry['definitions']]
expected = [('TYPE', name) for name in results] + [('DEF', name) for name in definitions]
report = (work / 'square_contracts.out').read_text()
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


for bad in [report + '...', report.replace('SQUARE_TYPE ' + results[0], 'SQUARE_TYPE wrong'),
            report + 'SQUARE_DEF unexpected\n', report.replace('SQUARE_TYPE ' + results[0], '', 1)]:
    rejected(lambda bad=bad: review.contracts(bad, expected))
entry = manifest['modules'][0]
source = (archive / (entry['file'] + '.source')).read_text()
review.inventory(source, entry)
for bad in [source.replace('Lemma den_sx_rename', 'Lemma wrong', 1),
            source + '\nDefinition unexpected := 0.\n']:
    rejected(lambda bad=bad: review.inventory(bad, entry))

normal = review.load('square_dependency_test', archive.parent / 'scalar-multiply-integration/review-normal.py')
assumptions = (work / 'square_assumptions.out').read_text()
assert normal.assumptions(assumptions) == review.expected_dependencies(results)
for bad in [assumptions + 'JET_ASSUMPTIONS pending\n',
            assumptions + 'JET_ASSUMPTIONS ' + results[0] + '\nClosed under the global context\n',
            'Axioms:\nnew_axiom : True\n' + assumptions,
            assumptions.replace('Events.external_functions_sem\n', 'new_axiom\n', 1)]:
    rejected(lambda bad=bad: normal.assumptions(bad))

valid = {name: {'exit_code': 0} for name in ['build', 'assumptions', 'contracts', 'kernel']}
valid.update(public_jet_equivalence=False, full_acceptance=False, checkout_coverage_added=0,
             scalar_mul_function_entry_alloc_free=False, actual_shared_input_pointer=True,
             actual_original_scalar_mul_body=True)
review.terminal(valid)
for key, value in [('public_jet_equivalence', True), ('full_acceptance', True),
                   ('checkout_coverage_added', 1), ('scalar_mul_function_entry_alloc_free', True),
                   ('actual_shared_input_pointer', False)]:
    bad = copy.deepcopy(valid); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
for key in ['build', 'assumptions', 'contracts', 'kernel']:
    bad = copy.deepcopy(valid); bad[key]['exit_code'] = None
    rejected(lambda bad=bad: review.terminal(bad))
print(f'square helper review: positive fixtures and {count} corruption fixtures passed; no inputs changed')
