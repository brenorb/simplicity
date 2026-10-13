"""Corrupt borrowed-function evidence in memory, never audit inputs."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('borrowed_function_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text()); work = Path(manifest['scratch'])
results = [entry['module'] + '.' + n for entry in manifest['modules'] for n in entry['results']]
definitions = [entry['module'] + '.' + n for entry in manifest['modules'] for n in entry['definitions']]
expected = [('TYPE', n) for n in results] + [('DEF', n) for n in definitions]
report = (work / 'borrowed_function_contracts.out').read_text(); review.contracts(report, expected)
count = 0


def rejected(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted borrowed function evidence accepted')


for bad in [report + '...', report.replace('BORROWED_FUNCTION_TYPE ' + results[0], 'BORROWED_FUNCTION_TYPE wrong'),
            report + 'BORROWED_FUNCTION_DEF unexpected\n', report.replace('BORROWED_FUNCTION_TYPE ' + results[0], '', 1)]:
    rejected(lambda bad=bad: review.contracts(bad, expected))
entry = manifest['modules'][0]; source = (archive / (entry['file'] + '.source')).read_text()
review.inventory(source, entry)
for bad in [source.replace('Lemma scalar_mul_borrowed_inputs_valid', 'Lemma wrong', 1),
            source + '\nDefinition unexpected := 0.\n']:
    rejected(lambda bad=bad: review.inventory(bad, entry))
normal = review.load('borrowed_function_dep_test', archive.parent / 'scalar-multiply-integration/review-normal.py')
assumptions = (work / 'borrowed_function_assumptions.out').read_text()
assert normal.assumptions(assumptions) == review.expected_dependencies(results)
for bad in [assumptions + 'JET_ASSUMPTIONS pending\n',
            assumptions + 'JET_ASSUMPTIONS ' + results[0] + '\nClosed under the global context\n',
            'Axioms:\nnew_axiom : True\n' + assumptions,
            assumptions.replace('Events.external_functions_sem\n', 'new_axiom\n', 1)]:
    rejected(lambda bad=bad: normal.assumptions(bad))
valid = json.loads((archive / 'REVIEW.json').read_text()); review.terminal(valid)
for key, value in [('public_jet_equivalence', True), ('scalar_mul_function_entry_alloc_free', False),
                   ('full_acceptance', True), ('checkout_coverage_added', 1), ('readable_nonowned_rhs', False), ('actual_output_loads_after_free', False)]:
    bad = copy.deepcopy(valid); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
for key in ['build', 'assumptions', 'contracts', 'kernel']:
    bad = copy.deepcopy(valid); bad[key]['exit_code'] = None
    rejected(lambda bad=bad: review.terminal(bad))
print(f'borrowed function review: positive fixtures and {count} corruption fixtures passed; no inputs changed')
