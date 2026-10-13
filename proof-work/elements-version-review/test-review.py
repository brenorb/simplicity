"""In-memory corruption fixtures for the Version proof receipt/reports."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('version_evidence_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
sourcing = json.loads((archive / 'SOURCING.json').read_text())
receipt = json.loads((archive / 'REVIEW.json').read_text())
work = Path(sourcing['candidate'])
results = [e['module'] + '.' + n for e in sourcing['modules'] for n in e['results']]
wanted = [('TYPE', n) for n in results] + [('DEF', n) for n in receipt['contracts']['definitions']]
text = (work / 'version_contracts.out').read_text()
review.terminal(receipt); review.contracts(text, wanted)
count = 0


def reject(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted Version evidence accepted')


for field in ['build', 'assumptions', 'contracts', 'kernel', 'AST_regeneration',
              'selected_semantics', 'source_mutations']:
    bad = copy.deepcopy(receipt); bad[field]['exit_code'] = None
    reject(lambda bad=bad: review.terminal(bad))
for field, value in [('normal_registration', True), ('full_acceptance', True),
                     ('checkout_coverage_added', 1)]:
    bad = copy.deepcopy(receipt); bad[field] = value
    reject(lambda bad=bad: review.terminal(bad))
bad = copy.deepcopy(receipt); bad['AST_regeneration']['byte_identical'] = False
reject(lambda: review.terminal(bad))
bad = copy.deepcopy(receipt); bad['selected_semantics']['other_30_semantics_not_claimed'] = False
reject(lambda: review.terminal(bad))
for bad in [text + '...', text + 'ELEMENTS_VERSION_TYPE wrong\n',
            text.replace('ELEMENTS_VERSION_TYPE ' + results[0], '', 1)]:
    reject(lambda bad=bad: review.contracts(bad, wanted))
raw = (work / 'version_assumptions.out').read_text()
for bad in [raw + 'JET_ASSUMPTIONS pending\n',
            raw.replace('Events.external_functions_sem', 'invented_version_axiom', 1),
            raw + 'JET_ASSUMPTIONS ' + results[0] + '\nClosed under the global context\n']:
    reject(lambda bad=bad: review.normal.assumptions(bad))
print(f'Version evidence: positive fixtures and {count} corruptions rejected; frozen inputs unchanged')

