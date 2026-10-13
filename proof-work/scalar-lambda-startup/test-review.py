"""In-memory startup-evidence corruption tests; frozen inputs never change."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('startup_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text())
receipt = json.loads((archive / 'REVIEW.json').read_text()); work = Path(manifest['scratch'])
rs = [e['module'] + '.' + n for e in manifest['modules'] for n in e['results']]
ds = [e['module'] + '.' + n for e in manifest['modules'] for n in e['definitions']]
expected = [('TYPE', n) for n in rs] + [('DEF', n) for n in ds]
report = (work / 'lambda_startup_contracts.out').read_text(); review.contracts(report, expected)
count = 0


def rejected(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted startup evidence accepted')


for bad in [report + '...', report.replace('LAMBDA_STARTUP_TYPE ' + rs[0], 'LAMBDA_STARTUP_TYPE wrong', 1),
            report + 'LAMBDA_STARTUP_DEF unexpected\n', report.replace('LAMBDA_STARTUP_TYPE ' + rs[0], '', 1)]:
    rejected(lambda bad=bad: review.contracts(bad, expected))
review.terminal(receipt)
for kind in ['build', 'assumptions', 'contracts', 'kernel']:
    bad = copy.deepcopy(receipt); bad[kind]['exit_code'] = None
    rejected(lambda bad=bad: review.terminal(bad))
for key, value in [('actual_secp_initialization_exists', False), ('initialized_lambda_witness', False),
                   ('normal_registration', True), ('full_acceptance', True), ('checkout_coverage_added', 1)]:
    bad = copy.deepcopy(receipt); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
generic = (archive / 'jet_program_initialization.v.source').read_text()
concrete = (archive / 'jet_secp_scalar_lambda_init_exists.v.source').read_text()
review.boundary(generic, concrete)
for bad in [concrete.replace('jets_secp.prog', 'other_program'),
            concrete.replace('/\\ scalar_lambda_initialized m', '/\\ True'),
            concrete.replace('apply scalar_lambda_initialized_from_init; exact HI', 'exact assumed_state')]:
    rejected(lambda bad=bad: review.boundary(generic, bad))
rejected(lambda: review.boundary(generic.replace('apply Genv.init_mem_exists', 'exact assumed_existence'), concrete))
normal = review.load('startup_deps_test', archive.parent / 'scalar-multiply-integration/review-normal.py')
assumptions = (work / 'lambda_startup_assumptions.out').read_text()
for bad in [assumptions + 'JET_ASSUMPTIONS pending\n',
            assumptions + 'JET_ASSUMPTIONS ' + rs[0] + '\nClosed under the global context\n',
            assumptions.replace('Classical_Prop.classic :', 'invented_initializer :', 1)]:
    rejected(lambda bad=bad: normal.assumptions(bad))
print(f'lambda startup review: positive fixtures and {count} corruption fixtures passed; no inputs changed')
