"""Negative fixtures are in-memory only; no frozen source is edited."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('lambda_caller_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text())
receipt = json.loads((archive / 'REVIEW.json').read_text()); work = Path(manifest['scratch']['caller'])
sources = {e['file']: (archive / (e['file'] + '.source')).read_text() for e in manifest['modules']}
rs = [e['module'] + '.' + n for e in manifest['modules'] for n in e['results']]
ds = [e['module'] + '.' + n for e in manifest['modules'] for n in e['definitions']]
expected = [('TYPE', n) for n in rs] + [('DEF', n) for n in ds]
report = (work / 'lambda_caller_contracts.out').read_text(); review.contracts(report, expected)
count = 0


def rejected(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted lambda caller evidence accepted')


for bad in [report + '...', report.replace('LAMBDA_CALLER_TYPE ' + rs[0], 'LAMBDA_CALLER_TYPE wrong', 1),
            report + 'LAMBDA_CALLER_DEF unexpected\n', report.replace('LAMBDA_CALLER_TYPE ' + rs[0], '', 1)]:
    rejected(lambda bad=bad: review.contracts(bad, expected))
review.terminal(receipt)
for kind in ['build', 'assumptions', 'contracts', 'kernel']:
    bad = copy.deepcopy(receipt); bad[kind]['exit_code'] = None
    rejected(lambda bad=bad: review.terminal(bad))
for key, value in [('complete_original_public_funcall', False), ('startup_state_preserved', False),
                   ('normal_registration', True), ('full_acceptance', True), ('checkout_coverage_added', 1),
                   ('init_mem_existence_proved', True)]:
    bad = copy.deepcopy(receipt); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
review.call_boundary(sources)
for file, before, after in [
    ('jet_secp_scalar_lambda_initialized.v', 'Ctypes.Internal f_simplicity_scalar_multiply_lambda',
     'Ctypes.Internal f_secp256k1_scalar_mul'),
    ('jet_secp_scalar_lambda_initialized.v', 'encode (@canonical_scalar_multiply_lambda Alg.CoreFunSem value)', '[]'),
    ('jet_secp_scalar_lambda_initialized.v', 'scalar_lambda_global_rep m /\\ readonly_region_bounds m scalar_lambda_block 0 32', 'True'),
    ('jet_secp_scalar_lambda_lifecycle.v', 'scalar_free_public_locals', 'assumed_cleanup'),
    ('jet_secp_scalar_lambda_rest.v', 'eapply eval_Evar_global; [reflexivity|exact scalar_lambda_global_symbol]',
     'apply eval_Evar_local; reflexivity'),
    ('jet_clight_readonly_frame.v', 'Mem.range_perm mf b lo hi Cur Readable', 'True'),
]:
    assert before in sources[file]
    bad = dict(sources); bad[file] = bad[file].replace(before, after)
    rejected(lambda bad=bad: review.call_boundary(bad))
normal = review.load('lambda_caller_dep_test', archive.parent / 'scalar-multiply-integration/review-normal.py')
assumptions = (work / 'lambda_caller_assumptions.out').read_text()
assert normal.assumptions(assumptions) == {n: set(d) for n, d in receipt['reviewed_dependencies'].items()}
for bad in [assumptions + 'JET_ASSUMPTIONS pending\n',
            assumptions + 'JET_ASSUMPTIONS ' + rs[0] + '\nClosed under the global context\n',
            assumptions.replace('Events.external_functions_properties\n', 'fabricated_model\n', 1)]:
    rejected(lambda bad=bad: normal.assumptions(bad))
print(f'lambda caller review: positive fixtures and {count} corruption fixtures passed; frozen inputs unchanged')
