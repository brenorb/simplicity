"""In-memory corruption fixtures; no frozen proof or report is edited."""
import copy
import importlib.util
import json
from pathlib import Path
import sys

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('frames_test', archive / 'review.py')
review = importlib.util.module_from_spec(spec); spec.loader.exec_module(review)
manifest = json.loads((archive / 'manifest.json').read_text())
receipt = json.loads((archive / 'REVIEW.json').read_text())
work, base = Path(manifest['scratch']), Path(manifest['dependency_coq'])
results = [e['module'] + '.' + n for e in manifest['modules'] for n in e['results']]
defs = [e['module'] + '.' + n for e in manifest['modules'] for n in e['definitions']]
expected = [('TYPE', n) for n in results] + [('DEF', n) for n in defs]
report = (work / 'lambda_frames_contracts.out').read_text()
review.contracts(report, expected)
review.terminal(receipt)
count = 0


def rejected(action):
    global count
    try:
        action()
    except ValueError:
        count += 1
    else:
        raise AssertionError('corrupted frame/initialized contract accepted')


for bad in [report + '...', report.replace('LAMBDA_FRAMES_TYPE ' + results[0], '', 1),
            report + 'LAMBDA_FRAMES_DEF unexpected\n']:
    rejected(lambda bad=bad: review.contracts(bad, expected))
for kind in ['build', 'assumptions', 'contracts', 'kernel']:
    bad = copy.deepcopy(receipt); bad[kind]['exit_code'] = None
    rejected(lambda bad=bad: review.terminal(bad))
for key, value in [('actual_secp_initialization_exists', False), ('all_inputs_fresh_frames', False),
                   ('literal_original_call', False), ('initialized_local_contract', False),
                   ('startup_preserved', False), ('normal_registration', True),
                   ('full_acceptance', True), ('checkout_coverage_added', 1),
                   ('c_evaluator_setup_proved', True)]:
    bad = copy.deepcopy(receipt); bad[key] = value
    rejected(lambda bad=bad: review.terminal(bad))
contract = (archive / 'jet_secp_initialized_contract.v.source').read_text()
legacy = (base / 'C/jet_secp_normalize_local.v').read_text()
fresh = (archive / 'jet_secp_scalar_lambda_fresh.v.source').read_text()
local = (archive / 'jet_secp_scalar_lambda_local.v.source').read_text()
state = (archive / 'jet_secp_scalar_lambda_frame_state.v.source').read_text()
review.boundary(contract, legacy, fresh, local, state)
for old, new in [('Ready m ->', ''), ('/\\ Ready mf', ''),
                 ('frame_output_cells_at mf', 'frame_output_cells_at m'),
                 ('Int.one', 'Int.zero'), ('write_prefix_at m mf', 'True')]:
    rejected(lambda old=old, new=new: review.boundary(
        contract.replace(old, new), legacy, fresh, local, state))
for old, new in [('Genv.init_mem jets_secp.prog', 'Genv.init_mem other_program'),
                 ('scalar_lambda_initialized_memory_exists', 'assumed_ready'),
                 ('jet_frames_constructible', 'assumed_frames'),
                 ('canonical_scalar_multiply_lambda', 'constant_zero'),
                 ('Mem.load chunk mf b ofs', 'Mem.load chunk mi b ofs')]:
    rejected(lambda old=old, new=new: review.boundary(
        contract, legacy, fresh.replace(old, new), local, state))
for old, new in [('scalar_lambda_initialized f_simplicity_scalar_multiply_lambda', 'True wrong_function'),
                 ('canonical_scalar_multiply_lambda Alg.CoreFunSem', 'canonical_scalar_square Alg.CoreFunSem')]:
    rejected(lambda old=old, new=new: review.boundary(
        contract, legacy, fresh, local.replace(old, new), state))
rejected(lambda: review.boundary(contract, legacy, fresh, local,
                                  state.replace('scalar_lambda_words_readable m\'', 'assumed_readable m\'')))
normal = review.load('frames_negative_deps', archive.parent / 'scalar-multiply-integration/review-normal.py')
assumptions = (work / 'lambda_frames_assumptions.out').read_text()
for bad in [assumptions + 'JET_ASSUMPTIONS pending\n',
            assumptions + 'JET_ASSUMPTIONS ' + results[0] + '\nClosed under the global context\n',
            assumptions.replace('Classical_Prop.classic :', 'invented_frame_axiom :', 1)]:
    rejected(lambda bad=bad: normal.assumptions(bad))
print(f'lambda frames review: positive fixtures and {count} corruption fixtures passed; frozen inputs unchanged')

