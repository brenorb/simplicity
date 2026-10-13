"""In-memory initialized lambda public-boundary mutations."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('lambda_gate', Path(__file__).with_name('check-lambda-public.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)


def run(repo, coq):
    gate.check(repo, coq)
    root = coq / 'C/jet_secp_scalar_lambda_local.v'
    contract = coq / 'C/jet_secp_initialized_contract.v'
    canonical = coq / 'C/jet_secp_canonical_scalar_lambda.v'
    ready = coq / 'C/jet_secp_scalar_lambda_initialized.v'
    global_src = coq / 'C/jet_secp_scalar_lambda_global.v'
    readonly = coq / 'C/jet_clight_readonly_frame.v'
    fresh = coq / 'C/jet_secp_scalar_lambda_fresh.v'
    haskell = repo / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'
    value = repo / 'Haskell/Core/Simplicity/LibSecp256k1/Spec.hs'
    catalog = repo / 'Haskell/Core/Simplicity/CoreJets.hs'
    fixtures = [
        (root, 'f_simplicity_scalar_multiply_lambda', 'f_simplicity_scalar_square'),
        (root, '(Word 8) (Word 8)', '(Word 8) (Word 9)'),
        (root, '(@canonical_scalar_multiply_lambda Alg.CoreFunSem)', '(@canonical_scalar_square Alg.CoreFunSem)'),
        (root, 'scalar_lambda_initialized f_simplicity', 'True f_simplicity'),
        (root, 'scalar_lambda_initialized_local_spec :', 'scalar_lambda_initialized_local_spec : False ->'),
        (root, 'Theorem scalar_lambda_initialized_local_spec :',
         'Theorem scalar_lambda_initialized_local_spec : True. Proof. exact I. Qed.\nTheorem scalar_lambda_initialized_local_spec :'),
        (contract, 'Ready m ->', ''),
        (contract, '/\\ Ready mf', ''),
        (contract, 'frame_output_cells_at mf', 'frame_output_cells_at m'),
        (contract, 'write_prefix_at m mf', 'True'),
        (contract, 'Int.one', 'Int.zero'),
        (canonical, '(unit >>> @canonical_scalar_lambda term) &&& iden', 'iden &&& iden'),
        (canonical, 'Alg.scribe canonical_lambda_word', 'Alg.scribe canonical_zero'),
        (canonical, '@fromZ (WordToZ 8) canonical_lambda_value', '@fromZ (WordToZ 8) 0'),
        (ready, 'readonly_region_bounds m scalar_lambda_block 0 32', 'True'),
        (global_src, 'secp_symbol_block _secp256k1_const_lambda', '123%positive'),
        (global_src, 'Int64.repr 1310022930574435960', 'Int64.repr 0'),
        (global_src, 'Mem.range_perm m scalar_lambda_block 0 32', 'Mem.range_perm m scalar_lambda_block 0 0'),
        (readonly, 'perm_order Readable p', 'perm_order Writable p'),
        (fresh, 'scalar_lambda_runs_from_actual_init (value : Ty.tySem (Word 8)) env :',
         'scalar_lambda_runs_from_actual_init (value : Ty.tySem (Word 8)) env : False ->'),
        (fresh, 'Genv.init_mem jets_secp.prog', 'Genv.init_mem other_program'),
        (haskell, 'scalar_multiply_lambda = (unit >>> scalar_lambda) &&& iden >>> scalar_multiply',
         'scalar_multiply_lambda = iden'),
        (haskell, 'scalar_lambda = scribe256 LibSecp256k1.lambda', 'scalar_lambda = scribe256 0'),
        (value, 'lambda = 0x5363ad4cc05c30e0a5261c028812645a122e22ea20816678df02967c1b23bd72', 'lambda = 0x01'),
        (catalog, 'specificationSecp256k1 ScalarMultiplyLambda = Secp256k1.scalar_multiply_lambda',
         'specificationSecp256k1 ScalarMultiplyLambda = Secp256k1.scalar_square'),
    ]
    original = Path.read_text
    for target, old, new in fixtures:
        text = original(target)
        if old not in text:
            raise AssertionError('missing mutation fixture: ' + old)
        # On fresh-startup fixtures, mutate the theorem, not the earlier
        # Local Opaque list mentioning init_mem.
        start = text.index('Theorem scalar_lambda_runs_from_actual_init') if target == fresh else 0
        if old not in text[start:]:
            raise AssertionError('missing statement mutation fixture: ' + old)
        changed = text[:start] + text[start:].replace(old, new, 1)
        def read(path, *args, **kwargs):
            return changed if path == target else original(path, *args, **kwargs)
        with patch.object(Path, 'read_text', read):
            try:
                gate.check(repo, coq)
            except (ValueError, AssertionError):
                pass
            else:
                raise AssertionError('lambda mutation accepted: ' + old)
    gate.check(repo, coq); return len(fixtures)


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: test-lambda-public.py REPO COQ')
    print(f'{run(*map(Path, sys.argv[1:]))} lambda public-boundary mutations rejected')

