"""Public square boundary mutations in memory, never edited audit inputs."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('square_gate', Path(__file__).with_name('check-square-public.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)


def run(repo, coq):
    gate.check(repo, coq)
    root = coq / 'C/jet_secp_scalar_square_local.v'
    canonical = coq / 'C/jet_secp_canonical_scalar_square.v'
    haskell = repo / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'
    original = Path.read_text
    fixtures = [
        (root, 'f_simplicity_scalar_square', 'f_simplicity_scalar_negate'),
        (root, '(@canonical_scalar_square Alg.CoreFunSem)', '(@canonical_scalar_normalize Alg.CoreFunSem)'),
        (root, '(Word 8) (Word 8)', '(Word 8) (Word 9)'),
        (root, 'scalar_square_literal_local_spec :', 'scalar_square_literal_local_spec : True ->'),
        (root, 'Theorem scalar_square_literal_local_spec :',
         'Theorem scalar_square_literal_local_spec : True. Proof. exact I. Qed.\nTheorem scalar_square_literal_local_spec :'),
        (canonical, 'iden &&& iden', 'iden &&& unit'),
        (haskell, 'scalar_square = iden &&& iden >>> scalar_multiply', 'scalar_square = iden'),
        (haskell, 'mkLib Sha256.Lib{..} = lib', 'different = lib'),
    ]
    for target, old, new in fixtures:
        text = original(target)
        if old not in text:
            raise AssertionError('missing mutation fixture: ' + old)
        changed = text.replace(old, new, 1)
        def read(path, *args, **kwargs):
            return changed if path == target else original(path, *args, **kwargs)
        with patch.object(Path, 'read_text', read):
            try:
                gate.check(repo, coq)
            except (ValueError, AssertionError):
                pass
            else:
                raise AssertionError('square mutation accepted: ' + old)
    gate.check(repo, coq); return len(fixtures)


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: test-square-public.py REPO COQ')
    print(f'{run(*map(Path, sys.argv[1:]))} square public-boundary mutations rejected')
