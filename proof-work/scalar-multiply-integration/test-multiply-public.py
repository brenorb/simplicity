"""Public-boundary mutations in memory; never modify acceptance inputs."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('multiply_public_gate',
    Path(__file__).with_name('check-multiply-public.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


def run(repo, coq):
    gate.check(repo, coq)
    target = coq / 'C/jet_secp_scalar_multiply_local.v'
    original = Path.read_text
    fixtures = [
        ('f_simplicity_scalar_multiply', 'f_simplicity_scalar_normalize'),
        ('(@canonical_scalar_multiply Alg.CoreFunSem)', '(@multiply_word_spec 8 Alg.CoreFunSem)'),
        ('(Ty.Prod (Word 8) (Word 8)) (Word 8)', '(Ty.Prod (Word 8) (Word 8)) (Word 9)'),
        ('scalar_multiply_literal_local_spec :', 'scalar_multiply_literal_local_spec : True ->'),
        ('Theorem scalar_multiply_literal_local_spec :',
         'Theorem scalar_multiply_literal_local_spec : True. Proof. exact I. Qed.\n'
         'Theorem scalar_multiply_literal_local_spec :'),
    ]
    for old, new in fixtures:
        text = original(target)
        if old not in text:
            raise AssertionError('missing fixture: ' + old)
        changed = text.replace(old, new, 1)
        def read(path, *args, **kwargs):
            return changed if path == target else original(path, *args, **kwargs)
        with patch.object(Path, 'read_text', read):
            try:
                gate.check(repo, coq)
            except (ValueError, AssertionError):
                pass
            else:
                raise AssertionError('mutation accepted: ' + old)
    gate.check(repo, coq)
    return len(fixtures)


if __name__ == '__main__':
    if len(sys.argv) != 3:
        raise SystemExit('usage: test-multiply-public.py REPO COQ')
    print(f'{run(*map(Path, sys.argv[1:]))} public-boundary mutations rejected')
