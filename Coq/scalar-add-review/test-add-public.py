"""Public boundary mutations in memory; no audit input is changed."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('scalar_add_public_gate',
    Path(__file__).with_name('check-add-public.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        raise SystemExit('usage: test-literal.py REPO SCRATCH COQ')
    args = list(map(Path, sys.argv[1:]))
    gate.check(*args)
    target = args[1] / 'jet_secp_scalar_add_local.v'
    fixtures = [
        ('f_simplicity_scalar_add', 'f_simplicity_scalar_normalize'),
        ('(@canonical_scalar_add Alg.CoreFunSem)', '(@canonical_add_word 8 Alg.CoreFunSem)'),
        ('(Ty.Prod (Word 8) (Word 8)) (Word 8)', '(Ty.Prod (Word 8) (Word 8)) (Word 9)'),
        ('scalar_add_literal_local_spec :', 'scalar_add_literal_local_spec : True ->'),
        ('Theorem scalar_add_literal_local_spec :', 'Theorem scalar_add_literal_local_spec : True. Proof. exact I. Qed.\nTheorem scalar_add_literal_local_spec :'),
    ]
    original = Path.read_text
    for old, new in fixtures:
        text = original(target)
        if old not in text:
            raise AssertionError('missing fixture: ' + old)
        changed = text.replace(old, new, 1)
        def read(p, *a, **kw):
            return changed if p == target else original(p, *a, **kw)
        with patch.object(Path, 'read_text', read):
            try:
                gate.check(*args)
            except (ValueError, AssertionError):
                pass
            else:
                raise AssertionError('mutation accepted: ' + old)
    gate.check(*args)
    print('exact scalar-add public contract matches; five public-boundary mutations rejected')
