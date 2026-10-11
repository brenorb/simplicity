"""In-memory public contract mutations; canonical ports tested separately."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('normalize_gate', Path(__file__).with_name('check-literal.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)

if __name__ == '__main__':
    if len(sys.argv) != 5:
        raise SystemExit('usage: test-literal.py REPO SCRATCH DEPENDENCIES COQ')
    args = list(map(Path, sys.argv[1:]))
    gate.check(*args)
    target = args[1] / 'jet_secp_scalar_normalize_local.v'
    original = Path.read_text
    baseline = original(target)
    for old, new in [
        ('f_simplicity_scalar_normalize (Word 8) (Word 8)', 'f_simplicity_scalar_is_zero (Word 8) (Word 8)'),
        ('f_simplicity_scalar_normalize (Word 8) (Word 8)', 'f_simplicity_scalar_normalize (Word 7) (Word 8)'),
        ('(@canonical_scalar_normalize Alg.CoreFunSem)', '(@canonical_scalar_is_zero Alg.CoreFunSem)'),
        ('(@canonical_scalar_normalize Alg.CoreFunSem)', '(fun x => x)'),
    ]:
        if old not in baseline:
            raise AssertionError('missing fixture')
        changed = baseline.replace(old, new, 1)
        def read(p, *a, **kw):
            return changed if p == target else original(p, *a, **kw)
        with patch.object(Path, 'read_text', read):
            try:
                gate.check(*args)
            except (ValueError, AssertionError):
                pass
            else:
                raise AssertionError('mutation accepted')
    gate.check(*args)
    print('literal public scalar normalize type checked; four in-memory contract mutations rejected')
