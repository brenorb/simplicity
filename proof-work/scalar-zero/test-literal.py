"""Reject public type/function/specification/width mutations in memory."""
from pathlib import Path
import importlib.util
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
archive = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('scalar_public_literal', archive / 'check-literal.py')
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)

if __name__ == '__main__':
    if len(sys.argv) != 4:
        raise SystemExit('usage: test-literal.py REPO SCRATCH COQ')
    repo, source, coq = map(Path, sys.argv[1:])
    gate.check(repo, source, coq)
    target = source / 'jet_secp_scalar_zero_local.v'
    original = Path.read_text
    baseline = original(target)
    mutations = [
        ('(@canonical_scalar_is_zero Alg.CoreFunSem).', '(fun _ => true).'),
        ('secp_jet_local_spec f_simplicity_scalar_is_zero',
         'secp_jet_local_spec f_simplicity_fe_is_zero'),
        ('(Word 8) Bit', '(Word 7) Bit'),
        ('secp_jet_local_spec f_simplicity_scalar_is_zero',
         'secp_jet_local_spec_restricted f_simplicity_scalar_is_zero'),
    ]
    for old, new in mutations:
        if old not in baseline:
            raise AssertionError('missing fixture')
        altered = baseline.replace(old, new, 1)

        def read(path, *args, **kwargs):
            return altered if path == target else original(path, *args, **kwargs)

        with patch.object(Path, 'read_text', read):
            try:
                gate.check(repo, source, coq)
            except (ValueError, AssertionError):
                pass
            else:
                raise AssertionError('public contract mutation accepted')
    gate.check(repo, source, coq)
    print('literal public contract matches; four public-contract mutations rejected')
