"""Read-only literal correspondence fixtures; all mutations are in memory."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('scalar_add_gate', Path(__file__).with_name('check-add-bridge.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


if __name__ == '__main__':
    if len(sys.argv) != 4:
        raise SystemExit('usage: test-literal.py REPO SCRATCH COQ')
    args = list(map(Path, sys.argv[1:]))
    gate.check(*args)
    port = args[1] / 'jet_secp_canonical_scalar_add.v'
    carry = args[2] / 'C/jet_secp_literal_add_program.v'
    normalize = args[2] / 'C/jet_secp_canonical_scalar_negate.v'
    program = args[0] / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'
    catalog = args[0] / 'Haskell/Core/Simplicity/CoreJets.hs'
    fixtures = [
        (port, '@canonical_add_word 8 term', '@canonical_add_word 7 term'),
        (port, '>>> @literal_fe_add_expand term', ''),
        (port, '@canonical_scalar_normalize512 term', '@literal_fe_normalize512 term'),
        (port, 'term (Ty.Prod (Word 8) (Word 8)) (Word 8)', 'term (Ty.Prod (Word 8) (Word 8)) (Word 9)'),
        (carry, 'Bit.cond ((unit >>> @literal_fe_one256 term)', 'Bit.cond ((unit >>> @Word.zero 8 term)'),
        (normalize, '@literal_modulo_word_spec 9 term', '@modulo_word_spec 9 term'),
        (normalize, '>>> @literal_modulo_word_spec 9 term >>> I H', '>>> @literal_modulo_word_spec 9 term >>> O H'),
        (program, 'scalar_add = add256 >>> cond', 'scalar_add = sub256 >>> cond'),
        (catalog, 'specificationSecp256k1 ScalarAdd = Secp256k1.scalar_add', 'specificationSecp256k1 ScalarAdd = Secp256k1.fe_add'),
        (port, 'Definition canonical_scalar_add', 'Definition canonical_scalar_add {term : Alg.Core.Algebra} := @canonical_add_word 8 term.\nDefinition canonical_scalar_add'),
    ]
    original = Path.read_text
    for target, old, new in fixtures:
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
    print('literal scalar-add and reused recursive ports match; ten in-memory wiring mutations rejected')
