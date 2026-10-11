"""In-memory wiring mutations, without modifying any running audit input."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('scalar_negate_gate', Path(__file__).with_name('check-literal.py'))
gate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(gate)


if __name__ == '__main__':
    if len(sys.argv) != 5:
        raise SystemExit('usage: test-literal.py REPO SCRATCH DEPENDENCIES COQ')
    args = list(map(Path, sys.argv[1:]))
    gate.check(*args)
    port = args[1] / 'jet_secp_canonical_scalar_negate.v'
    program = args[0] / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'
    catalog = args[0] / 'Haskell/Core/Simplicity/CoreJets.hs'
    fixtures = [
        (port, '(unit >>> Alg.scribe canonical_scalar_negate_factor)', 'Alg.scribe canonical_scalar_negate_factor'),
        (port, '@literal_modulo_word_spec 9 term', '@modulo_word_spec 9 term'),
        (port, '>>> @literal_modulo_word_spec 9 term >>> I H', '>>> @literal_modulo_word_spec 9 term >>> O H'),
        (port, '@multiply_word_spec 8 term', '@multiply_word_spec 7 term'),
        (port, '((-1) mod canonical_group_order)', '((-2) mod canonical_group_order)'),
        (port, 'Alg.scribe canonical_group_word', 'Alg.scribe canonical_field_word'),
        (program, 'scalar_negate = (unit >>> scribe256 ((-1)', 'scalar_negate = (unit >>> scribe256 ((-2)'),
        (catalog, 'specificationSecp256k1 ScalarNegate = Secp256k1.scalar_negate',
         'specificationSecp256k1 ScalarNegate = Secp256k1.fe_negate'),
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
    print('literal scalar-negate and recursive ports match; eight in-memory wiring mutations rejected')
