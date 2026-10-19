"""Pure-source mutations: no candidate or accepted input is written."""
import argparse
import importlib.machinery
import importlib.util
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--repo', required=True)
p.add_argument('--candidates', required=True)
args = p.parse_args()
path = Path(__file__).with_name('check-negate-wiring.py.source')
if not path.exists(): path = path.with_suffix('')
loader = importlib.machinery.SourceFileLoader('negate_gate', str(path))
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
sources = gate.load_sources(args.repo, args.candidates)
assert gate.check(sources)
mutations = [
    ('catalog', 'specificationSecp256k1 FeNegate = Secp256k1.fe_negate',
     'specificationSecp256k1 FeNegate = Secp256k1.fe_normalize'),
    ('catalog', 'FeNegate :: Secp256k1Jet Secp256k1.FE Secp256k1.FE',
     'FeNegate :: Secp256k1Jet Bit Secp256k1.FE'),
    ('program', 'fe_negate = fe_multiplyInt (-1)', 'fe_negate = fe_multiplyInt 1'),
    ('program', 'mul256 = Arith.multiply word256', 'mul256 = Arith.multiply word128'),
    ('program', 'mod512 = Arith.modulo word512', 'mod512 = Arith.modulo word256'),
    ('program', '>>> mod512 >>> ih', '>>> mod512 >>> oh'),
    ('program', 'fe_multiply = mul256 >>> fe_normalize512', 'fe_multiply = mul256'),
    ('program', 'scribe256 (i `mod` LibSecp256k1.fieldOrder)', 'scribe256 i'),
    ('arith', 'modulo w = div_mod w >>> ih', 'modulo w = div_mod w >>> oh'),
    ('arith', 'zero (DoubleV w)', 'zero w'),
    ('port', '@modulo_word_spec 9 term', '@modulo_word_spec 8 term'),
    ('port', '((-1) mod canonical_field_order)', '(1 mod canonical_field_order)'),
    ('port', '>>> I H.', '>>> O H.'),
    ('port', '@multiply_word_spec 8 term', '@multiply_word_spec 7 term'),
    ('multiply', '(@zero (S n) term)', '(@zero n term)'),
    ('division', '@div_mod_word_spec n term >>> I H.', '@div_mod_word_spec n term >>> O H.'),
    ('local', 'secp_jet_local_spec f_simplicity_fe_negate', 'False -> secp_jet_local_spec f_simplicity_fe_negate'),
    ('local', 'f_simplicity_fe_negate', 'f_simplicity_fe_normalize'),
    ('local', '(@canonical_fe_negate Alg.CoreFunSem)', '(@canonical_fe_normalize Alg.CoreFunSem)'),
]
for key, old, new in mutations:
    assert old in sources[key], (key, old)
    changed = dict(sources)
    changed[key] = changed[key].replace(old, new)
    try:
        gate.check(changed)
    except (ValueError, IndexError):
        pass
    else:
        raise AssertionError('mutation accepted: '+key+' '+old)
print(str(len(mutations))+' meaningful negation wiring mutations rejected')
