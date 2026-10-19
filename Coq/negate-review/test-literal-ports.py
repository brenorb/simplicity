"""Pure source mutations for the literal-add ports and full public theorem."""
import argparse
import importlib.machinery
import importlib.util
from pathlib import Path

p = argparse.ArgumentParser()
p.add_argument('--repo', required=True)
p.add_argument('--candidates', required=True)
args = p.parse_args()
path = Path(__file__).with_name('check-literal-ports.py.source')
if not path.exists(): path = path.with_suffix('')
loader = importlib.machinery.SourceFileLoader('literal_gate', str(path))
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
h, parser, sources = gate.load(args.repo, args.candidates, path.parent)
assert gate.check(h, parser, sources) == 14
mutations = [
    ('division', '@canonical_add_word n term', '@Word.adder n term'),
    ('division', '@canonical_add_word (S n) term', '@Word.adder (S n) term'),
    ('division', '@literal_div2n1n_word_spec n term', '@div2n1n_word_spec n term'),
    ('division', '@literal_div3n2n_loop2_spec n term', '@div3n2n_loop2_spec n term'),
    ('division', '@literal_div3n2n_word_builder n term', '@div3n2n_word_builder n term'),
    ('division', '@literal_div_mod_word_spec n term >>> I H', '@literal_div_mod_word_spec n term >>> O H'),
    ('add', 'Bit.false &&& iden', 'Bit.true &&& iden'),
    ('add', '@Word.fullAdder n term', '@Word.fullAdder (S n) term'),
    ('field', '@literal_modulo_word_spec 9 term', '@modulo_word_spec 9 term'),
    ('field', '@literal_modulo_word_spec 9 term', '@literal_modulo_word_spec 8 term'),
    ('field', '>>> I H.', '>>> O H.'),
    ('field', 'Alg.scribe canonical_negate_factor', 'Alg.scribe canonical_field_word'),
    ('field', 'secp_jet_local_spec f_simplicity_fe_negate', 'False -> secp_jet_local_spec f_simplicity_fe_negate'),
    ('field', 'secp_jet_local_spec f_simplicity_fe_negate', 'secp_jet_local_spec f_simplicity_fe_normalize'),
    ('field', '(@literal_fe_negate Alg.CoreFunSem).', '(@canonical_fe_negate Alg.CoreFunSem).'),
]
for key, old, new in mutations:
    assert old in sources[key], (key, old)
    changed = dict(sources)
    changed[key] = changed[key].replace(old, new)
    try:
        gate.check(h, parser, changed)
    except ValueError:
        pass
    else:
        raise AssertionError('accepted literal port mutation '+key+' '+old)
print(str(len(mutations))+' literal-add/final-contract mutations rejected')
