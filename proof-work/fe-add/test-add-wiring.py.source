"""In-memory negative fixtures; never edit proof/audit inputs."""
import argparse
import importlib.machinery
import importlib.util
import sys
from pathlib import Path

sys.dont_write_bytecode = True
p = argparse.ArgumentParser()
p.add_argument('--repo', required=True)
p.add_argument('--candidates', required=True)
p.add_argument('--dependencies', required=True)
a = p.parse_args()
path = Path(__file__).with_name('check-add-wiring.py')
if not path.exists():
    path = path.with_suffix('.py.source')
loader = importlib.machinery.SourceFileLoader('field_add_gate', str(path))
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
s = gate.load(a.repo, a.candidates, a.dependencies)
assert gate.check(s) == 10
mutations = [
    ('catalog', 'specificationSecp256k1 FeAdd = Secp256k1.fe_add', 'specificationSecp256k1 FeAdd = Secp256k1.scalar_add'),
    ('catalog', 'FeAdd :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE', 'FeAdd :: Secp256k1Jet Secp256k1.FE Secp256k1.FE'),
    ('program', 'fe_add = add256 >>>', 'fe_add = mul256 >>>'),
    ('program', 'cond ((unit >>> one256) &&& iden) ((unit >>> zero256) &&& iden)', 'cond ((unit >>> zero256) &&& iden) ((unit >>> one256) &&& iden)'),
    ('program', 'fe_add = add256 >>> cond ((unit >>> one256) &&& iden)', 'fe_add = add256 >>> cond ((unit >>> zero256) &&& iden)'),
    ('program', '((unit >>> zero256) &&& iden) >>> fe_normalize512', '((unit >>> one256) &&& iden) >>> fe_normalize512'),
    ('program', '>>> fe_normalize512\n\n  , fe_negate', '\n\n  , fe_negate'),
    ('program', 'add256 = Arith.add word256', 'add256 = Arith.add word128'),
    ('program', 'one256 = Arith.one word256', 'one256 = Arith.one word128'),
    ('program', 'zero256 = Arith.zero word256', 'zero256 = Arith.zero word128'),
    ('program', 'mod512 = Arith.modulo word512', 'mod512 = Arith.modulo word256'),
    ('program', '>>> mod512 >>> ih', '>>> mod512 >>> oh'),
    ('program', 'scribeFeOrder = scribe256 LibSecp256k1.fieldOrder', 'scribeFeOrder = scribe256 LibSecp256k1.groupOrder'),
    ('arith', 'one w = true >>> left_pad_low word1 w', 'one w = false >>> left_pad_low word1 w'),
    ('arith', 'add w = false &&& iden >>> full_add w', 'add w = true &&& iden >>> full_add w'),
    ('word', 'left_pad_pad _ SingleV = iden', 'left_pad_pad _ SingleV = unit'),
    ('word', 'fill t v &&& left_pad_pad t v', 'left_pad_pad t v &&& fill t v'),
    ('word', 'left_pad_low w v = left_pad_pad (unit >>> low w) v', 'left_pad_low w v = left_pad_pad (unit >>> high w) v'),
    ('word', 'low = fill false', 'low = fill true'),
    ('padding', '(left_pad_low_1_n n)\n  end.', '(left_pad_low_1_n n) &&& iden\n  end.'),
    ('port', 'Bit.true >>> @left_pad_low_1_n term 8', 'Bit.false >>> @left_pad_low_1_n term 8'),
    ('port', '@left_pad_low_1_n term 8', '@left_pad_low_1_n term 7'),
    ('port', 'Bit.cond ((unit >>> @literal_fe_one256 term)', 'Bit.cond ((unit >>> @Word.zero 8 term)'),
    ('port', '((unit >>> @Word.zero 8 term) &&& iden)', '((unit >>> @literal_fe_one256 term) &&& iden)'),
    ('port', '@canonical_add_word 8 term', '@canonical_add_word 7 term'),
    ('port', '>>> @literal_fe_add_expand term', ''),
    ('port', '>>> @literal_fe_normalize512 term', ''),
    ('port', 'term (Ty.Prod (Word 8) (Word 8)) (Word 8)', 'term (Word 8) (Word 8)'),
    ('add', 'Bit.false &&& iden >>> @Word.fullAdder n term', 'Bit.true &&& iden >>> @Word.fullAdder n term'),
    ('normalize512', '@literal_modulo_word_spec 9 term', '@literal_modulo_word_spec 8 term'),
    ('normalize512', '>>> I H.', '>>> O H.'),
    ('normalize512', 'Alg.scribe canonical_field_word', 'Alg.scribe canonical_group_word'),
    ('body', 'PTree.set jets_secp._b', 'PTree.set jets_secp._a'),
    ('body', 'Ssequence (secp_read_field_stmt jets_secp._b)', 'Ssequence (secp_read_field_stmt jets_secp._a)'),
    ('body', 'Ssequence secp_public_add_stmt', 'Ssequence Sskip'),
    ('body', 'Ssequence secp_public_write_stmt', 'Ssequence Sskip'),
    ('body', '(Int.repr 1) tint', '(Int.repr 0) tint'),
    ('body', 'Evar jets_secp._secp256k1_fe_add', 'Evar jets_secp._secp256k1_fe_negate'),
    ('body', 'Evar jets_secp._b secp_field_type', 'Evar jets_secp._a secp_field_type'),
    ('body', 'fn_body f_simplicity_fe_add', 'fn_body f_simplicity_fe_multiply'),
    ('entry', '[(bl,0,16);(ba,0,40);(bb,0,40)]', '[(bl,0,16);(ba,0,40)]'),
    ('entry', '(bb,0,40)', '(bb,0,32)'),
    ('lifecycle', 'secp_free_add_locals', 'secp_free_public_locals'),
    ('lifecycle', 'eapply secp_fe_add_entry', 'eapply secp_fe_normalize_entry'),
    ('local', 'secp_jet_local_spec f_simplicity_fe_add', 'False -> secp_jet_local_spec f_simplicity_fe_add'),
    ('local', 'f_simplicity_fe_add', 'f_simplicity_fe_multiply'),
    ('local', '(Ty.Prod (Word 8) (Word 8))', '(Word 8)'),
    ('local', '(@literal_fe_add Alg.CoreFunSem)', '(@canonical_fe_add Alg.CoreFunSem)'),
    ('c', 'read_fe(&b, &src);', ''),
    ('c', 'secp256k1_fe_add(&a, &b);', 'secp256k1_fe_add(&a, &a);'),
    ('c', 'write_fe(dst, &a);', 'write_fe(dst, &b);'),
    ('c', 'bool simplicity_fe_add(frameItem* dst, frameItem src, const txEnv* env)', 'bool simplicity_fe_add(frameItem* dst, frameItem* src, const txEnv* env)'),
]
for key, old, new in mutations:
    assert old in s[key], (key, old)
    changed = dict(s)
    changed[key] = changed[key].replace(old, new)
    try:
        gate.check(changed)
    except (ValueError, IndexError):
        pass
    else:
        raise AssertionError('mutation accepted: '+key+' '+old)
print(str(len(mutations))+' field-add specification/lifecycle mutations rejected')
