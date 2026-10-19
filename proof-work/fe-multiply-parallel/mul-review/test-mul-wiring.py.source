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
path = Path(__file__).with_name('check-mul-wiring.py')
loader = importlib.machinery.SourceFileLoader('field_mul_gate', str(path))
spec = importlib.util.spec_from_loader(loader.name, loader)
gate = importlib.util.module_from_spec(spec)
loader.exec_module(gate)
s = gate.load(a.repo, a.candidates, a.dependencies)
assert gate.check(s) == 13
mutations = [
    ('catalog', 'specificationSecp256k1 FeMultiply = Secp256k1.fe_multiply', 'specificationSecp256k1 FeMultiply = Secp256k1.scalar_multiply'),
    ('catalog', 'specificationSecp256k1 FeSquare = Secp256k1.fe_square', 'specificationSecp256k1 FeSquare = Secp256k1.fe_multiply'),
    ('catalog', 'FeMultiply :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE', 'FeMultiply :: Secp256k1Jet Secp256k1.FE Secp256k1.FE'),
    ('catalog', 'FeSquare :: Secp256k1Jet Secp256k1.FE Secp256k1.FE', 'FeSquare :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE'),
    ('program', 'fe_multiply = mul256 >>> fe_normalize512', 'fe_multiply = mul256 >>> scalar_normalize512'),
    ('program', 'fe_multiply = mul256 >>>', 'fe_multiply = add256 >>>'),
    ('program', 'fe_square = iden &&& iden >>> fe_multiply', 'fe_square = iden &&& iden >>> fe_add'),
    ('program', 'fe_square = iden &&& iden', 'fe_square = iden &&& unit'),
    ('program', 'mul256 = Arith.multiply word256', 'mul256 = Arith.multiply word128'),
    ('program', 'mod512 = Arith.modulo word512', 'mod512 = Arith.modulo word256'),
    ('program', '>>> mod512 >>> ih', '>>> mod512 >>> oh'),
    ('program', 'scribeFeOrder = scribe256 LibSecp256k1.fieldOrder', 'scribeFeOrder = scribe256 LibSecp256k1.groupOrder'),
    ('arith', 'multiply w = iden &&& (unit >>> zero (DoubleV w)) >>> full_multiply w', 'multiply w = iden &&& (unit >>> zero (DoubleV w)) >>> full_add w'),
    ('multiply', '(@zero (S n) term)', '(@zero n term)'),
    ('multiply', '(@fullMultiplier n term)', '(@fullAdder n term)'),
    ('normalize512', '@literal_modulo_word_spec 9 term', '@literal_modulo_word_spec 8 term'),
    ('normalize512', '>>> I H.', '>>> O H.'),
    ('normalize512', 'Alg.scribe canonical_field_word', 'Alg.scribe canonical_group_word'),
    ('normalize512', '@multiply_word_spec 8 term >>> @literal_fe_normalize512 term', '@multiply_word_spec 8 term >>> @canonical_fe_normalize512 term'),
    ('normalize512', '@multiply_word_spec 8 term', '@multiply_word_spec 7 term'),
    ('square', 'iden &&& iden >>> @literal_fe_multiply term', 'iden &&& iden >>> @literal_fe_add term'),
    ('square', 'iden &&& iden >>> @literal_fe_multiply term', 'iden >>> @literal_fe_negate term'),
    ('square', 'term (Word 8) (Word 8) :=', 'term (Word 8) (Word 9) :='),
    ('mul_local', 'Evar jets_secp._secp256k1_fe_mul (Tfunction', 'Evar jets_secp._secp256k1_fe_sqr (Tfunction'),
    ('mul_local', '''[Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._b secp_field_type) (tptr secp_field_type)]''', '''[Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._b secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._b secp_field_type) (tptr secp_field_type)]'''),
    ('mul_local', 'Ssequence (secp_read_field_stmt jets_secp._b)', 'Ssequence (secp_read_field_stmt jets_secp._a)'),
    ('mul_local', 'Ssequence secp_public_mul_stmt', 'Ssequence Sskip'),
    ('mul_local', 'secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word 8)) (Word 8)\n    (@literal_fe_multiply Alg.CoreFunSem).', 'False -> secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word 8)) (Word 8)\n    (@literal_fe_multiply Alg.CoreFunSem).'),
    ('mul_local', '(@literal_fe_multiply Alg.CoreFunSem).\nProof.', '(@literal_fe_add Alg.CoreFunSem).\nProof.'),
    ('mul_local', 'fn_body f_simplicity_fe_multiply =', 'fn_body f_simplicity_fe_add ='),
    ('mul_local', 'eapply secp_fe_mul_entry', 'eapply secp_fe_add_entry'),
    ('sqr_local', 'Evar jets_secp._secp256k1_fe_sqr (Tfunction', 'Evar jets_secp._secp256k1_fe_negate (Tfunction'),
    ('sqr_local', 'Ssequence secp_public_sqr_stmt', 'Ssequence Sskip'),
    ('sqr_local', 'secp_jet_local_spec f_simplicity_fe_square (Word 8) (Word 8)', 'secp_jet_local_spec f_simplicity_fe_negate (Word 8) (Word 8)'),
    ('sqr_local', '(@literal_fe_square Alg.CoreFunSem).\nProof.', '(@literal_fe_negate Alg.CoreFunSem).\nProof.'),
    ('sqr_local', 'fn_body f_simplicity_fe_square =', 'fn_body f_simplicity_fe_negate ='),
    ('sqr_local', 'secp_free_public_locals', 'secp_free_add_locals'),
    ('c', 'secp256k1_fe_mul(&a, &a, &b);', 'secp256k1_fe_mul(&a, &b, &a);'),
    ('c', 'read_fe(&b, &src);\n  secp256k1_fe_mul', 'read_fe(&b, &src);\n  read_fe(&b, &src);\n  secp256k1_fe_mul'),
    ('c', 'secp256k1_fe_sqr(&a, &a);', 'secp256k1_fe_mul(&a, &a, &a);'),
    ('c', 'bool simplicity_fe_square(frameItem* dst, frameItem src, const txEnv* env)', 'bool simplicity_fe_square(frameItem* dst, frameItem* src, const txEnv* env)'),
]
for key, old, new in mutations:
    assert old in s[key], (key, old)
    changed = dict(s)
    changed[key] = changed[key].replace(old, new, 1)
    try:
        gate.check(changed)
    except (ValueError, IndexError):
        pass
    else:
        raise AssertionError('mutation accepted: '+key+' '+old)
print(str(len(mutations))+' field multiply/square specification/lifecycle mutations rejected')
