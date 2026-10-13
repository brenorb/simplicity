"""Meaningful negative fixtures, applied in memory to the scoped source gate."""
import argparse
import importlib.util
from pathlib import Path
import sys
sys.dont_write_bytecode = True
spec=importlib.util.spec_from_file_location('gate',Path(__file__).with_name('check-infinity-wiring.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
p=argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('--candidates',required=True)
a=p.parse_args();s=gate.load(a.repo,a.candidates);gate.check(s)
mutations=[
 ('catalog','GejInfinity :: Secp256k1Jet () Secp256k1.GEJ','GejInfinity :: Secp256k1Jet Secp256k1.FE Secp256k1.GEJ'),
 ('catalog','specificationSecp256k1 GejInfinity = Secp256k1.gej_infinity','specificationSecp256k1 GejInfinity = Secp256k1.gej_double'),
 ('program','zero256 = Arith.zero word256','zero256 = Arith.zero word128'),
 ('program',', fe_zero = zero256',', fe_zero = one256'),
 ('program','(zero &&& zero) &&& zero','zero &&& (zero &&& zero)'),
 ('program','zero = fe_zero','zero = fe_one'),
 ('arith','zero = low','zero = high'),
 ('word','low = fill false','low = fill true'),
 ('word','fill t SingleV = t','fill t SingleV = unit'),
 ('word','fill t (DoubleV w) = rec &&& rec','fill t (DoubleV w) = rec'),
 ('word','rec = fill t w','rec = fill t SingleV'),
 ('zero','| 0 => false','| 0 => true'),
 ('zero','| S n => zero &&& zero','| S n => zero'),
 ('port','@Word.zero 8 term','@Word.zero 7 term'),
 ('port','(@literal_fe_zero256 term &&& @literal_fe_zero256 term) &&& @literal_fe_zero256 term','@literal_fe_zero256 term &&& (@literal_fe_zero256 term &&& @literal_fe_zero256 term)'),
 ('entry','Mem.alloc m 0 16','Mem.alloc m 0 8'),
 ('entry','Mem.alloc ma 0 128','Mem.alloc ma 0 40'),
 ('entry','function_entry2 secp_ge f_simplicity_gej_infinity','function_entry2 secp_ge f_simplicity_gej_double'),
 ('lifecycle','[(bl,0,16);(ba,0,128)]','[(bl,0,16)]'),
 ('lifecycle','Mem.free_list m','Mem.free_list m0'),
 ('call','gej_prepare_public_locals','gej_prepare_assumed_locals'),
 ('call','exec_gej_public_rest_owned','exec_gej_public_rest_from_calls'),
 ('call','gej_free_public_locals mw bl ba','gej_free_public_locals mi bl ba'),
 ('call','+ exact HFree.','+ exact HAssumedFree.'),
 ('local','secp_jet_local_spec f_simplicity_gej_infinity','False -> secp_jet_local_spec f_simplicity_gej_infinity'),
 ('local','f_simplicity_gej_infinity','f_simplicity_gej_double'),
 ('local','Ty.Unit (Ty.Prod','(Word 8) (Ty.Prod'),
 ('local','(@literal_gej_infinity Alg.CoreFunSem)','(@numeric_gej_infinity Alg.CoreFunSem)'),
 ('c','secp256k1_gej_set_infinity(&a);','secp256k1_gej_set_ge(&a, &g);'),
 ('c','write_gej(dst, &a);','write_gej(dst, &b);'),
 ('c','write_fe(dst, &r->y);','write_fe(dst, &r->x);'),
 ('c','write_fe(dst, &r->z);',''),
]
for app in ['bitcoin','elements']:
    # Restrict substitutions to this registration, not other jets.
    m=__import__('re').search(r'\[GEJ_INFINITY\].*?\.cost',s[app],__import__('re').S)
    for old,new in [('.jet = simplicity_gej_infinity','.jet = simplicity_gej_double'),
                    ('.sourceIx = ty_u','.sourceIx = ty_w256'),
                    ('.targetIx = ty_pw512w256','.targetIx = ty_w256')]:
        mutations.append((app,m[0],m[0].replace(old,new)))
for key,old,new in mutations:
    assert old in s[key],(key,old)
    changed=dict(s);changed[key]=s[key].replace(old,new)
    try:gate.check(changed)
    except (ValueError,IndexError):pass
    else:raise AssertionError('mutation accepted: '+key+' '+old)
print(str(len(mutations))+' infinity specification/lifecycle mutations rejected')
