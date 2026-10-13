"""Negative fixtures for the supplemental point-predicate source gate."""
import argparse
import importlib.util
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location('gate', Path(__file__).with_name('check-gej-predicate-wiring.py'))
gate = importlib.util.module_from_spec(spec); spec.loader.exec_module(gate)
p = argparse.ArgumentParser()
p.add_argument('--repo', required=True); p.add_argument('--candidates', required=True)
p.add_argument('--dependencies', required=True)
a = p.parse_args(); s = gate.load(a.repo,a.candidates,a.dependencies); gate.check(s)
mutations = [
 ('catalog','GejIsInfinity :: Secp256k1Jet Secp256k1.GEJ Bit','GejIsInfinity :: Secp256k1Jet Secp256k1.FE Bit'),
 ('catalog','specificationSecp256k1 GejIsInfinity = Secp256k1.gej_is_infinity','specificationSecp256k1 GejIsInfinity = Secp256k1.gej_double'),
 ('catalog','implementationSecp256k1 GejIsInfinity = FFI.gej_is_infinity','implementationSecp256k1 GejIsInfinity = FFI.gej_double'),
 ('program','gej_is_infinity = drop fe_is_zero','gej_is_infinity = take fe_is_zero'),
 ('program','gej_is_infinity = drop fe_is_zero','gej_is_infinity = drop fe_is_odd'),
 ('port','Alg.Core.Combinators.drop (@canonical_fe_is_zero term)','Alg.Core.Combinators.take (@canonical_fe_is_zero term)'),
 ('port','@canonical_fe_is_zero term','@numeric_fe_is_zero term'),
 ('entry','Mem.alloc m 0 16','Mem.alloc m 0 8'),
 ('entry','Mem.alloc ma 0 128','Mem.alloc ma 0 40'),
 ('entry','f_simplicity_gej_is_infinity','f_simplicity_gej_infinity'),
 ('entry','create_undef_temps','create_defined_temps'),
 ('entry','PTree.set _dst','PTree.set _src'),
 ('lifecycle','[(bl,0,16);(ba,0,128)]','[(bl,0,16)]'),
 ('lifecycle','Mem.free_list m','Mem.free_list m0'),
 ('call','gej_prepare_owned_locals','gej_prepare_assumed_locals'),
 ('call','exec_gej_predicate_rest_owned','exec_gej_predicate_rest_from_calls'),
 ('call','gej_free_public_locals mw bl ba','gej_free_public_locals mi bl ba'),
 ('call','+ exact HFree.','+ exact HAssumedFree.'),
 ('call','eapply gej_predicate_public_entry','eapply gej_infinity_public_entry'),
 ('call','rewrite gej_predicate_body','rewrite gej_public_body'),
 ('local','secp_jet_local_spec f_simplicity_gej_is_infinity','False -> secp_jet_local_spec f_simplicity_gej_is_infinity'),
 ('local','Word 8','Word 7'),
 ('local','(Ty.Sum Ty.Unit Ty.Unit)','Ty.Unit'),
 ('local','@literal_gej_is_infinity Alg.CoreFunSem','@numeric_gej_is_infinity Alg.CoreFunSem'),
 ('c','read_gej(&a, &src);',''),
 ('c','writeBit(dst, secp256k1_gej_is_infinity(&a));','writeBit(dst, false);'),
 ('c','read_fe(&r->y, src);','read_fe(&r->x, src);'),
 ('c','read_fe(&r->z, src);',''),
 ('c','r->infinity = secp256k1_fe_is_zero(&r->z);','r->infinity = secp256k1_fe_is_zero(&r->x);'),
 ('group','return a->infinity;','return a->x;'),
]
# Target the public function return only, not unrelated C functions.
m = re.search(r'bool simplicity_gej_is_infinity\([^)]*\)\s*\{[^{}]*\}', s['c'], re.S)
mutations.append(('c', m[0], m[0].replace('return true;', 'return false;')))
for app in ['bitcoin','elements']:
    m = re.search(r'\[GEJ_IS_INFINITY\].*?\.cost', s[app], re.S)
    for old,new in [('.jet = simplicity_gej_is_infinity','.jet = simplicity_gej_double'),
                    ('.sourceIx = ty_pw512w256','.sourceIx = ty_w256'),
                    ('.targetIx = ty_b','.targetIx = ty_u')]:
        assert old in m[0], (app,old)
        mutations.append((app,m[0],m[0].replace(old,new)))
for key,old,new in mutations:
    assert old in s[key] and old != new, (key,old)
    changed = dict(s); changed[key] = s[key].replace(old,new)
    try: gate.check(changed)
    except (ValueError,IndexError): pass
    else: raise AssertionError('mutation accepted: '+key+' '+old)
print(str(len(mutations))+' point-predicate specification/lifecycle mutations rejected')
