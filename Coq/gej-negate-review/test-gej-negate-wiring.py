"""Mutation fixtures for the supplemental point-negate source gate."""
import argparse
import importlib.util
from pathlib import Path
import re
import sys
sys.dont_write_bytecode=True
spec=importlib.util.spec_from_file_location('gate',Path(__file__).with_name('check-gej-negate-wiring.py'))
gate=importlib.util.module_from_spec(spec);spec.loader.exec_module(gate)
p=argparse.ArgumentParser()
for n in ['repo','candidates','dependencies']:p.add_argument('--'+n,required=True)
a=p.parse_args();s=gate.load(a.repo,a.candidates,a.dependencies);gate.check(s)
mutations=[]
for key,fragments in gate.FRAGMENTS.items():
    for fragment in fragments:
        # Each required active binding must independently be necessary.
        mutations.append((key,fragment,'BROKEN_BINDING'))
mutations += [
 ('program','gej_negate = take ge_negate &&& drop fe_normalize','gej_negate = take ge_negate &&& drop fe_negate'),
 ('program','ge_negate = take fe_normalize &&& drop fe_negate','ge_negate = take fe_negate &&& drop fe_normalize'),
 ('port','O (@canonical_fe_normalize term) &&& I (@literal_fe_negate term)','O (@literal_fe_negate term) &&& I (@canonical_fe_normalize term)'),
 ('port','O (@literal_ge_negate term) &&& I (@canonical_fe_normalize term)','O (@literal_ge_negate term) &&& I (@numeric_fe_normalize term)'),
 ('temps','create_undef_temps','create_defined_temps'),
 ('local','secp_jet_local_spec f_simplicity_gej_negate','False -> secp_jet_local_spec f_simplicity_gej_negate'),
 ('local','Word 8','Word 7'),
 ('local','@literal_gej_negate Alg.CoreFunSem','@numeric_gej_negate Alg.CoreFunSem'),
 ('c','secp256k1_gej_neg(&a, &a);','secp256k1_gej_neg(&a, &b);'),
 ('c','write_gej(dst, &a);',''),
 ('c','read_fe(&r->y, src);','read_fe(&r->x, src);'),
 ('c','write_fe(dst, &r->z);',''),
 ('group','r->z = a->z;','r->z = a->x;'),
 ('group','secp256k1_fe_normalize_weak(&r->y);',''),
 ('group','secp256k1_fe_negate(&r->y, &r->y, 1);','secp256k1_fe_negate(&r->y, &r->y, 2);')]
m=re.search(r'bool simplicity_gej_negate\([^)]*\)\s*\{[^{}]*\}',s['c'],re.S)
mutations.append(('c',m[0],m[0].replace('return true;','return false;')))
for app in ['bitcoin','elements']:
    m=re.search(r'\[GEJ_NEGATE\].*?\.cost',s[app],re.S)
    for old,new in [('.jet = simplicity_gej_negate','.jet = simplicity_gej_double'),
                    ('.sourceIx = ty_pw512w256','.sourceIx = ty_w256'),
                    ('.targetIx = ty_pw512w256','.targetIx = ty_w256')]:
        assert old in m[0]
        mutations.append((app,m[0],m[0].replace(old,new)))
for key,old,new in mutations:
    assert old in s[key] and old != new,(key,old)
    changed=dict(s);changed[key]=s[key].replace(old,new)
    try:gate.check(changed)
    except (ValueError,IndexError):pass
    else:raise AssertionError('mutation accepted: '+key+' '+old)
print(str(len(mutations))+' point-negate source/lifecycle mutations rejected')
