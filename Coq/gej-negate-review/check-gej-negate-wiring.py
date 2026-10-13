"""Supplemental scoped correspondence; not a compiler or kernel substitute.

Inherited field ports require their existing gates. No snapshot update mode.
"""
import argparse
import importlib.util
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

def compact(s):
    return re.sub(r'\s+', '', s)

def exact(a, b, label):
    if compact(a) != compact(b):
        raise ValueError('source correspondence differs: '+label)

def definition(s, name):
    m = re.search(r'\bDefinition\s+'+name+r'\b.*?:=(.*?)\.\s*(?:\n|$)', s, re.S)
    if not m:
        raise ValueError('missing definition '+name)
    return m[1]

def load(repo, candidates, dependencies):
    repo, candidates, dependencies = map(Path, (repo, candidates, dependencies))
    spec = importlib.util.spec_from_file_location('parser', repo/'Coq/check-secp-predicates-specification.py')
    parser = importlib.util.module_from_spec(spec); spec.loader.exec_module(parser)
    paths = {'catalog':repo/'Haskell/Core/Simplicity/CoreJets.hs',
             'program':repo/'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs',
             'temps':repo/'Coq/C/jet_secp_public_copy.v',
             'lifecycle':dependencies/'jet_secp_gej_public_lifecycle.v'}
    for key, name in [('port','jet_secp_gej_negate_literal'),
                      ('entry','jet_secp_gej_negate_boundary'),
                      ('call','jet_secp_gej_negate_call'),
                      ('rest','jet_secp_gej_negate_rest_owned'),
                      ('local','jet_secp_gej_negate_local')]:
        paths[key] = candidates/(name+'.v')
    s = {k:parser.read_code(p) for k,p in paths.items()}
    for key, path in [('c','C/jets-secp256k1.c'),('group','C/secp256k1/group_impl.h'),
                      ('bitcoin','C/bitcoin/primitiveJetNode.inc'),
                      ('elements','C/elements/primitiveJetNode.inc')]:
        s[key] = re.sub(r'/\*.*?\*/|//[^\n]*',' ',(repo/path).read_text(),flags=re.S)
    return s

FRAGMENTS = {
 'catalog':['GejNegate :: Secp256k1Jet Secp256k1.GEJ Secp256k1.GEJ',
            'specificationSecp256k1 GejNegate = Secp256k1.gej_negate',
            'implementationSecp256k1 GejNegate = FFI.gej_negate'],
 'entry':['Mem.alloc m 0 16 = (ma, bl)','Mem.alloc ma 0 128 = (mb, ba)',
          'function_entry2 secp_ge f_simplicity_gej_negate'],
 'lifecycle':['[(bl,0,16);(ba,0,128)]',
              'Mem.free_list m (blocks_of_env secp_ge (gej_public_env bl ba)) = Some mf'],
 'call':['gej_prepare_owned_locals','exec_gej_negate_rest_owned',
         'gej_free_public_locals mw bl ba','eapply gej_negate_public_entry',
         'rewrite gej_negate_public_body','+ exact HFree.'],
 'rest':['eval_read_gej_canonical_fields','eval_gej_negate_point_output',
         'eval_write_gej_negated_literal','point_lframe_preserves_inv',
         'exec_gej_negate_rest_from_calls']}

def check(s):
    for key, fragments in FRAGMENTS.items():
        for fragment in fragments:
            if compact(fragment) not in compact(s[key]):
                raise ValueError('missing active binding '+key+': '+fragment)
    record = s['program'].split('lib@Lib{..} = Lib {',1)[1]
    for name, expected in [('gej_negate','take ge_negate &&& drop fe_normalize'),
                           ('ge_negate','take fe_normalize &&& drop fe_negate')]:
        m = re.search(r'\b'+name+r'\s*=(.*?)\n\s*,',record,re.S)
        if not m: raise ValueError('missing canonical '+name)
        exact(m[1],expected,name)
    exact(definition(s['port'],'literal_ge_negate'),
          'O (@canonical_fe_normalize term) &&& I (@literal_fe_negate term)','literal GE port')
    exact(definition(s['port'],'literal_gej_negate'),
          'O (@literal_ge_negate term) &&& I (@canonical_fe_normalize term)','literal GEJ port')
    exact(definition(s['temps'],'secp_public_temps'),
          'PTree.set jets_secp._env v_env (PTree.set jets_secp._src (Vptr bs (Ptrofs.repr sbase)) '
          '(PTree.set jets_secp._dst (Vptr bd (Ptrofs.repr dbase)) '
          '(create_undef_temps (fn_temps f_simplicity_fe_normalize))))','actual initial temps')
    m = re.search(r'\bTheorem\s+gej_negate_literal_local_spec\s*:(.*?)\bProof\.',s['local'],re.S)
    if not m: raise ValueError('missing public theorem')
    exact(m[1],'secp_jet_local_spec f_simplicity_gej_negate '
          '(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) '
          '(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) '
          '(@literal_gej_negate Alg.CoreFunSem).','public statement')
    for key,name,expected in [
      ('c','simplicity_gej_negate','(void) env; secp256k1_gej a; read_gej(&a, &src); '
       'secp256k1_gej_neg(&a, &a); write_gej(dst, &a); return true;'),
      ('c','read_gej','read_fe(&r->x, src); read_fe(&r->y, src); read_fe(&r->z, src); '
       'r->infinity = secp256k1_fe_is_zero(&r->z);'),
      ('c','write_gej','write_fe(dst, &r->x); write_fe(dst, &r->y); write_fe(dst, &r->z);'),
      ('group','secp256k1_gej_neg','r->infinity = a->infinity; r->x = a->x; '
       'r->y = a->y; r->z = a->z; secp256k1_fe_normalize_weak(&r->y); '
       'secp256k1_fe_negate(&r->y, &r->y, 1);')]:
        m = re.search(r'\b'+name+r'\([^)]*\)\s*\{([^{}]*)\}',s[key],re.S)
        if not m: raise ValueError('missing C body '+name)
        exact(m[1],expected,'C '+name)
    for app in ['bitcoin','elements']:
        m = re.search(r'\[GEJ_NEGATE\]\s*=\s*\{([^{}]*(?:\{\{[^{}]*\}\})?[^{}]*)\}',s[app],re.S)
        if not m: raise ValueError('missing registration '+app)
        for fragment in ['.jet = simplicity_gej_negate','.sourceIx = ty_pw512w256','.targetIx = ty_pw512w256']:
            if compact(fragment) not in compact(m[1]):
                raise ValueError('registration differs '+app)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for n in ['repo','candidates','dependencies']: p.add_argument('--'+n,required=True)
    a=p.parse_args(); check(load(a.repo,a.candidates,a.dependencies))
    print('Scoped point-negate literal program and original lifecycle correspondence passed')
