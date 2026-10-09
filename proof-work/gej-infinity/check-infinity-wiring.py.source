"""Scoped infinity source correspondence, supplementary to kernel/AST checks.

This is not a Haskell compiler, transitive fidelity certificate, or proof of
evaluator-domain admissibility. Pure checks, without snapshot update mode.
"""
import argparse
import importlib.util
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

def compact(s):
    return re.sub(r'\s+', '', s)

def load(repo, candidates):
    repo, candidates = Path(repo), Path(candidates)
    spec = importlib.util.spec_from_file_location('parser', repo/'Coq/check-secp-predicates-specification.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    paths = {'catalog': repo/'Haskell/Core/Simplicity/CoreJets.hs',
             'program': repo/'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs',
             'arith': repo/'Haskell/Core/Simplicity/Programs/Arith.hs',
             'word': repo/'Haskell/Core/Simplicity/Programs/Word.hs',
             'zero': repo/'Coq/Simplicity/Word.v'}
    for key, name in [('port','jet_secp_literal_infinity'),('entry','jet_secp_gej_public_entry'),
                      ('lifecycle','jet_secp_gej_public_lifecycle'),('call','jet_secp_gej_public_call'),
                      ('local','jet_secp_gej_infinity_local')]:
        paths[key] = candidates/(name+'.v')
    s = {k: parser.read_code(p) for k,p in paths.items()}
    s['c'] = re.sub(r'/\*.*?\*/|//[^\n]*', ' ', (repo/'C/jets-secp256k1.c').read_text(), flags=re.S)
    for app in ['bitcoin','elements']:
        s[app] = re.sub(r'/\*.*?\*/', ' ', (repo/f'C/{app}/primitiveJetNode.inc').read_text(), flags=re.S)
    return s

FRAGMENTS = {
 'catalog': ['GejInfinity :: Secp256k1Jet () Secp256k1.GEJ',
             'specificationSecp256k1 GejInfinity = Secp256k1.gej_infinity'],
 'program': ['zero256 = Arith.zero word256', ', fe_zero = zero256'],
 'arith': ['zero = low'],
 'word': ['fill t SingleV = t', 'fill t (DoubleV w) = rec &&& rec', 'rec = fill t w', 'low = fill false'],
 'entry': ['Mem.alloc m 0 16 = (ma, bl)', 'Mem.alloc ma 0 128 = (mb, ba)',
           'function_entry2 secp_ge f_simplicity_gej_infinity'],
 'lifecycle': ['[(bl,0,16);(ba,0,128)]', 'Mem.free_list m (blocks_of_env secp_ge (gej_public_env bl ba)) = Some mf'],
 'call': ['gej_prepare_public_locals', 'exec_gej_public_rest_owned', 'gej_free_public_locals mw bl ba',
          'eapply gej_infinity_public_entry', 'rewrite gej_public_body', '+ exact HFree.']}

def exact(actual, expected, label):
    if compact(actual) != compact(expected):
        raise ValueError('source correspondence differs: '+label)

def definition(s, name):
    m = re.search(r'\b(?:Definition|Fixpoint)\s+'+name+r'\b.*?:=(.*?)\.\s*(?:\n|$)', s, re.S)
    if not m: raise ValueError('missing definition '+name)
    return m[1]

def check(s):
    for key, fragments in FRAGMENTS.items():
        for fragment in fragments:
            if compact(fragment) not in compact(s[key]):
                raise ValueError('missing active binding '+key+': '+fragment)
    record = s['program'].split('lib@Lib{..} = Lib {',1)[1]
    m = re.search(r'\bgej_infinity\s*=(.*?)\n\s*,\s*gej_negate\b',record,re.S)
    if not m: raise ValueError('missing canonical infinity')
    exact(m[1], 'let zero = fe_zero in (zero &&& zero) &&& zero', 'canonical program')
    exact(definition(s['port'],'literal_fe_zero256'), '@Word.zero 8 term', 'zero port')
    exact(definition(s['port'],'literal_gej_infinity'),
          '(@literal_fe_zero256 term &&& @literal_fe_zero256 term) &&& @literal_fe_zero256 term', 'point port')
    exact(definition(s['zero'],'zero'), 'match n with | 0 => false | S n => zero &&& zero end', 'recursive zero')
    m = re.search(r'\bTheorem\s+gej_infinity_literal_local_spec\s*:(.*?)\bProof\.',s['local'],re.S)
    if not m: raise ValueError('missing public theorem')
    exact(m[1], 'secp_jet_local_spec f_simplicity_gej_infinity Ty.Unit (Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (@literal_gej_infinity Alg.CoreFunSem).', 'public statement')
    for name, expected in [
      ('simplicity_gej_infinity','(void) src; (void) env; secp256k1_gej a; secp256k1_gej_set_infinity(&a); write_gej(dst, &a); return true;'),
      ('write_gej','write_fe(dst, &r->x); write_fe(dst, &r->y); write_fe(dst, &r->z);')]:
        m = re.search(r'\b'+name+r'\([^)]*\)\s*\{([^{}]*)\}',s['c'],re.S)
        if not m: raise ValueError('missing original C '+name)
        exact(m[1],expected,'original C '+name)
    for app in ['bitcoin','elements']:
        m = re.search(r'\[GEJ_INFINITY\]\s*=\s*\{([^{}]*(?:\{\{[^{}]*\}\})?[^{}]*)\}', s[app], re.S)
        if not m: raise ValueError('missing registration '+app)
        for fragment in ['.jet = simplicity_gej_infinity', '.sourceIx = ty_u', '.targetIx = ty_pw512w256']:
            if compact(fragment) not in compact(m[1]): raise ValueError('registration differs '+app)

if __name__ == '__main__':
    p = argparse.ArgumentParser();p.add_argument('--repo',required=True);p.add_argument('--candidates',required=True)
    args=p.parse_args();check(load(args.repo,args.candidates));print('Scoped literal infinity and original public lifecycle correspondence passed')
