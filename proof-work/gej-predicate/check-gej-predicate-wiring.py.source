"""Scoped point-predicate correspondence; supplemental to kernel and AST audits.

Not a Haskell compiler, transitive fidelity certificate, or evaluator-domain
proof. No snapshot update mode. Inherited field-zero ports need their own gate.
"""
import argparse
import importlib.util
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

def compact(s):
    return re.sub(r'\s+', '', s)

def load(repo, candidates, dependencies):
    repo, candidates, dependencies = map(Path, (repo, candidates, dependencies))
    spec = importlib.util.spec_from_file_location('parser', repo/'Coq/check-secp-predicates-specification.py')
    parser = importlib.util.module_from_spec(spec); spec.loader.exec_module(parser)
    paths = {'catalog': repo/'Haskell/Core/Simplicity/CoreJets.hs',
             'program': repo/'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'}
    for key, name in [('port','jet_secp_literal_gej_predicate'),
                      ('entry','jet_secp_gej_predicate_entry'),
                      ('call','jet_secp_gej_predicate_call'),
                      ('local','jet_secp_gej_predicate_local')]:
        paths[key] = candidates/(name+'.v')
    paths['lifecycle'] = dependencies/'jet_secp_gej_public_lifecycle.v'
    s = {k: parser.read_code(p) for k,p in paths.items()}
    for key, path in [('c','C/jets-secp256k1.c'), ('group','C/secp256k1/group_impl.h'),
                      ('bitcoin','C/bitcoin/primitiveJetNode.inc'),
                      ('elements','C/elements/primitiveJetNode.inc')]:
        s[key] = re.sub(r'/\*.*?\*/|//[^\n]*', ' ', (repo/path).read_text(), flags=re.S)
    return s

FRAGMENTS = {
 'catalog': ['GejIsInfinity :: Secp256k1Jet Secp256k1.GEJ Bit',
             'specificationSecp256k1 GejIsInfinity = Secp256k1.gej_is_infinity',
             'implementationSecp256k1 GejIsInfinity = FFI.gej_is_infinity'],
 'entry': ['Mem.alloc m 0 16 = (ma,bl)', 'Mem.alloc ma 0 128 = (mb,ba)',
           'function_entry2 secp_ge f_simplicity_gej_is_infinity'],
 'lifecycle': ['[(bl,0,16);(ba,0,128)]',
               'Mem.free_list m (blocks_of_env secp_ge (gej_public_env bl ba)) = Some mf'],
 'call': ['gej_prepare_owned_locals', 'exec_gej_predicate_rest_owned',
          'gej_free_public_locals mw bl ba', 'eapply gej_predicate_public_entry',
          'rewrite gej_predicate_body', '+ exact HFree.']}

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
    m = re.search(r'\bgej_is_infinity\s*=(.*?)\n\s*,\s*gej_double\b', record, re.S)
    if not m: raise ValueError('missing canonical predicate')
    exact(m[1], 'drop fe_is_zero', 'canonical program')
    exact(definition(s['port'],'literal_gej_is_infinity'),
          'Alg.Core.Combinators.drop (@canonical_fe_is_zero term)', 'literal port')
    exact(definition(s['entry'],'gej_predicate_temps'),
          'PTree.set _env v_env (PTree.set _src (Vptr bs (Ptrofs.repr sbase)) '
          '(PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) '
          '(create_undef_temps (fn_temps f_simplicity_gej_is_infinity))))', 'actual initial temps')
    m = re.search(r'\bTheorem\s+gej_is_infinity_literal_local_spec\s*:(.*?)\bProof\.', s['local'], re.S)
    if not m: raise ValueError('missing public theorem')
    exact(m[1], 'secp_jet_local_spec f_simplicity_gej_is_infinity '
          '(Ty.Prod (Ty.Prod (Word 8) (Word 8)) (Word 8)) (Ty.Sum Ty.Unit Ty.Unit) '
          '(@literal_gej_is_infinity Alg.CoreFunSem).', 'public statement')
    for key, name, expected in [
      ('c','simplicity_gej_is_infinity',
       '(void) env; secp256k1_gej a; read_gej(&a, &src); '
       'writeBit(dst, secp256k1_gej_is_infinity(&a)); return true;'),
      ('c','read_gej','read_fe(&r->x, src); read_fe(&r->y, src); '
       'read_fe(&r->z, src); r->infinity = secp256k1_fe_is_zero(&r->z);'),
      ('group','secp256k1_gej_is_infinity','return a->infinity;')]:
        m = re.search(r'\b'+name+r'\([^)]*\)\s*\{([^{}]*)\}', s[key], re.S)
        if not m: raise ValueError('missing original C '+name)
        exact(m[1], expected, 'original C '+name)
    for app in ['bitcoin','elements']:
        m = re.search(r'\[GEJ_IS_INFINITY\]\s*=\s*\{([^{}]*(?:\{\{[^{}]*\}\})?[^{}]*)\}', s[app], re.S)
        if not m: raise ValueError('missing registration '+app)
        for fragment in ['.jet = simplicity_gej_is_infinity', '.sourceIx = ty_pw512w256', '.targetIx = ty_b']:
            if compact(fragment) not in compact(m[1]):
                raise ValueError('registration differs '+app)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--repo', required=True); p.add_argument('--candidates', required=True)
    p.add_argument('--dependencies', required=True)
    a = p.parse_args(); check(load(a.repo,a.candidates,a.dependencies))
    print('Scoped literal point-predicate and original public lifecycle correspondence passed')
