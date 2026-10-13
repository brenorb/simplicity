"""Supplemental affine correspondence gate; not a compiler/kernel substitute."""
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
        raise ValueError('source correspondence differs: ' + label)

def definition(s, name):
    m = re.search(r'\bDefinition\s+' + name + r'\b.*?:=(.*?)\.\s*(?:\n|$)', s, re.S)
    if not m:
        raise ValueError('missing definition ' + name)
    return m[1]

def load(repo, candidates, dependencies):
    repo, candidates, dependencies = map(Path, (repo, candidates, dependencies))
    spec = importlib.util.spec_from_file_location('parser', repo/'Coq/check-secp-predicates-specification.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    paths = {
        'catalog': repo/'Haskell/Core/Simplicity/CoreJets.hs',
        'program': repo/'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs',
        'temps': repo/'Coq/C/jet_secp_public_copy.v',
        'port': dependencies/'jet_secp_gej_negate_literal.v',
    }
    for key, name in [
        ('lifecycle', 'jet_secp_owned_public_lifecycle'),
        ('prepare', 'jet_secp_owned_public_prepare'),
        ('entry', 'jet_secp_ge_negate_boundary'),
        ('call', 'jet_secp_ge_negate_call'),
        ('rest', 'jet_secp_ge_negate_rest_owned'),
        ('local', 'jet_secp_ge_negate_local'),
        ('writer', 'jet_secp_write_ge_negated_literal'),
    ]:
        paths[key] = candidates/(name + '.v')
    s = {k: parser.read_code(p) for k, p in paths.items()}
    for key, path in [
        ('c', 'C/jets-secp256k1.c'), ('group', 'C/secp256k1/group_impl.h'),
        ('bitcoin', 'C/bitcoin/primitiveJetNode.inc'),
        ('elements', 'C/elements/primitiveJetNode.inc'),
    ]:
        s[key] = re.sub(r'/\*.*?\*/|//[^\n]*', ' ', (repo/path).read_text(), flags=re.S)
    return s

FRAGMENTS = {
    'catalog': ['GeNegate :: Secp256k1Jet Secp256k1.GE Secp256k1.GE',
                'specificationSecp256k1 GeNegate = Secp256k1.ge_negate',
                'implementationSecp256k1 GeNegate = FFI.ge_negate'],
    'entry': ['Mem.alloc m 0 16 = (ma,bl)', 'Mem.alloc ma 0 88 = (mb,ba)',
              'function_entry2 secp_ge f_simplicity_ge_negate'],
    'lifecycle': ['sizeof (genv_cenv secp_ge) ty = size ->',
                  '[(bl,0,16);(ba,0,size)]',
                  'Mem.free_list m (blocks_of_env secp_ge (owned_public_env ty bl ba)) = Some mf'],
    'prepare': ['owned_public_alloc_fresh size', 'owned_public_alloc_freeable size',
                'owned_public_alloc_source_fields size', 'apply exec_owned_public_copy',
                'apply finv_init'],
    'call': ['Mem.alloc ma 0 88',
             'owned_public_prepare_locals (Tstruct __6121 noattr) 88',
             'exec_ge_negate_rest_owned',
             'owned_public_free_locals (Tstruct __6121 noattr) 88',
             'eq_refl HSeparate HFinalFreeL HFinalFreeA',
             'eapply ge_negate_public_entry', 'rewrite ge_negate_public_body',
             '+ exact HFree.'],
    'rest': ['eval_read_ge_canonical_fields', 'eval_affine_negate_point_output',
             'eval_write_ge_negated_literal', 'point_lframe_preserves_inv',
             'point_lframe_preserves_source', 'exec_ge_negate_rest_from_calls'],
    'writer': ['eval_write_ge_general', 'point_canonical_field_bounded',
               'point_negative_field_bounded', 'literal_ge_negate_writer_encoding'],
}

def check(s):
    for key, fragments in FRAGMENTS.items():
        for fragment in fragments:
            if compact(fragment) not in compact(s[key]):
                raise ValueError('missing active binding ' + key + ': ' + fragment)
    record = s['program'].split('lib@Lib{..} = Lib {', 1)[1]
    m = re.search(r'\bge_negate\s*=(.*?)\n\s*,', record, re.S)
    if not m:
        raise ValueError('missing canonical ge_negate')
    exact(m[1], 'take fe_normalize &&& drop fe_negate', 'canonical ge_negate')
    exact(definition(s['port'], 'literal_ge_negate'),
          'O (@canonical_fe_normalize term) &&& I (@literal_fe_negate term)', 'literal GE port')
    exact(definition(s['temps'], 'secp_public_temps'),
          'PTree.set jets_secp._env v_env (PTree.set jets_secp._src (Vptr bs (Ptrofs.repr sbase)) '
          '(PTree.set jets_secp._dst (Vptr bd (Ptrofs.repr dbase)) '
          '(create_undef_temps (fn_temps f_simplicity_fe_normalize))))', 'actual initial temps')
    m = re.search(r'\bTheorem\s+ge_negate_literal_local_spec\s*:(.*?)\bProof\.', s['local'], re.S)
    if not m:
        raise ValueError('missing public theorem')
    exact(m[1], 'secp_jet_local_spec f_simplicity_ge_negate '
          '(Ty.Prod (Word 8) (Word 8)) (Ty.Prod (Word 8) (Word 8)) '
          '(@literal_ge_negate Alg.CoreFunSem).', 'public statement')
    for key, name, expected in [
        ('c', 'simplicity_ge_negate', '(void) env; secp256k1_ge a; read_ge(&a, &src); '
         'secp256k1_ge_neg(&a, &a); write_ge(dst, &a); return true;'),
        ('c', 'read_ge', 'read_fe(&r->x, src); read_fe(&r->y, src); r->infinity = 0;'),
        ('c', 'write_ge', 'write_fe(dst, &r->x); write_fe(dst, &r->y);'),
        ('group', 'secp256k1_ge_neg', '*r = *a; secp256k1_fe_normalize_weak(&r->y); '
         'secp256k1_fe_negate(&r->y, &r->y, 1);'),
    ]:
        m = re.search(r'\b' + name + r'\([^)]*\)\s*\{([^{}]*)\}', s[key], re.S)
        if not m:
            raise ValueError('missing C body ' + name)
        exact(m[1], expected, 'C ' + name)
    for app in ['bitcoin', 'elements']:
        m = re.search(r'\[GE_NEGATE\]\s*=\s*\{([^{}]*(?:\{\{[^{}]*\}\})?[^{}]*)\}', s[app], re.S)
        if not m:
            raise ValueError('missing registration ' + app)
        for fragment in ['.jet = simplicity_ge_negate', '.sourceIx = ty_w512', '.targetIx = ty_w512']:
            if compact(fragment) not in compact(m[1]):
                raise ValueError('registration differs ' + app)

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for n in ['repo', 'candidates', 'dependencies']:
        p.add_argument('--' + n, required=True)
    a = p.parse_args()
    check(load(a.repo, a.candidates, a.dependencies))
    print('Scoped affine-negate literal program and original lifecycle correspondence passed')
