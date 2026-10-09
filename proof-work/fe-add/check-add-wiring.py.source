"""Scoped canonical field-add and original-C lifecycle source correspondence.

Supplement to kernel checking, not a formal Haskell compiler or a complete
transitive/domain audit. Pure source checks; no update/generation mode.
"""
import argparse
import importlib.util
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True


def compact(s):
    return re.sub(r'\s+', '', s)


def load(repo, candidates, dependencies):
    repo, candidates, dependencies = map(Path, (repo, candidates, dependencies))
    spec = importlib.util.spec_from_file_location(
        'predicate_parser', repo/'Coq/check-secp-predicates-specification.py')
    parser = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parser)
    paths = {
        'catalog': repo/'Haskell/Core/Simplicity/CoreJets.hs',
        'program': repo/'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs',
        'arith': repo/'Haskell/Core/Simplicity/Programs/Arith.hs',
        'word': repo/'Haskell/Core/Simplicity/Programs/Word.hs',
        'padding': repo/'Coq/C/jet_spec.v',
        'port': candidates/'jet_secp_literal_add_program.v',
        'body': candidates/'jet_secp_add_body.v',
        'entry': candidates/'jet_secp_add_entry.v',
        'lifecycle': candidates/'jet_secp_add_lifecycle.v',
        'local': candidates/'jet_secp_add_local.v',
        'add': dependencies/'jet_canonical_add_adapter.v',
        'normalize512': dependencies/'jet_secp_negate_literal_contract.v',
    }
    s = {key: parser.read_code(path) for key, path in paths.items()}
    c = (repo/'C/jets-secp256k1.c').read_text()
    s['c'] = re.sub(r'/\*.*?\*/|//[^\n]*', ' ', c, flags=re.S)
    return s


def require(source, expected):
    if compact(expected) not in compact(source):
        raise ValueError('missing source binding: '+expected)


def body(source, name):
    m = re.search(r'\b(?:Definition|Fixpoint)\s+'+name+r'\b.*?:=(.*?)\.\s*(?:\n|$)', source, re.S)
    if not m:
        raise ValueError('missing definition '+name)
    return m[1]


def statement(source, name):
    m = re.search(r'\b(?:Theorem|Lemma)\s+'+name+r'\b[^:\n]*:(.*?)\bProof\.', source, re.S)
    if not m:
        raise ValueError('missing proposition '+name)
    return m[1]


def check(s):
    require(s['catalog'], 'FeAdd :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE')
    require(s['catalog'], 'specificationSecp256k1 FeAdd = Secp256k1.fe_add')
    implementation = s['program'].split('lib@Lib{..} = Lib {', 1)[1]
    m = re.search(r'\bfe_add\s*=(.*?)\n\s*,\s*fe_negate\b', implementation, re.S)
    expected = 'add256 >>> cond ((unit >>> one256) &&& iden) ((unit >>> zero256) &&& iden) >>> fe_normalize512'
    if not m or compact(m[1]) != compact(expected):
        raise ValueError('canonical field-add record differs')
    for expected in [
        'add256 = Arith.add word256', 'one256 = Arith.one word256',
        'zero256 = Arith.zero word256', 'mod512 = Arith.modulo word512',
        'scribeFeOrder = scribe256 LibSecp256k1.fieldOrder',
        'fe_normalize512 = iden &&& (unit >>> zero256 &&& scribeFeOrder) >>> mod512 >>> ih']:
        require(s['program'], expected)
    for expected in ['one w = true >>> left_pad_low word1 w',
                     'add w = false &&& iden >>> full_add w']:
        require(s['arith'], expected)
    for expected in ['left_pad_pad _ SingleV = iden',
                     'left_pad_pad t (DoubleV v) = fill t v &&& left_pad_pad t v',
                     'left_pad_low w v = left_pad_pad (unit >>> low w) v',
                     'low = fill false']:
        require(s['word'], expected)
    definitions = {
        ('padding', 'left_pad_low_1_n'): '''match n with
          | Datatypes.O => @Alg.Core.Combinators.iden Bit term
          | S n => @Alg.Core.Combinators.pair Bit (Word n) (Word n) term
            (fill (n := n) (@Alg.Core.Combinators.comp Bit Ty.Unit Bit term
              (@Alg.Core.Combinators.unit Bit term) (@Bit.false Ty.Unit term)))
            (left_pad_low_1_n n) end''',
        ('port', 'literal_fe_one256'): 'Bit.true >>> @left_pad_low_1_n term 8',
        ('port', 'literal_fe_add_expand'): 'Bit.cond ((unit >>> @literal_fe_one256 term) &&& iden) ((unit >>> @Word.zero 8 term) &&& iden)',
        ('port', 'literal_fe_add'): '@canonical_add_word 8 term >>> @literal_fe_add_expand term >>> @literal_fe_normalize512 term',
        ('add', 'canonical_add_word'): 'Bit.false &&& iden >>> @Word.fullAdder n term',
        ('normalize512', 'literal_fe_normalize512'): 'iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word)) >>> @literal_modulo_word_spec 9 term >>> I H',
        ('body', 'secp_public_add_env'): 'PTree.set jets_secp._b (bb, secp_field_type) (secp_public_env bl ba)',
        ('body', 'secp_fe_add_rest'): '''Ssequence (secp_read_field_stmt jets_secp._a)
          (Ssequence (secp_read_field_stmt jets_secp._b)
            (Ssequence secp_public_add_stmt (Ssequence secp_public_write_stmt
              (Sreturn (Some (Econst_int (Int.repr 1) tint))))))''',
        ('body', 'secp_read_field_stmt'): '''Scall None
          (Evar jets_secp._read_fe (Tfunction
            (Tcons (tptr secp_field_type) (Tcons (tptr secp_frame_type) Tnil)) tvoid cc_default))
          [Eaddrof (Evar id secp_field_type) (tptr secp_field_type);
           Eaddrof (Evar jets_secp._src secp_frame_type) (tptr secp_frame_type)]''',
        ('body', 'secp_public_add_stmt'): '''Scall None
          (Evar jets_secp._secp256k1_fe_add (Tfunction
            (Tcons (tptr secp_field_type) (Tcons (tptr secp_field_type) Tnil)) tvoid cc_default))
          [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
           Eaddrof (Evar jets_secp._b secp_field_type) (tptr secp_field_type)]''',
    }
    for (key, name), expected in definitions.items():
        if compact(body(s[key], name)) != compact(expected):
            raise ValueError('reviewed definition differs: '+name)
    for expected in [
        'term Ty.Unit (Word 8)',
        'term (Ty.Prod Bit (Word 8)) (Word 9)',
        'term (Ty.Prod (Word 8) (Word 8)) (Word 8)']:
        require(s['port'], expected)
    expected = '''secp_jet_local_spec f_simplicity_fe_add
      (Ty.Prod (Word 8) (Word 8)) (Word 8) (@literal_fe_add Alg.CoreFunSem).'''
    if compact(statement(s['local'], 'fe_add_literal_local_spec')) != compact(expected):
        raise ValueError('full public contract differs')
    expected = '''fn_body f_simplicity_fe_add =
      Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
        (Etempvar jets_secp._src secp_frame_type)) secp_fe_add_rest.'''
    if compact(statement(s['body'], 'secp_fe_add_body')) != compact(expected):
        raise ValueError('original public body equality differs')
    expected = '''blocks_of_env secp_ge (secp_public_add_env bl ba bb) =
      [(bl,0,16);(ba,0,40);(bb,0,40)].'''
    if compact(statement(s['entry'], 'secp_add_public_blocks')) != compact(expected):
        raise ValueError('original local cleanup shape differs')
    for expected in ['eapply secp_fe_add_entry', 'rewrite secp_fe_add_body',
                     'exec_secp_fe_add_rest_literal', 'secp_prepare_add_locals',
                     'secp_free_add_locals', 'eval_funcall_internal']:
        require(s['lifecycle'], expected)
    m = re.search(r'bool\s+simplicity_fe_add\s*\((.*?)\)\s*\{(.*?)\}', s['c'], re.S)
    signature = 'frameItem* dst, frameItem src, const txEnv* env'
    implementation = '''(void) env; secp256k1_fe a, b;
      read_fe(&a, &src); read_fe(&b, &src); secp256k1_fe_add(&a, &b);
      write_fe(dst, &a); return true;'''
    if not m or compact(m[1]) != compact(signature) or compact(m[2]) != compact(implementation):
        raise ValueError('original public C field-add differs')
    return len(definitions)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--repo', required=True)
    p.add_argument('--candidates', required=True)
    p.add_argument('--dependencies', required=True)
    a = p.parse_args()
    print('Canonical field-add and original public C lifecycle match:',
          check(load(a.repo, a.candidates, a.dependencies)), 'definitions')
