"""Scoped canonical field multiply/square and original-C lifecycle source correspondence.

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
        'multiply': dependencies/'jet_multiply_spec.v',
        'normalize512': dependencies/'jet_secp_negate_literal_contract.v',
        'square': candidates/'jet_parallel_fe_sqr_field.v',
        'mul_local': candidates/'jet_parallel_fe_mul_local.v',
        'sqr_local': candidates/'jet_parallel_fe_sqr_local.v',
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


def c_body(source, name):
    m = re.search(r'bool\s+'+name+r'\s*\((.*?)\)\s*\{(.*?)\}', source, re.S)
    if not m:
        raise ValueError('missing C jet '+name)
    return m[1], m[2]


def check(s):
    for expected in [
        'FeMultiply :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE',
        'FeSquare :: Secp256k1Jet Secp256k1.FE Secp256k1.FE',
        'specificationSecp256k1 FeMultiply = Secp256k1.fe_multiply',
        'specificationSecp256k1 FeSquare = Secp256k1.fe_square']:
        require(s['catalog'], expected)
    implementation = s['program'].split('lib@Lib{..} = Lib {', 1)[1]
    records = {
        'fe_multiply': (r'\bfe_multiply\s*=(.*?)\n\s*,\s*fe_multiply_beta\b', 'mul256 >>> fe_normalize512'),
        'fe_square': (r'\bfe_square\s*=(.*?)\n\s*,\s*fe_halve\b', 'iden &&& iden >>> fe_multiply'),
    }
    for name, (pattern, expected) in records.items():
        m = re.search(pattern, implementation, re.S)
        if not m or compact(m[1]) != compact(expected):
            raise ValueError('canonical record differs: '+name)
    for expected in [
        'mul256 = Arith.multiply word256', 'zero256 = Arith.zero word256',
        'mod512 = Arith.modulo word512',
        'scribeFeOrder = scribe256 LibSecp256k1.fieldOrder',
        'fe_normalize512 = iden &&& (unit >>> zero256 &&& scribeFeOrder) >>> mod512 >>> ih']:
        require(s['program'], expected)
    require(s['arith'], 'multiply w = iden &&& (unit >>> zero (DoubleV w)) >>> full_multiply w')
    definitions = {
        ('multiply', 'multiply_word_spec'): '''Alg.Core.Combinators.comp
          (Alg.Core.Combinators.pair Alg.Core.Combinators.iden
            (Alg.Core.Combinators.comp Alg.Core.Combinators.unit (@zero (S n) term)))
          (@fullMultiplier n term)''',
        ('normalize512', 'literal_fe_normalize512'): 'iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word)) >>> @literal_modulo_word_spec 9 term >>> I H',
        ('normalize512', 'literal_fe_multiply'): '@multiply_word_spec 8 term >>> @literal_fe_normalize512 term',
        ('square', 'literal_fe_square'): 'iden &&& iden >>> @literal_fe_multiply term',
        ('mul_local', 'secp_public_mul_stmt'): '''Scall None
          (Evar jets_secp._secp256k1_fe_mul (Tfunction
            (Tcons (tptr secp_field_type) (Tcons (tptr secp_field_type)
              (Tcons (tptr secp_field_type) Tnil))) tvoid cc_default))
          [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
           Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
           Eaddrof (Evar jets_secp._b secp_field_type) (tptr secp_field_type)]''',
        ('mul_local', 'secp_fe_mul_rest'): '''Ssequence (secp_read_field_stmt jets_secp._a)
          (Ssequence (secp_read_field_stmt jets_secp._b)
            (Ssequence secp_public_mul_stmt (Ssequence secp_public_write_stmt
              (Sreturn (Some (Econst_int (Int.repr 1) tint))))))''',
        ('sqr_local', 'secp_public_sqr_stmt'): '''Scall None
          (Evar jets_secp._secp256k1_fe_sqr (Tfunction
            (Tcons (tptr secp_field_type) (Tcons (tptr secp_field_type) Tnil)) tvoid cc_default))
          [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
           Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type)]''',
        ('sqr_local', 'secp_fe_sqr_rest'): '''Ssequence secp_public_read_stmt
          (Ssequence secp_public_sqr_stmt (Ssequence secp_public_write_stmt
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))))''',
    }
    for (key, name), expected in definitions.items():
        if compact(body(s[key], name)) != compact(expected):
            raise ValueError('reviewed definition differs: '+name)
    require(s['multiply'], '@Alg.Core.domain term (Ty.Prod (Word n) (Word n)) (Word (S n))')
    require(s['normalize512'], 'term (Word 9) (Word 8)')
    require(s['normalize512'], 'term (Ty.Prod (Word 8) (Word 8)) (Word 8)')
    require(s['square'], 'Definition literal_fe_square {term : Alg.Core.Algebra} : term (Word 8) (Word 8)')
    contracts = {
        ('mul_local', 'fe_multiply_literal_local_spec'): '''secp_jet_local_spec f_simplicity_fe_multiply
          (Ty.Prod (Word 8) (Word 8)) (Word 8) (@literal_fe_multiply Alg.CoreFunSem).''',
        ('mul_local', 'fe_multiply_local_spec'): '''secp_jet_local_spec f_simplicity_fe_multiply
          (Ty.Prod (Word 8) (Word 8)) (Word 8) (@canonical_fe_multiply Alg.CoreFunSem).''',
        ('sqr_local', 'fe_square_literal_local_spec'): '''secp_jet_local_spec f_simplicity_fe_square
          (Word 8) (Word 8) (@literal_fe_square Alg.CoreFunSem).''',
        ('mul_local', 'secp_fe_mul_body'): '''fn_body f_simplicity_fe_multiply =
          Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
            (Etempvar jets_secp._src secp_frame_type)) secp_fe_mul_rest.''',
        ('sqr_local', 'secp_fe_sqr_body'): '''fn_body f_simplicity_fe_square =
          Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
            (Etempvar jets_secp._src secp_frame_type)) secp_fe_sqr_rest.''',
    }
    for (key, name), expected in contracts.items():
        if compact(statement(s[key], name)) != compact(expected):
            raise ValueError('reviewed proposition differs: '+name)
    for key, expected in [
            ('mul_local', 'eapply secp_fe_mul_entry'), ('mul_local', 'rewrite secp_fe_mul_body'),
            ('mul_local', 'secp_prepare_add_locals'), ('mul_local', 'secp_free_add_locals'),
            ('sqr_local', 'eapply secp_fe_square_entry'), ('sqr_local', 'rewrite secp_fe_sqr_body'),
            ('sqr_local', 'secp_prepare_public_locals'), ('sqr_local', 'secp_free_public_locals')]:
        require(s[key], expected)
    signature = 'frameItem* dst, frameItem src, const txEnv* env'
    implementations = {
        'simplicity_fe_multiply': '''(void) env; secp256k1_fe a, b;
          read_fe(&a, &src); read_fe(&b, &src); secp256k1_fe_mul(&a, &a, &b);
          write_fe(dst, &a); return true;''',
        'simplicity_fe_square': '''(void) env; secp256k1_fe a;
          read_fe(&a, &src); secp256k1_fe_sqr(&a, &a);
          write_fe(dst, &a); return true;''',
    }
    for name, expected in implementations.items():
        args, code = c_body(s['c'], name)
        if compact(args) != compact(signature) or compact(code) != compact(expected):
            raise ValueError('original public C jet differs: '+name)
    return len(definitions) + len(contracts)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--repo', required=True)
    p.add_argument('--candidates', required=True)
    p.add_argument('--dependencies', required=True)
    a = p.parse_args()
    print('Canonical field multiply/square and original public C lifecycle match:',
          check(load(a.repo, a.candidates, a.dependencies)), 'reviewed definitions/propositions')
