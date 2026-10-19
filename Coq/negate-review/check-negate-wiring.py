"""Scoped literal negation wiring gate, not execution or transitive fidelity proof.

Checks active source, exact port bodies and the complete final public statement.
Recursive multiplier/division dependencies still require separate review.
"""
import argparse
import importlib.util
import re
import sys
from pathlib import Path

sys.dont_write_bytecode = True


def load_sources(repo, candidates):
    repo, candidates = Path(repo), Path(candidates)
    parser_spec = importlib.util.spec_from_file_location(
        'predicate_parser', repo/'Coq/check-secp-predicates-specification.py')
    parser = importlib.util.module_from_spec(parser_spec)
    parser_spec.loader.exec_module(parser)
    sources = {}
    for key, path in [
        ('catalog', repo/'Haskell/Core/Simplicity/CoreJets.hs'),
        ('program', repo/'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'),
        ('arith', repo/'Haskell/Core/Simplicity/Programs/Arith.hs'),
        ('multiply', repo/'Coq/C/jet_multiply_spec.v'),
        ('division', repo/'Coq/C/jet_division_core_spec.v'),
        ('port', candidates/'jet_secp_canonical_negate.v'),
        ('local', candidates/'jet_secp_negate_local.v')]:
        sources[key] = parser.read_code(path)
    return sources


def compact(text):
    return re.sub(r'\s+', '', text)


def body(text, name):
    match = re.search(r'\bDefinition\s+'+name+r'\b.*?:=(.*?)\.\s*(?:\n|$)', text, re.S)
    if not match:
        raise ValueError('missing definition '+name)
    return match[1]


def require(text, wanted):
    if compact(wanted) not in compact(text):
        raise ValueError('missing literal binding '+wanted)


def check(sources):
    s = sources
    require(s['catalog'], 'FeNegate :: Secp256k1Jet Secp256k1.FE Secp256k1.FE')
    require(s['catalog'], 'specificationSecp256k1 FeNegate = Secp256k1.fe_negate')
    implementation = s['program'].split('lib@Lib{..} = Lib {', 1)[1]
    for name, following, wanted in [
        ('fe_negate', 'fe_multiply', 'fe_multiplyInt (-1)'),
        ('fe_multiply', 'fe_multiply_beta', 'mul256 >>> fe_normalize512')]:
        match = re.search(r'\b'+name+r'\s*=(.*?)\n\s*,\s*'+following+r'\b', implementation, re.S)
        if not match or compact(match[1]) != compact(wanted):
            raise ValueError('canonical record differs '+name)
    for wanted in [
        'scribe256 = scribe . toWord256',
        'scribeFeOrder = scribe256 LibSecp256k1.fieldOrder',
        'mul256 = Arith.multiply word256', 'zero256 = Arith.zero word256',
        'mod512 = Arith.modulo word512',
        'fe_normalize512 = iden &&& (unit >>> zero256 &&& scribeFeOrder) >>> mod512 >>> ih',
        'fe_multiplyInt i = scribe256 (i `mod` LibSecp256k1.fieldOrder) &&& iden >>> fe_multiply']:
        require(s['program'], wanted)
    require(s['arith'], 'multiply w = iden &&& (unit >>> zero (DoubleV w)) >>> full_multiply w')
    require(s['arith'], 'modulo w = div_mod w >>> ih')
    expected = {
        'canonical_fe_normalize512': 'iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word)) >>> @modulo_word_spec 9 term >>> I H',
        'canonical_fe_multiply': '@multiply_word_spec 8 term >>> @canonical_fe_normalize512 term',
        'canonical_negate_factor': '@fromZ (WordToZ 8) ((-1) mod canonical_field_order)',
        'canonical_fe_negate': 'Alg.scribe canonical_negate_factor &&& iden >>> @canonical_fe_multiply term',
    }
    for name, wanted in expected.items():
        if compact(body(s['port'], name)) != compact(wanted):
            raise ValueError('literal Coq port differs '+name)
    require(s['port'], 'term (Word 9) (Word 8)')
    require(s['port'], 'term (Ty.Prod (Word 8) (Word 8)) (Word 8)')
    require(s['port'], 'term (Word 8) (Word 8)')
    wanted_mul = '''Alg.Core.Combinators.comp
      (Alg.Core.Combinators.pair Alg.Core.Combinators.iden
        (Alg.Core.Combinators.comp Alg.Core.Combinators.unit (@zero (S n) term)))
      (@fullMultiplier n term)'''
    if compact(body(s['multiply'], 'multiply_word_spec')) != compact(wanted_mul):
        raise ValueError('multiply wrapper differs')
    if compact(body(s['division'], 'modulo_word_spec')) != compact('@div_mod_word_spec n term >>> I H'):
        raise ValueError('modulo wrapper differs')
    statement = re.search(r'Theorem fe_negate_local_spec\s*:(.*?)\bProof\.', s['local'], re.S)
    wanted = 'secp_jet_local_spec f_simplicity_fe_negate (Word 8) (Word 8) (@canonical_fe_negate Alg.CoreFunSem).'
    if not statement or compact(statement[1]) != compact(wanted):
        raise ValueError('full public negation statement differs')
    return True


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--repo', required=True)
    p.add_argument('--candidates', required=True)
    args = p.parse_args()
    check(load_sources(args.repo, args.candidates))
    print('Literal negate wiring and final statement match; transitive review pending')
