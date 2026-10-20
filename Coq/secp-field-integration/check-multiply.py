"""Scoped FeMultiply catalog/term/final-contract correspondence and mutations.

This is source-review evidence, not a substitute for the formal C proof or
the separate recursive/literal/foundation/normalization gates.
"""
import importlib.util
import os
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
COQ = HERE.parent
REPO = Path(os.environ.get("JET_C_REPO", COQ.parent))
sp = importlib.util.spec_from_file_location('multiply_literal_parser', COQ / 'check-secp-predicates-specification.py')
p = importlib.util.module_from_spec(sp)
sp.loader.exec_module(p)
sp = importlib.util.spec_from_file_location('multiply_literal_scanner', COQ / 'scan-jet-proofs.py')
scanner = importlib.util.module_from_spec(sp)
sp.loader.exec_module(scanner)


def sources():
    return {
        'catalog': p.read_code(REPO / 'Haskell/Core/Simplicity/CoreJets.hs'),
        'program': p.read_code(REPO / 'Haskell/Core/Simplicity/Programs/LibSecp256k1.hs'),
        'port': p.read_code(COQ / 'C/jet_secp_negate_literal_contract.v'),
        'jet': scanner.code_only((COQ / 'C/jet_secp_multiply_literal_jet.v').read_text()),
    }


def compact(text):
    return re.sub(r'\s+', '', text)


def require(source, fragment):
    if compact(fragment) not in compact(source):
        raise ValueError('missing active FeMultiply binding: ' + fragment)


def body(source, name):
    matches = re.findall(r'\bDefinition\s+' + name + r'\b.*?:=(.*?)\.\s*(?:\n|$)', source, re.S)
    if len(matches) != 1:
        raise ValueError('missing/duplicate literal definition: ' + name)
    return matches[0]


def check(s):
    require(s['catalog'], 'FeMultiply :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE')
    require(s['catalog'], 'specificationSecp256k1 FeMultiply = Secp256k1.fe_multiply')
    implementation = s['program'].split('lib@Lib{..} = Lib {', 1)
    hs = re.search(r'\bfe_multiply\s*=(.*?)\n\s*,\s*fe_multiply_beta\b',
                   implementation[1], re.S) if len(implementation) == 2 else None
    if not hs or compact(hs[1]) != compact('mul256 >>> fe_normalize512'):
        raise ValueError('original FeMultiply implementation record differs')
    for fragment in ['mul256 = Arith.multiply word256', 'mod512 = Arith.modulo word512',
        'fe_normalize512 = iden &&& (unit >>> zero256 &&& scribeFeOrder) >>> mod512 >>> ih']:
        require(s['program'], fragment)
    expected = {
        'literal_fe_normalize512': 'iden &&& (unit >>> (@Word.zero 8 term &&& Alg.scribe canonical_field_word)) >>> @literal_modulo_word_spec 9 term >>> I H',
        'literal_fe_multiply': '@multiply_word_spec 8 term >>> @literal_fe_normalize512 term',
    }
    for name, wanted in expected.items():
        if compact(body(s['port'], name)) != compact(wanted):
            raise ValueError('existing literal multiply term differs: ' + name)
    statements = re.findall(r'(?m)^Theorem fe_multiply_literal_local_spec\s*:(.*?)\bProof\.', s['jet'], re.S)
    wanted = '''secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word 8)) (Word 8)
      (@literal_fe_multiply Alg.CoreFunSem).'''
    if len(statements) != 1 or compact(statements[0]) != compact(wanted):
        raise ValueError('complete public C-to-literal statement differs')


def test():
    s = sources()
    check(s)
    mutations = [
        ('catalog', 'FeMultiply :: Secp256k1Jet (Secp256k1.FE, Secp256k1.FE) Secp256k1.FE',
         'FeMultiply :: Secp256k1Jet Secp256k1.FE Secp256k1.FE'),
        ('catalog', 'specificationSecp256k1 FeMultiply = Secp256k1.fe_multiply',
         'specificationSecp256k1 FeMultiply = Secp256k1.fe_square'),
        ('program', 'fe_multiply = mul256 >>> fe_normalize512', 'fe_multiply = mul256 >>> fe_normalize'),
        ('port', '@literal_modulo_word_spec 9 term', '@literal_modulo_word_spec 8 term'),
        ('port', '>>> I H.', '>>> O H.'),
        ('port', '@multiply_word_spec 8 term', '@multiply_word_spec 7 term'),
        ('jet', 'secp_jet_local_spec f_simplicity_fe_multiply', 'False -> secp_jet_local_spec f_simplicity_fe_multiply'),
        ('jet', 'secp_jet_local_spec f_simplicity_fe_multiply', 'secp_jet_local_spec f_simplicity_fe_square'),
        ('jet', '(Ty.Prod (Word 8) (Word 8)) (Word 8)', '(Ty.Sum (Word 8) (Word 8)) (Word 8)'),
        ('jet', '(@literal_fe_multiply Alg.CoreFunSem).', '(fun a => a).'),
    ]
    for key, old, new in mutations:
        if old not in s[key]:
            raise ValueError('inactive mutation fixture: ' + old)
        changed = dict(s)
        changed[key] = changed[key].replace(old, new)
        try:
            check(changed)
        except ValueError:
            pass
        else:
            raise ValueError('accepted FeMultiply mutation: ' + old)
    print('FeMultiply catalog/literal program/full public contract match; 10 targeted mutations rejected')


if __name__ == '__main__':
    test()
