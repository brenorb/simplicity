"""Selected output proof-byte views, canonical primitives and complete C contracts.

This guard is not a kernel checker or a formal proof about the host lens or
cryptography libraries; the formal endpoints use the project's Coq primitives.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def check(repo, coq, literal):
    inherited = load('output_proof_indexed_source', HERE.parent / 'elements-outpoint-output/check-source.py')
    record = inherited.check(repo, coq, coq / 'C/jet_elements_indexed_literal.v')
    parser = load('output_proof_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('output-proof source differs: ' + label)

    def definition(path, name, expected):
        matches = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                             r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous output-proof definition: ' + name)
        equal(matches[0], expected, name)

    def line(text, start, expected):
        matches = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', text)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous output-proof clause: ' + start)
        equal(matches[0], expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for fragment in ['data Confidential prf a = Explicit a | Confidential Point prf',
                     'prf_ :: Traversal (Confidential prfA a) (Confidential prfB a) prfA prfB',
                     'type SurjectionProof = BSL.ByteString', 'type RangeProof = BSL.ByteString',
                     'newtype AssetWith prf = Asset (Confidential prf Hash256)',
                     'newtype AmountWith prf = Amount (Confidential prf Value)',
                     'type AssetWithWitness = AssetWith SurjectionProof',
                     'type AmountWithWitness = AmountWith RangeProof',
                     'txoAsset :: AssetWithWitness', 'txoAmount :: AmountWithWitness']:
        parser.require(data, fragment, 'proof-view carrier')
    parser.require(hs, 'import Lens.Family2 (to, view, under)', 'host lens interpretation boundary')
    line(data, 'prf_ f (Confidential pt prf)', 'Confidential pt <$> f prf')
    line(data, 'prf_ f (Explicit x)', 'pure (Explicit x)')
    for adapter, constructor in [('asset', 'Asset'), ('amount', 'Amount')]:
        end = 'clear' + constructor + 'Prf ::'
        start = '\n' + adapter + ' ='
        if data.count(start) != 1 or data.count(end) != 1:
            raise ValueError('missing/ambiguous proof-view adapter')
        equal(data.split(start, 1)[1].split(end, 1)[0], 'adapter to fro where to (' + constructor + ' x) = x fro x = (' + constructor + ' x)', adapter)
    port = coq / 'C/jet_elements_prim.v'
    definition(port, 'assetWith', 'confidential prf hash256')
    definition(port, 'amountWith', 'confidential prf int64')
    definition(port, 'viewPrf', 'match c with | Explicit _ => [] | Confidential _ p => p end')
    definition(literal, 'haskell_confidential_proof_view', 'match c with Explicit _ => [] | Confidential _ proof => proof end')
    definition(literal, 'elements_output_proof_digest_literal_spec', '''
      elements_indexed_literal_result (fun e => sigTxOut (Elements.envTx e))
        (fun txo => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (byteStringHash (proof_of txo)))))''')
    source = read(port)
    sem = parser.definition(source, 'sem')
    indexed = coq / 'C/jet_elements_output_proof_jets.v'
    for name, tag, following, field, adapter, offset in [
        ('surjection', 'OutputSurjectionProof', 'OutputRangeProof', 'txoAsset', 'asset', 36),
        ('range', 'OutputRangeProof', 'GenesisBlockHash', 'txoAmount', 'amount', 68),
    ]:
        suffix, camel = 'output_' + name + '_proof', 'output' + name.capitalize() + 'Proof'
        parser.require(catalog, tag + ' :: TransactionJet Word32 (S Word256)', 'selected jet type')
        line(catalog, 'specificationTransaction ' + tag, 'primitive Prim.' + tag)
        parser.require(hs, tag + ' :: Prim Word32 (S Word256)', 'primitive type')
        line(hs, 'primName ' + tag, '"' + camel + '"')
        line(hs, 'interpret ' + tag, 'return . (atOutput $ encodeHash . bslHash . view (to ' + field + '.under ' + adapter + '.prf_))')
        parser.require(source, '| ' + tag + ' : prim Word32 (S Word256)', 'Coq primitive type')
        parser.require(source, '| ' + tag + ' => "' + camel + '"', 'Coq primitive identity')
        if sem.count('| ' + tag + ' =>') != 1 or sem.count('| ' + following + ' =>') != 1:
            raise ValueError('ambiguous output-proof primitive clause')
        equal(sem.split('| ' + tag + ' =>', 1)[1].split('| ' + following + ' =>', 1)[0],
              'atOutput (fun txo => encodeHash (byteStringHash (viewPrf (' + field + ' txo))))', tag)
        definition(indexed, 'elements_' + suffix + '_spec', 'Primitive.Combinators.prim Elements.' + tag)
        definition(indexed, name + '_proof_hash_words', 'hash256_reg (byteStringHash (viewPrf (' + field + ' txo)))')
        definition(indexed, 'elements_' + suffix + '_result', '''
          match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
          | Some txo => inr (from_hash256 (byteStringHash (viewPrf (''' + field + ''' txo)))) | None => inl tt end''')
        definition(literal, 'elements_' + suffix + '_literal_spec',
                   'elements_output_proof_digest_literal_spec (fun txo => haskell_confidential_proof_view (' + field + ' txo))')
        for is_literal, path in [(False, indexed), (True, literal)]:
            theorem = 'elements_' + suffix + ('_literal' if is_literal else '') + '_local_spec'
            target = ('elements_' + suffix + '_literal_spec' if is_literal else
                      '(fun a environment => @elements_' + suffix + '_spec (PrimitivePrimSem option_Monad_Zero) a environment)')
            found = re.findall(r'\bTheorem\s+' + theorem + r'\s*:(.*?)\bProof\.', read(path), re.S)
            if len(found) != 1:
                raise ValueError('missing/ambiguous full output-proof C contract')
            equal(found[0], 'application_jet_local_spec_sep f_simplicity_' + suffix + ' elements_ge Elements.env Word32 ' +
                  '(Ty.Sum Ty.Unit Word256) (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e)) ' +
                  '(fun m b ofs txo => uint32_array_at m b ofs (' + name + '_proof_hash_words txo)) 248 ' + str(offset) + ' 8 704) ' + target + '.', theorem)
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=['Elements.OutputSurjectionProof', 'Elements.OutputRangeProof'],
                  proof_view_cases_reviewed=True, whole_contracts_reviewed=True,
                  formal_host_lens_equivalence=False, formal_host_crypto_equivalence=False,
                  caller_cache_construction_proved=False, normal_registration=False, kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for n in ['repo', 'coq', 'literal']:
        p.add_argument('--' + n, type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(check(a.repo, a.coq, a.literal), indent=2))
