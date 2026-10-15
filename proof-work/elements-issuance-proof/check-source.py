"""Selected issuance-proof ports, proof-view cases and complete C contracts.

This is a source-correspondence guard, not kernel checking or verification of
the host lens/cryptography libraries. Their interpretation boundary is kept
explicit; the actual formal theorems target the project's Coq primitives.
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
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(repo, coq, literal):
    shared = load('issuance_source_shared', HERE.parent / 'elements-script-hash/check-source.py')
    record = shared.check(repo, coq, coq / 'C/jet_elements_script_hash_literal.v')
    parser = load('issuance_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []
    def read(path):
        paths.append(path)
        return parser.read_code(path)
    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('issuance-proof source differs: ' + label)
    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous issuance-proof definition: ' + name)
        equal(found[0], expected, name)
    def line(source, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous issuance-proof clause: ' + start)
        equal(found[0], expected, start)
    def between(source, start, end, expected):
        if source.count(start) != 1 or source.count(end) != 1:
            raise ValueError('ambiguous issuance-proof region: ' + start)
        equal(source.split(start, 1)[1].split(end, 1)[0], expected, start)
    def theorem(path, name, expected):
        found = re.findall(r'\bTheorem\s+' + re.escape(name) + r'\s*:(.*?)\bProof\.', read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous issuance-proof whole-C contract')
        equal(found[0], expected, name)
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    primitive = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for fragment in ['type RangeProof = BSL.ByteString', 'type AmountWithWitness = AmountWith RangeProof',
                     'type Issuance = Either NewIssuance Reissuance', 'sigTxiIssuance :: Maybe Issuance',
                     'newtype AmountWith prf = Amount (Confidential prf Value)', 'import Lens.Family2.Stock (some_)']:
        parser.require(primitive if fragment.startswith('import ') else data, fragment, 'issuance/proof carrier')
    parser.require(primitive, 'import Lens.Family2 (to, view, under)', 'lens interpretation boundary')
    line(primitive, 'just_ f', 'some_ f')
    line(primitive, 'issuanceAmount', 'either newIssuanceAmount reissuanceAmount')
    line(primitive, 'issuanceTokenAmount', 'either newIssuanceTokenAmount (const (Amount (Explicit 0)))')
    line(data, 'prf_ f (Confidential pt prf)', 'Confidential pt <$> f prf')
    line(data, 'prf_ f (Explicit x)', 'pure (Explicit x)')
    between(data, '\namount =', 'clearAmountPrf ::', 'adapter to fro where to (Amount x) = x fro x = (Amount x)')
    port = coq / 'C/jet_elements_prim.v'
    definition(port, 'viewPrf', 'match c with | Explicit _ => [] | Confidential _ p => p end')
    definition(port, 'amountWith', 'confidential prf int64')
    definition(port, 'issuance', 'newIssuance + reissuance')
    definition(port, 'issuanceAmount', 'match i with | inl new => newIssuanceAmount new | inr re => reissuanceAmount re end')
    definition(port, 'issuanceTokenAmount', 'match i with | inl new => newIssuanceTokenAmount new | inr _ => Explicit Int64.zero end')
    definition(port, 'issuanceProof', 'match sigTxiIssuance txi with | Some i => viewPrf (f i) | None => [] end')
    definition(literal, 'haskell_amount_proof_view', 'match a with Explicit _ => [] | Confidential _ proof => proof end')
    definition(literal, 'haskell_issuance_proof_view', '''match sigTxiIssuance txi with
      | None => []
      | Some (inl new) => haskell_amount_proof_view (if token then newIssuanceTokenAmount new else newIssuanceAmount new)
      | Some (inr re) => if token then [] else haskell_amount_proof_view (reissuanceAmount re) end''')
    indexed, current = coq / 'C/jet_elements_input_hash_jets.v', coq / 'C/jet_elements_current_input_jets.v'
    for part, tag, amount, offset, next_tag, token in [
        ('asset', 'IssuanceAssetProof', 'issuanceAmount', 360, 'IssuanceTokenProof', 'false'),
        ('token', 'IssuanceTokenProof', 'issuanceTokenAmount', 392, 'CurrentIndex', 'true'),
    ]:
        suffix = 'issuance_' + part + '_proof'
        for prefix, domain, output, target in [('', 'Word32', '(S Word256)', 'primitive Prim.' + tag),
                                              ('Current', '()', 'Word256', 'Prog.current' + tag)]:
            parser.require(catalog, prefix + tag + ' :: TransactionJet ' + domain + ' ' + output, 'selected jet type')
            line(catalog, 'specificationTransaction ' + prefix + tag, target)
        line(primitive, 'primName ' + tag, '"issuance' + part.capitalize() + 'Proof"')
        line(primitive, 'interpret ' + tag, 'return . (atInput $ encodeHash . bslHash . view (to sigTxiIssuance.just_.to ' + amount + '.under amount.prf_))')
        source = read(port)
        parser.require(source, '| ' + tag + ' : prim Word32 (S Word256)', 'primitive type')
        parser.require(source, '| ' + tag + ' => "issuance' + part.capitalize() + 'Proof"', 'primitive identity')
        between(parser.definition(source, 'sem'), '| ' + tag + ' =>', '| ' + next_tag + ' =>',
                'atInput (fun txi => encodeHash (byteStringHash (issuanceProof ' + amount + ' txi)))')
        line(library, 'current' + tag, 'Transaction.current' + tag + ' Transaction.lib')
        if program.count('lib = l') != 1:
            raise ValueError('ambiguous transaction library')
        found = re.findall(r'(?m)^\s*, current' + tag + r'\s*=([^\n]*)$', program.split('lib = l', 1)[1])
        if len(found) != 1:
            raise ValueError('missing/ambiguous current issuance-proof binding')
        equal(found[0], 'primitive CurrentIndex >>> assert (primitive ' + tag + ')', 'current assertion program')
        payload = ('match i with inl new => newIssuanceAmount new | inr re => reissuanceAmount re end' if part == 'asset'
                   else 'match i with | inl new => newIssuanceTokenAmount new | inr _ => Explicit Int64.zero end')
        definition(indexed, suffix + '_bytes', 'match sigTxiIssuance txi with | Some i => viewPrf (' + payload + ') | None => nil end')
        definition(indexed, suffix + '_words', 'hash256_reg (byteStringHash (' + suffix + '_bytes txo))')
        definition(indexed, 'elements_' + suffix + '_spec', 'Primitive.Combinators.prim Elements.' + tag)
        definition(current, 'elements_current_' + suffix + '_spec', 'elements_current_spec (@elements_' + suffix + '_spec alg)')
        definition(literal, 'elements_' + suffix + '_literal_spec', 'elements_input_digest_literal_spec (fun txi => byteStringHash (haskell_issuance_proof_view ' + token + ' txi))')
        definition(literal, 'elements_current_' + suffix + '_literal_spec', 'elements_current_literal_result elements_' + suffix + '_literal_spec')
        view_lemma = 'elements_' + suffix + '_view_matches'
        found = re.findall(r'\bLemma\s+' + view_lemma + r'\s+txi\s*:(.*?)\bProof\.', read(literal), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous closed proof-view bridge')
        equal(found[0], suffix + '_bytes txi = haskell_issuance_proof_view ' + token + ' txi.', view_lemma)
        for prefix in ['', 'current_']:
            for is_literal in [False, True]:
                v = 'txi' if prefix or is_literal else 'txo'
                relation = ('current_ptr_rep' if prefix else 'indexed_ptr_rep') + ' (fun e => sigTxIn (Elements.envTx e)) '
                relation += 'Elements.envIx ' if prefix else ''
                relation += '(fun m b ofs ' + v + ' => uint32_array_at m b ofs (' + suffix + '_words ' + v + ')) 544 ' + str(offset) + ' 0 696'
                target = ('elements_' + prefix + suffix + '_literal_spec' if is_literal else
                          '(fun a environment => @elements_' + prefix + suffix + '_spec (PrimitivePrimSem option_Monad_Zero) a environment)')
                theorem(literal if is_literal else current if prefix else indexed,
                        'elements_' + prefix + suffix + ('_literal' if is_literal else '') + '_local_spec',
                        'application_jet_local_spec_sep f_simplicity_' + prefix + suffix + ' elements_ge Elements.env ' +
                        ('Ty.Unit Word256' if prefix else 'Word32 (Ty.Sum Ty.Unit Word256)') + ' (' + relation + ') ' + target + '.')
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=['Elements.' + p + t for p in ['', 'Current'] for t in ['IssuanceAssetProof', 'IssuanceTokenProof']],
                  proof_view_cases_reviewed=True, selected_canonical_correspondence_reviewed=True,
                  formal_host_lens_equivalence=False, formal_host_crypto_equivalence=False,
                  normal_registration=False, kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'literal']:
        p.add_argument('--' + name, type=Path, required=True)
    args = p.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.literal), indent=2))
