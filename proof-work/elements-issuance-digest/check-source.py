"""Selected direct issuance-digest projections and whole C contracts.

This checks correspondence of the selected sources, not host-language
compiler correctness. Kernel checking is a separate mandatory stage.
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
FAMILIES = [
    ('reissuance_blinding', 'ReissuanceBlinding', 'reissuanceBlinding', 'gh_blinding', 'inr re', 'reissuanceBlindingNonce re', 0,
     'either (const Nothing) (Just . reissuanceBlindingNonce)'),
    ('new_issuance_contract', 'NewIssuanceContract', 'newIssuanceContract', 'gh_contract', 'inl new', 'newIssuanceContractHash new', 0,
     'either (Just . newIssuanceContractHash) (const Nothing)'),
    ('reissuance_entropy', 'ReissuanceEntropy', 'reissuanceEntropy', 'gh_entropy', 'inr re', 'reissuanceEntropy re', 72,
     'either (const Nothing) (Just . reissuanceEntropy)'),
]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


def check(repo, coq, literal):
    inherited = load('issuance_digest_annex_guard', HERE.parent / 'elements-annex-hash/check-source.py')
    record = inherited.check(repo, coq, coq / 'C/jet_elements_optional_digest_literal.v')
    parser = load('issuance_digest_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('issuance direct-digest source differs: ' + label)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous direct-digest definition: ' + name)
        equal(found[0], expected, name)

    def line(source, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous direct-digest clause: ' + start)
        equal(found[0], expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    datatypes = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for carrier in ['type Issuance = Either NewIssuance Reissuance', 'sigTxiIssuance :: Maybe Issuance',
                    'newIssuanceContractHash :: Hash256', 'reissuanceBlindingNonce :: Hash256', 'reissuanceEntropy :: Entropy']:
        parser.require(datatypes, carrier, 'optional issuance/direct digest carrier')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous current issuance program library')
    indexed = coq / 'C/jet_elements_issuance_jets.v'
    current = coq / 'C/jet_elements_current_input_jets.v'
    portpath = coq / 'C/jet_elements_prim.v'
    port = read(portpath)
    sem = parser.definition(port, 'sem')
    definition(indexed, 'issuance_tag', 'match o with None => Int.repr 0 | Some (inl _) => Int.repr 1 | Some (inr _) => Int.repr 2 end')
    definition(indexed, 'issuance_hash_rep', r'''Mem.load Mint32 m b (ofs + 272) = Some (Vint (issuance_tag (sigTxiIssuance txi))) /\
      forall h, gh (sigTxiIssuance txi) = Some h -> uint32_array_at m b (ofs + delta) (hash256_reg h)''')
    definition(indexed, 'issuance_hash_result', '''match nth_error elems (Z.to_nat (toZ a)) with
      | Some txi => inr (match gh (sigTxiIssuance txi) with Some h => inr (from_hash256 h) | None => inl tt end)
      | None => inl tt end''')
    definition(literal, 'elements_reissuance_blinding_literal_spec',
               'elements_input_optional_digest_literal_spec (fun txi => gh_blinding (sigTxiIssuance txi))')
    selected = []
    for name, jet, camel, gh, branch, field, offset, projection in FAMILIES:
        currentjet, currentcamel = 'Current' + jet, 'current' + jet
        for j, domain, output, target in [(jet, 'Word32', '(S (S Word256))', 'primitive Prim.' + jet),
                                          (currentjet, '()', '(S Word256)', 'Prog.' + currentcamel)]:
            parser.require(catalog, j + ' :: TransactionJet ' + domain + ' ' + output, 'selected jet type')
            line(catalog, 'specificationTransaction ' + j, target)
            selected.append('Elements.' + j)
        line(hs, 'primName ' + jet, '"' + camel + '"')
        found = re.findall(r'(?m)^\s*interpret ' + jet + r'\s*=\s*(.*?)(?=\n\s*interpret |\Z)', hs, re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous multiline optional projection')
        equal(found[0], 'return . (atInput $ cast . fmap encodeHash . (' + projection + ' <=< sigTxiIssuance))', jet)
        parser.require(port, '| ' + jet + ' : prim Word32 (S (S Word256))', 'Coq primitive type')
        parser.require(port, '| ' + jet + ' => "' + camel + '"', 'Coq primitive identity')
        if sem.count('| ' + jet + ' =>') != 1:
            raise ValueError('ambiguous Coq optional projection')
        # Split at a top-level primitive clause, not an inner option branch.
        found = re.split(r'\n\s*\| [A-Z][A-Za-z0-9]* =>', sem.split('| ' + jet + ' =>', 1)[1], maxsplit=1)[0]
        equal(found, 'atInput (fun txi => cast (option_map encodeHash (match sigTxiIssuance txi with | Some (' + branch + ') => Some (' + field + ') | _ => None end)))', jet + ' port')
        definition(indexed, gh, 'match o with Some (' + branch + ') => Some (' + field + ') | _ => None end')
        definition(indexed, 'elements_' + name + '_spec', 'Primitive.Combinators.prim Elements.' + jet)
        definition(current, 'elements_current_' + name + '_spec', 'elements_current_spec (@elements_' + name + '_spec alg)')
        definition(literal, 'elements_' + name + '_literal_spec',
                   'elements_input_optional_digest_literal_spec (fun txi => ' + gh + ' (sigTxiIssuance txi))')
        definition(literal, 'elements_current_' + name + '_literal_spec', 'elements_current_literal_result elements_' + name + '_literal_spec')
        line(library, currentcamel, 'Transaction.' + currentcamel + ' Transaction.lib')
        found = re.findall(r'(?m)^\s*, ' + currentcamel + r'\s*=([^\n]*)$', program.split('lib = l', 1)[1])
        if len(found) != 1:
            raise ValueError('missing/ambiguous current issuance program')
        equal(found[0], 'primitive CurrentIndex >>> assert (primitive ' + jet + ')', currentjet)
        for is_current, original in [(False, indexed), (True, current)]:
            basename = 'elements_' + ('current_' if is_current else '') + name
            domain = 'Ty.Unit' if is_current else 'Word32'
            output = '(Ty.Sum Ty.Unit Word256)' if is_current else '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))'
            rep = ('current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx' if is_current else
                   'indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))') + ' (issuance_hash_rep ' + str(offset) + ' ' + gh + ') 544 256 0 696'
            for is_literal, path in [(False, original), (True, literal)]:
                theorem = basename + ('_literal' if is_literal else '') + '_local_spec'
                target = basename + '_literal_spec' if is_literal else '(fun a environment => @' + basename + '_spec (PrimitivePrimSem option_Monad_Zero) a environment)'
                found = re.findall(r'\bTheorem\s+' + theorem + r'\s*:(.*?)\bProof\.', read(path), re.S)
                if len(found) != 1:
                    raise ValueError('missing/ambiguous whole issuance C contract: ' + theorem)
                equal(found[0], 'application_jet_local_spec_sep f_simplicity_' + ('current_' if is_current else '') + name +
                      ' elements_ge Elements.env ' + domain + ' ' + output + ' (' + rep + ') ' + target + '.', theorem)
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=selected, optional_direct_digest_reviewed=True, whole_contracts_reviewed=True,
                  normal_registration=False, kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for n in ['repo', 'coq', 'literal']:
        p.add_argument('--' + n, type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(check(a.repo, a.coq, a.literal), indent=2))
