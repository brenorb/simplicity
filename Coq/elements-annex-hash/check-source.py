"""Selected annex-hash primitive/current program and complete C contracts."""
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
    pegin = load('annex_source_pegin', HERE.parent / 'elements-pegin/check-source.py')
    record = pegin.check(repo, coq, coq / 'C/jet_elements_pegin_literal.v')
    parser = load('annex_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []
    def read(path):
        paths.append(path)
        return parser.read_code(path)
    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('annex-hash source differs: ' + label)
    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous annex definition: ' + name)
        equal(found[0], expected, name)
    def line(source, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous annex clause: ' + start)
        equal(found[0], expected, start)
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    primitive = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    for jet, domain, output, target in [('InputAnnexHash', 'Word32', '(S (S Word256))', 'primitive Prim.InputAnnexHash'),
                                       ('CurrentAnnexHash', '()', '(S Word256)', 'Prog.currentAnnexHash')]:
        parser.require(catalog, jet + ' :: TransactionJet ' + domain + ' ' + output, 'selected jet type')
        line(catalog, 'specificationTransaction ' + jet, target)
    line(primitive, 'primName InputAnnexHash', '"inputAnnexHash"')
    line(primitive, 'interpret InputAnnexHash', 'return . (atInput $ cast . fmap (encodeHash . bslHash) . sigTxiAnnex)')
    parser.require(read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'), 'sigTxiAnnex :: Maybe BSL.ByteString', 'optional annex bytes')
    line(read(repo / 'Haskell/Core/Simplicity/Digest.hs'), 'bslHash', 'ivHash . IV . pushChunks sha256Incremental . padSHA1')
    definition(coq / 'Simplicity/Digest.v', 'byteStringHash', 'Hash256 (process_msg SHA256.init_registers (generate_and_pad_alt x)) (length_process_msg _)')
    port = read(coq / 'C/jet_elements_prim.v')
    parser.require(port, 'sigTxiAnnex : option (list byte)', 'Coq optional byte carrier')
    parser.require(port, '| InputAnnexHash : prim Word32 (S (S Word256))', 'primitive type')
    parser.require(port, '| InputAnnexHash => "inputAnnexHash"', 'primitive identity')
    sem = parser.definition(port, 'sem')
    if sem.count('| InputAnnexHash =>') != 1 or sem.count('| InputScriptSigHash =>') != 1:
        raise ValueError('ambiguous annex primitive clause')
    equal(sem.split('| InputAnnexHash =>', 1)[1].split('| InputScriptSigHash =>', 1)[0],
          'atInput (fun txi => cast (option_map (fun x => encodeHash (byteStringHash x)) (sigTxiAnnex txi)))', 'optional hash primitive')
    line(read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs'), 'currentAnnexHash', 'Transaction.currentAnnexHash Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous transaction library')
    found = re.findall(r'(?m)^\s*, currentAnnexHash\s*=([^\n]*)$', program.split('lib = l', 1)[1])
    if len(found) != 1:
        raise ValueError('missing/ambiguous current annex program')
    equal(found[0], 'primitive CurrentIndex >>> assert (primitive InputAnnexHash)', 'current assertion')
    indexed, current = coq / 'C/jet_elements_annex_local.v', coq / 'C/jet_elements_current_gen_jets.v'
    definition(indexed, 'elements_annex_hashes', 'map (fun txi => option_map byteStringHash (sigTxiAnnex txi)) (sigTxIn (Elements.envTx e))')
    definition(indexed, 'annex_elem_rep', r'''Mem.load Mint8unsigned m b (ofs + 536) = Some (Vint (bit_int (is_some o))) /\
      forall h, o = Some h -> hash_elem_rep m b ofs h''')
    definition(indexed, 'bit_int', 'if b then Int.one else Int.zero')
    definition(indexed, 'is_some', 'match o with Some _ => true | None => false end')
    definition(indexed, 'elements_input_annex_hash_spec', 'Primitive.Combinators.prim Elements.InputAnnexHash')
    definition(indexed, 'elements_input_annex_hash_env_rep', r'''exists be ebase bt txbase bin inbase nI,
      env = Vptr be (Ptrofs.repr ebase) /\
      0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
      0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
      0 <= inbase /\ inbase + 544 * Z.of_nat (length (elements_annex_hashes e)) <= Ptrofs.max_unsigned /\
      Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
      Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
      Mem.load Mint64 m bt (txbase + 696) = Some (Vlong nI) /\
      Int64.unsigned nI = Z.of_nat (length (elements_annex_hashes e)) /\
      (forall j o, nth_error (elements_annex_hashes e) j = Some o -> annex_elem_rep m bin (inbase + 544 * Z.of_nat j) o) /\
      fp = [(be, ebase, ebase + 8); (bt, txbase + 0, txbase + 8);
            (bin, inbase, inbase + 544 * Z.of_nat (length (elements_annex_hashes e)))].'''.removesuffix('.'))
    definition(current, 'annex_hash_of', 'option_map byteStringHash (sigTxiAnnex txi)')
    definition(current, "elements_input_annex_hash_spec'", 'Primitive.Combinators.prim Elements.InputAnnexHash')
    definition(current, 'elements_current_annex_hash_spec', "elements_current_spec (@elements_input_annex_hash_spec' alg)")
    definition(literal, 'elements_input_optional_digest_literal_spec', '''Some
      (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
       | None => inl tt | Some txi => inr (match hash_of txi with
         | None => inl tt | Some h => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) end) end)''')
    definition(literal, 'elements_input_annex_hash_literal_spec', 'elements_input_optional_digest_literal_spec (fun txi => option_map byteStringHash (sigTxiAnnex txi))')
    definition(literal, 'elements_current_annex_hash_literal_spec', 'elements_current_literal_result elements_input_annex_hash_literal_spec')
    for prefix, path, name, target in [
        ('input', indexed, 'elements_input_annex_hash_local_spec', '(fun a environment => @elements_input_annex_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment)'),
        ('current', current, 'elements_current_annex_hash_local_spec', '(fun a environment => @elements_current_annex_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment)'),
        ('input', literal, 'elements_input_annex_hash_literal_local_spec', 'elements_input_annex_hash_literal_spec'),
        ('current', literal, 'elements_current_annex_hash_literal_local_spec', 'elements_current_annex_hash_literal_spec'),
    ]:
        found = re.findall(r'\bTheorem\s+' + name + r'\s*:(.*?)\bProof\.', read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous complete annex C contract')
        shape = ('Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) elements_input_annex_hash_env_rep' if prefix == 'input' else
                 'Ty.Unit (Ty.Sum Ty.Unit Word256) (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) (flag_hash_rep annex_hash_of 536 0) 544 0 696)')
        equal(found[0], 'application_jet_local_spec_sep f_simplicity_' + prefix + '_annex_hash elements_ge Elements.env ' + shape + ' ' + target + '.', name)
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=['Elements.InputAnnexHash', 'Elements.CurrentAnnexHash'], optional_direct_digest_reviewed=False,
                  optional_byte_hash_reviewed=True, whole_contracts_reviewed=True, caller_cache_construction_proved=False,
                  formal_host_crypto_equivalence=False, normal_registration=False, kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'literal']:
        p.add_argument('--' + name, type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(check(a.repo, a.coq, a.literal), indent=2))
