"""Selected outpoint/output-script source correspondence, not a proof checker."""
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
    shared = load('indexed_source_annex', HERE.parent / 'elements-annex-hash/check-source.py')
    record = shared.check(repo, coq, coq / 'C/jet_elements_optional_digest_literal.v')
    parser = load('indexed_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('outpoint/output source differs: ' + label)

    def definition(path, name, expected):
        matches = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                             r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous indexed definition: ' + name)
        equal(matches[0], expected, name)

    def line(text, start, expected):
        matches = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', text)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous indexed clause: ' + start)
        equal(matches[0], expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    for jet, domain, output, binding in [
        ('InputPrevOutpoint', 'Word32', '(S (Word256,Word32))', 'primitive Prim.InputPrevOutpoint'),
        ('CurrentPrevOutpoint', '()', '(Word256,Word32)', 'Prog.currentPrevOutpoint'),
        ('OutputScriptHash', 'Word32', '(S Word256)', 'primitive Prim.OutputScriptHash'),
    ]:
        parser.require(catalog, jet + ' :: TransactionJet ' + domain + ' ' + output, 'selected catalog type')
        line(catalog, 'specificationTransaction ' + jet, binding)
    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    for jet, name, domain, output in [('InputPrevOutpoint', 'inputPrevOutpoint', 'Word32', '(S (Word256,Word32))'),
                                       ('OutputScriptHash', 'outputScriptHash', 'Word32', '(S Word256)')]:
        parser.require(hs, jet + ' :: Prim ' + domain + ' ' + output, 'selected primitive type')
        line(hs, 'primName ' + jet, '"' + name + '"')
    line(hs, 'interpret InputPrevOutpoint', 'return . (atInput $ encodeOutpoint . sigTxiPreviousOutpoint)')
    line(hs, 'interpret OutputScriptHash', 'return . (atOutput $ encodeHash . bslHash . txoScript)')
    line(hs, 'lookupOutput', '(sigTxOut tx !?) . fromIntegral')
    line(hs, 'atOutput f', 'cast . fmap f . lookupOutput . fromInteger . fromWord32')
    line(hs, 'encodeOutpoint op', '(encodeHash $ opHash op, toWord32 . fromIntegral $ opIndex op)')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for fragment in ['type Script = BSL.ByteString', 'opHash :: Hash256', 'opIndex :: Word32',
                     'sigTxiPreviousOutpoint :: Outpoint', 'txoScript :: Script']:
        parser.require(data, fragment, 'selected field carrier')
    portpath = coq / 'C/jet_elements_prim.v'
    port = read(portpath)
    for fragment in ['opHash : hash256', 'opIndex : int', 'sigTxiPreviousOutpoint : outpoint',
                     'txoScript : script', 'txoScript_bound : Zlength txoScript < Int.modulus',
                     '| InputPrevOutpoint : prim Word32 (S (Prod Word256 Word32))',
                     '| InputPrevOutpoint => "inputPrevOutpoint"',
                     '| OutputScriptHash : prim Word32 (S Word256)', '| OutputScriptHash => "outputScriptHash"']:
        parser.require(port, fragment, 'Coq carrier/identity/type')
    outpoint = re.findall(r'\bRecord outpoint\s*:\s*Set\s*:=\s*(.*?)\.', port, re.S)
    if len(outpoint) != 1:
        raise ValueError('missing/ambiguous Coq outpoint carrier')
    equal(outpoint[0], '{ opHash : hash256 ; opIndex : int }', 'whole Coq outpoint carrier')
    definition(portpath, 'script', 'list byte')
    definition(portpath, 'encodeOutpoint', '(encodeHash (opHash op), fromZ (Int.unsigned (opIndex op)) : tySem Word32)')
    sem = parser.definition(port, 'sem')
    for jet, following, body in [
        ('InputPrevOutpoint', 'InputAsset', 'atInput (fun txi => encodeOutpoint (sigTxiPreviousOutpoint txi))'),
        ('OutputScriptHash', 'OutputNullDatum', 'atOutput (fun txo => encodeHash (byteStringHash (txoScript txo)))'),
    ]:
        if sem.count('| ' + jet + ' =>') != 1 or sem.count('| ' + following + ' =>') != 1:
            raise ValueError('ambiguous primitive clause')
        equal(sem.split('| ' + jet + ' =>', 1)[1].split('| ' + following + ' =>', 1)[0], body, jet + ' primitive')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    line(library, 'currentPrevOutpoint', 'Transaction.currentPrevOutpoint Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous transaction library')
    matches = re.findall(r'(?m)^\s*, currentPrevOutpoint\s*=([^\n]*)$', program.split('lib = l', 1)[1])
    if len(matches) != 1:
        raise ValueError('missing/ambiguous current-outpoint program')
    equal(matches[0], 'primitive CurrentIndex >>> assert (primitive InputPrevOutpoint)', 'current outpoint')
    indexed, current = coq / 'C/jet_elements_indexed_ptr_jets.v', coq / 'C/jet_elements_current_input_jets.v'
    definition(indexed, 'elements_input_prev_outpoint_spec', 'Primitive.Combinators.prim Elements.InputPrevOutpoint')
    definition(indexed, 'elements_output_script_hash_spec', 'Primitive.Combinators.prim Elements.OutputScriptHash')
    definition(current, 'elements_current_prev_outpoint_spec', 'elements_current_spec (@elements_input_prev_outpoint_spec alg)')
    definition(indexed, 'outpoint_ix', 'Int64.repr (Int.unsigned (opIndex op))')
    definition(indexed, 'outpoint_words', 'hash256_reg (opHash (sigTxiPreviousOutpoint txi))')
    definition(indexed, 'outpoint_rep', r'''uint32_array_at m b ofs (outpoint_words txi) /\
      Mem.load Mint64 m b (ofs + 32) = Some (Vlong (outpoint_ix (sigTxiPreviousOutpoint txi)))''')
    definition(indexed, 'script_hash_words', 'hash256_reg (byteStringHash (txoScript txo))')
    definition(coq / 'C/jet_elements_indexed_ptr.v', 'indexed_ptr_rep', r'''
      exists be ebase bt txbase bin inbase nI,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
        0 <= inbase /\ inbase + sz * Z.of_nat (length (elems_of environment)) <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
        Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) /\
        Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) /\
        Int64.unsigned nI = Z.of_nat (length (elems_of environment)) /\
        (forall j x, nth_error (elems_of environment) j = Some x ->
          elemrep m bin (inbase + sz * Z.of_nat j + poff) x) /\
        fp = [(be, ebase, ebase + 8); (bt, txbase + adelta, txbase + adelta + 8);
              (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))]''')
    definition(coq / 'C/jet_elements_current_ptr_jets.v', 'current_ptr_rep', r'''
      exists be ebase bt txbase bin inbase nI ixv,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
        0 <= inbase /\ inbase + sz * Z.of_nat (length (elems_of environment)) <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
        Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) /\
        Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) /\
        Mem.load Mint64 m be (ebase + 80) = Some (Vlong ixv) /\
        Int64.unsigned nI = Z.of_nat (length (elems_of environment)) /\
        Int64.unsigned ixv = Z.of_nat (ix_of environment) /\
        (forall j x, nth_error (elems_of environment) j = Some x ->
          elemrep m bin (inbase + sz * Z.of_nat j + poff) x) /\
        fp = [(bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment))) ]''')
    definition(literal, 'elements_indexed_literal_result', '''Some
      (match nth_error (elems environment) (Z.to_nat (haskell_from_word 5 a)) with
       | None => inl tt | Some x => inr (encode x) end)''')
    definition(literal, 'haskell_encode_outpoint', '''
      (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (opHash op))),
       haskell_to_word 5 (Int.unsigned (opIndex op)))''')
    definition(literal, 'elements_input_prev_outpoint_literal_spec', '''
      elements_indexed_literal_result (fun e => sigTxIn (Elements.envTx e))
        (fun txi => haskell_encode_outpoint (sigTxiPreviousOutpoint txi))''')
    definition(literal, 'elements_current_prev_outpoint_literal_spec', 'elements_current_literal_result elements_input_prev_outpoint_literal_spec')
    definition(literal, 'elements_output_script_hash_literal_spec', '''
      elements_indexed_literal_result (fun e => sigTxOut (Elements.envTx e))
        (fun txo => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (byteStringHash (txoScript txo)))))''')
    for name, origin, shape in [
        ('input_prev_outpoint', indexed, 'Word32 (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32)) (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) outpoint_rep 544 96 0 696)'),
        ('current_prev_outpoint', current, 'Ty.Unit (Ty.Prod Word256 Word32) (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx outpoint_rep 544 96 0 696)'),
        ('output_script_hash', indexed, 'Word32 (Ty.Sum Ty.Unit Word256) (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e)) (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) 248 180 8 704)'),
    ]:
        for is_literal, path in [(False, origin), (True, literal)]:
            theorem = 'elements_' + name + ('_literal' if is_literal else '') + '_local_spec'
            target = ('elements_' + name + '_literal_spec' if is_literal else
                      '(fun a environment => @elements_' + name + '_spec (PrimitivePrimSem option_Monad_Zero) a environment)')
            found = re.findall(r'\bTheorem\s+' + theorem + r'\s*:(.*?)\bProof\.', read(path), re.S)
            if len(found) != 1:
                raise ValueError('missing/ambiguous complete C contract: ' + theorem)
            equal(found[0], 'application_jet_local_spec_sep f_simplicity_' + name + ' elements_ge Elements.env ' + shape + ' ' + target + '.', theorem)
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=['Elements.InputPrevOutpoint', 'Elements.CurrentPrevOutpoint', 'Elements.OutputScriptHash'],
                  outpoint_tuple_conversion_reviewed=True, output_script_digest_reviewed=True, whole_contracts_reviewed=True,
                  caller_cache_construction_proved=False, formal_host_crypto_equivalence=False,
                  normal_registration=False, kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for n in ['repo', 'coq', 'literal']:
        p.add_argument('--' + n, type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(check(a.repo, a.coq, a.literal), indent=2))
