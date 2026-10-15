"""Selected optional-pegin digest programs and complete actual-C contracts."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def check(repo, coq, literal):
    digest = load('pegin_digest_source', coq / 'elements-hash-literal/check-source.py')
    record = digest.check(repo, coq, coq / 'C/jet_haskell_hash_word.v', coq / 'C/jet_elements_hash_literal.v')
    current = load('pegin_current_source', coq / 'elements-current-sequence/check-source.py')
    extra = current.check(repo, coq, coq / 'C/jet_elements_sequence_literal.v', coq / 'C/jet_elements_current_sequence_literal.v')
    record['source_sha256'].update(extra['source_sha256'])
    parser = load('pegin_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('pegin correspondence differs: ' + label)

    def definition(path, name, expected):
        matches = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                             r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous selected definition: ' + name)
        equal(matches[0], expected, name)

    def line(source, start, expected):
        clauses = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', source)
        if len(clauses) != 1:
            raise ValueError('missing/ambiguous pegin clause: ' + start)
        equal(clauses[0], expected, start)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    for fragment in ['InputPegin :: TransactionJet Word32 (S (S Word256))',
                     'CurrentPegin :: TransactionJet () (S Word256)']:
        parser.require(catalog, fragment, 'selected jet type')
    line(catalog, 'specificationTransaction InputPegin', 'primitive Prim.InputPegin')
    line(catalog, 'specificationTransaction CurrentPegin', 'Prog.currentPegin')
    primitive = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    parser.require(primitive, 'InputPegin :: Prim Word32 (S (S Word256))', 'primitive domain/presence tags')
    line(primitive, 'primName InputPegin', '"inputPegin"')
    line(primitive, 'interpret InputPegin', 'return . (atInput $ cast . fmap encodeHash . sigTxiPegin)')
    parser.require(read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'),
                   'sigTxiPegin :: Maybe Hash256', 'optional direct hash, not pegin bytes')
    port = read(coq / 'C/jet_elements_prim.v')
    parser.require(port, 'sigTxiPegin : option hash256', 'Coq optional digest carrier')
    parser.require(port, '| InputPegin : prim Word32 (S (S Word256))', 'Coq primitive type')
    parser.require(port, '| InputPegin => "inputPegin"', 'Coq identity')
    sem = parser.definition(port, 'sem')
    if sem.count('| InputPegin =>') != 1 or sem.count('| InputPrevOutpoint =>') != 1:
        raise ValueError('ambiguous pegin semantic clause')
    equal(sem.split('| InputPegin =>', 1)[1].split('| InputPrevOutpoint =>', 1)[0],
          'atInput (fun txi => cast (option_map encodeHash (sigTxiPegin txi)))', 'nested optional primitive')
    definition(coq / 'C/jet_elements_prim.v', 'encodeHash', 'from_hash256 h')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    line(library, 'currentPegin', 'Transaction.currentPegin Transaction.lib')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    if program.count('lib = l') != 1:
        raise ValueError('ambiguous Transaction library')
    clauses = re.findall(r'(?m)^\s*, currentPegin\s*=([^\n]*)$', program.split('lib = l', 1)[1])
    if len(clauses) != 1:
        raise ValueError('missing/ambiguous current pegin program')
    equal(clauses[0], 'primitive CurrentIndex >>> assert (primitive InputPegin)', 'current assertion composition')
    indexed = coq / 'C/jet_elements_pegin_local.v'
    definition(indexed, 'elements_input_pegin_hash_spec', 'Primitive.Combinators.prim Elements.InputPegin')
    definition(indexed, 'elements_pegin_hashes', 'map sigTxiPegin (sigTxIn (Elements.envTx e))')
    definition(indexed, 'is_some', 'match o with Some _ => true | None => false end')
    definition(indexed, 'bit_int', 'if b then Int.one else Int.zero')
    definition(indexed, 'pegin_elem_rep', r'''
      Mem.load Mint8unsigned m b (ofs + 537) = Some (Vint (bit_int (is_some o))) /\
      forall h, o = Some h -> hash_elem_rep m b (ofs + 32) h''')
    definition(indexed, 'elements_input_pegin_hash_env_rep', r'''
      exists be ebase bt txbase bin inbase nI,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
        0 <= inbase /\ inbase + 544 * Z.of_nat (length (elements_pegin_hashes e)) <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
        Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
        Mem.load Mint64 m bt (txbase + 696) = Some (Vlong nI) /\
        Int64.unsigned nI = Z.of_nat (length (elements_pegin_hashes e)) /\
        (forall j o, nth_error (elements_pegin_hashes e) j = Some o ->
          pegin_elem_rep m bin (inbase + 544 * Z.of_nat j) o) /\
        fp = [(be, ebase, ebase + 8); (bt, txbase + 0, txbase + 8);
              (bin, inbase, inbase + 544 * Z.of_nat (length (elements_pegin_hashes e)))]''')
    definition(coq / 'C/jet_elements_hash_elem.v', 'hash_elem_rep', 'uint32_array_at m b ofs (hash256_reg h)')
    current = coq / 'C/jet_elements_current_gen_jets.v'
    definition(current, "elements_input_pegin_spec'", 'Primitive.Combinators.prim Elements.InputPegin')
    definition(current, 'elements_current_pegin_spec', "elements_current_spec (@elements_input_pegin_spec' alg)")
    definition(current, 'flag_bit', 'if b then Int.one else Int.zero')
    definition(current, 'flag_hash_rep', r'''
      Mem.load Mint8unsigned m b (ofs + foff) = Some (Vint (flag_bit (opt_is_some (g txi)))) /\
      forall h, g txi = Some h -> hash_elem_rep m b (ofs + hoff) h''')
    definition(coq / 'C/jet_elements_current_gen.v', 'current_gen_rep', r'''
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
        Int64.unsigned ixv = Z.of_nat (Elements.envIx environment) /\
        (forall j x, nth_error (elems_of environment) j = Some x ->
          elemrep m bin (inbase + sz * Z.of_nat j) x) /\
        fp = [(be, ebase, ebase + 8); (be, ebase + 80, ebase + 88);
              (bt, txbase + adelta, txbase + adelta + 8);
              (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))]''')
    definition(literal, 'elements_input_pegin_literal_spec', '''
      Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
        | None => inl tt | Some txi => inr (match sigTxiPegin txi with
          | None => inl tt
          | Some h => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) end) end)''')
    definition(literal, 'elements_current_pegin_literal_spec', 'elements_current_literal_result elements_input_pegin_literal_spec')
    representations = {
        'input': 'elements_input_pegin_hash_env_rep',
        'current': '(current_gen_rep (fun e => sigTxIn (Elements.envTx e)) (flag_hash_rep sigTxiPegin 537 32) 544 0 696)',
    }
    for prefix, path, theorem, target in [
        ('input', indexed, 'elements_input_pegin_hash_local_spec', '(fun a environment => @elements_input_pegin_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment)'),
        ('current', current, 'elements_current_pegin_local_spec', '(fun a environment => @elements_current_pegin_spec (PrimitivePrimSem option_Monad_Zero) a environment)'),
        ('input', literal, 'elements_input_pegin_literal_local_spec', 'elements_input_pegin_literal_spec'),
        ('current', literal, 'elements_current_pegin_literal_local_spec', 'elements_current_pegin_literal_spec'),
    ]:
        statements = re.findall(r'Theorem ' + theorem + r'\s*:(.*?)\bProof\.', read(path), re.S)
        if len(statements) != 1:
            raise ValueError('missing/ambiguous whole pegin C contract')
        domain, output = ('Word32', '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))') if prefix == 'input' else ('Ty.Unit', '(Ty.Sum Ty.Unit Word256)')
        equal(statements[0], 'application_jet_local_spec_sep f_simplicity_' + prefix + '_pegin elements_ge Elements.env ' +
              domain + ' ' + output + ' ' + representations[prefix] + ' ' + target + '.', theorem)
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=['Elements.InputPegin', 'Elements.CurrentPegin'],
                  optional_direct_digest_reviewed=True, index_and_digest_conversion_reviewed=True,
                  normal_registration=False, kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'literal']:
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.literal), indent=2))
