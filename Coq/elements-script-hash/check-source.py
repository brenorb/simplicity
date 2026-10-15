"""Four script-hash primitives/programs and their entire represented-C contracts.

The Digest byte-string hash is the existing primitive model. This guard pins
its use; it does not certify the Haskell cryptography implementation or callers
which populate the C cached fields.
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
    digest = load('script_hash_digest_source', coq / 'elements-hash-literal/check-source.py')
    record = digest.check(repo, coq, coq / 'C/jet_haskell_hash_word.v', coq / 'C/jet_elements_hash_literal.v')
    current = load('script_hash_current_source', coq / 'elements-current-sequence/check-source.py')
    shared = current.check(repo, coq, coq / 'C/jet_elements_sequence_literal.v', coq / 'C/jet_elements_current_sequence_literal.v')
    record['source_sha256'].update(shared['source_sha256'])
    parser = load('script_hash_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return parser.read_code(path)

    def equal(actual, expected, label):
        if parser.compact(actual) != parser.compact(expected):
            raise ValueError('script-hash source differs: ' + label)

    def definition(path, name, expected):
        matches = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                             r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous script-hash definition: ' + name)
        equal(matches[0], expected, name)

    def line(text, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', text)
        if len(found) != 1:
            raise ValueError('missing/ambiguous script-hash clause: ' + start)
        equal(found[0], expected, start)

    def theorem(path, name, expected):
        found = re.findall(r'\bTheorem\s+' + re.escape(name) + r'\s*:(.*?)\bProof\.', read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous script-hash whole-C contract: ' + name)
        equal(found[0], expected, name)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    primitive = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    program = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction.hs')
    library = read(repo / 'Haskell/Simplicity/Elements/Programs/Transaction/Lib.hs')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for fragment in ['type Script = BSL.ByteString', 'utxoScript :: Script', 'sigTxiScriptSig :: Script']:
        parser.require(data, fragment, 'selected script carrier')
    line(read(repo / 'Haskell/Core/Simplicity/Digest.hs'), 'bslHash', 'ivHash . IV . pushChunks sha256Incremental . padSHA1')
    definition(coq / 'Simplicity/Digest.v', 'byteStringHash', '''
      Hash256 (process_msg SHA256.init_registers (generate_and_pad_alt x)) (length_process_msg _)''')
    port = read(coq / 'C/jet_elements_prim.v')
    parser.require(port, 'Definition script := list byte.', 'script byte list')
    parser.require(port, 'utxoScript : script', 'UTXO script field')
    parser.require(port, 'sigTxiScriptSig : script', 'scriptSig field')
    indexed = coq / 'C/jet_elements_input_hash_jets.v'
    current_path = coq / 'C/jet_elements_current_input_jets.v'
    definition(indexed, 'utxo_script_bytes', 'utxoScript (sigTxiTxo txi)')
    definition(literal, 'elements_input_digest_literal_spec', '''
      Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
        | None => inl tt
        | Some txi => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (hash_of txi)))) end)''')
    selected = []
    for suffix, tag, words, coq_bytes, hs_bytes, offset in [
        ('script_hash', 'ScriptHash', 'utxo_script_hash_words', 'utxo_script_bytes', 'utxoScript . sigTxiTxo', 136),
        ('script_sig_hash', 'ScriptSigHash', 'script_sig_hash_words', 'sigTxiScriptSig', 'sigTxiScriptSig', 64),
    ]:
        for prefix, hs_prefix, domain, output in [('input', 'Input', 'Word32', '(S Word256)'), ('current', 'Current', '()', 'Word256')]:
            jet = hs_prefix + tag
            parser.require(catalog, jet + ' :: TransactionJet ' + domain + ' ' + output, 'selected jet type')
            line(catalog, 'specificationTransaction ' + jet,
                 'primitive Prim.' + jet if prefix == 'input' else 'Prog.current' + tag)
            selected.append('Elements.' + jet)
        line(primitive, 'primName Input' + tag, '"input' + tag + '"')
        line(primitive, 'interpret Input' + tag, 'return . (atInput $ encodeHash . bslHash . ' + hs_bytes + ')')
        clause = ('utxoScript (sigTxiTxo txi)' if suffix == 'script_hash' else 'sigTxiScriptSig txi')
        parser.require(port, '| Input' + tag + ' : prim Word32 (S Word256)', 'primitive type')
        parser.require(port, '| Input' + tag + ' => "input' + tag + '"', 'primitive identity')
        sem = parser.definition(port, 'sem')
        matches = re.findall(r'(?m)^\s*\| Input' + tag + r' =>([^\n]*)$', sem)
        if len(matches) != 1:
            raise ValueError('missing/ambiguous selected primitive semantics')
        equal(matches[0], 'atInput (fun txi => encodeHash (byteStringHash (' + clause + ')))', 'primitive hash projection')
        if program.count('lib = l') != 1:
            raise ValueError('ambiguous transaction library')
        matches = re.findall(r'(?m)^\s*, current' + tag + r'\s*=([^\n]*)$', program.split('lib = l', 1)[1])
        if len(matches) != 1:
            raise ValueError('missing/ambiguous current script-hash program')
        equal(matches[0], 'primitive CurrentIndex >>> assert (primitive Input' + tag + ')', 'current assertion program')
        line(library, 'current' + tag, 'Transaction.current' + tag + ' Transaction.lib')
        definition(indexed, words, 'hash256_reg (byteStringHash (' + coq_bytes + ' txo))')
        definition(indexed, 'elements_input_' + suffix + '_spec', 'Primitive.Combinators.prim Elements.Input' + tag)
        definition(literal, 'elements_input_' + suffix + '_literal_spec',
                   'elements_input_digest_literal_spec (fun txi => byteStringHash (' + coq_bytes + ' txi))')
        definition(current_path, 'elements_current_' + suffix + '_spec', 'elements_current_spec (@elements_input_' + suffix + '_spec alg)')
        definition(literal, 'elements_current_' + suffix + '_literal_spec', 'elements_current_literal_result elements_input_' + suffix + '_literal_spec')
        for prefix in ['input', 'current']:
            for is_literal in [False, True]:
                v = 'txi' if is_literal or prefix == 'current' else 'txo'
                relation = ('indexed_ptr_rep' if prefix == 'input' else 'current_ptr_rep')
                relation += ' (fun e => sigTxIn (Elements.envTx e)) ' + ('' if prefix == 'input' else 'Elements.envIx ')
                relation += '(fun m b ofs ' + v + ' => uint32_array_at m b ofs (' + words + ' ' + v + ')) 544 ' + str(offset) + ' 0 696'
                target = ('elements_' + prefix + '_' + suffix + '_literal_spec' if is_literal else
                          '(fun a environment => @elements_' + prefix + '_' + suffix + '_spec (PrimitivePrimSem option_Monad_Zero) a environment)')
                name = 'elements_' + prefix + '_' + suffix + ('_literal' if is_literal else '') + '_local_spec'
                theorem(literal if is_literal else indexed if prefix == 'input' else current_path, name,
                        'application_jet_local_spec_sep f_simplicity_' + prefix + '_' + suffix + ' elements_ge Elements.env ' +
                        ('Word32 (Ty.Sum Ty.Unit Word256)' if prefix == 'input' else 'Ty.Unit Word256') + ' (' + relation + ') ' + target + '.')
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
        (forall j x, nth_error (elems_of environment) j = Some x -> elemrep m bin (inbase + sz * Z.of_nat j + poff) x) /\
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
        (forall j x, nth_error (elems_of environment) j = Some x -> elemrep m bin (inbase + sz * Z.of_nat j + poff) x) /\
        fp = [(bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))].'''.removesuffix('.'))
    record['source_sha256'].update({str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(set(paths))})
    record.update(selected_jets=selected, represented_cached_hashes=True, whole_contracts_reviewed=True,
                  new_hash_algorithm_proof=False, caller_cache_construction_proved=False,
                  normal_registration=False, kernel_checked_by_this_tool=False)
    return record


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    for name in ['repo', 'coq', 'literal']:
        p.add_argument('--' + name, type=Path, required=True)
    args = p.parse_args()
    print(json.dumps(check(args.repo, args.coq, args.literal), indent=2))
