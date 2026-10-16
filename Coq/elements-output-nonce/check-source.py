"""Selected indexed nonce correspondence, with full C representation contracts.

Not a kernel checker, host-library equivalence proof, or normal acceptance.
The native Word256 nonce case must not be silently replaced by a field element.
"""
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent


def load(name, path):
    sp = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(m)
    return m


def check(repo):
    coq = repo / 'Coq'
    # Reuse exact index/lookup/representation and native-word decoder guards.
    indexed = load('nonce_indexed_source', HERE.parent / 'elements-outpoint-output/check-source.py')
    r = indexed.check(repo, coq, coq / 'C/jet_elements_indexed_literal.v')
    native = load('nonce_native_word_source', HERE.parent / 'elements-tap-getters/check-source.py')
    n = native.check(repo)
    r['source_sha256'].update(n['source_sha256'])
    p = load('nonce_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, name):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('output nonce source differs: ' + name)

    def line(source, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', source)
        if len(found) != 1:
            raise ValueError('missing/ambiguous nonce clause: ' + name)
        equal(found[0], expected, name)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous nonce definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Theorem|Lemma)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous whole nonce contract: ' + name)
        equal(found[0], expected, name)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    p.require(catalog, 'OutputNonce :: TransactionJet Word32 (S (S (Conf Word256)))', 'selected jet type')
    line(catalog, 'specificationTransaction OutputNonce', 'primitive Prim.OutputNonce')
    p.require(hs, 'OutputNonce :: Prim Word32 (S (S (Conf Word256)))', 'primitive type')
    line(hs, 'primName OutputNonce', '"outputNonce"')
    line(hs, 'interpret OutputNonce', 'return . (atOutput $ encodeNonce . txoNonce)')
    line(hs, 'encodeNonce', 'cast . fmap (((toBit *** (toWord256 . toInteger)) +++ encodeHash) . nonce)')
    line(hs, 'cast (Just x)', 'Right x')
    line(hs, 'cast Nothing', 'Left ()')
    p.require(data, 'newtype Nonce = Nonce { nonce :: Either (Bool, Word256) Hash256 } deriving Show',
              'raw Word256, not Schnorr.FE')
    p.require(data, 'txoNonce :: Maybe Nonce', 'optional field')
    bits = read(repo / 'Haskell/Core/Simplicity/Ty/Bit.hs')
    line(bits, 'toBit False', 'Left ()')
    line(bits, 'toBit True', 'Right ()')
    words = read(repo / 'Haskell/Core/Simplicity/Word.hs')
    line(words, 'put (Word256 a3 a2 a1 a0)', 'put a3 >> put a2 >> put a1 >> put a0')

    port = coq / 'C/jet_elements_prim.v'
    source = read(port)
    for fragment in ['Local Notation Conf a := (Sum (Prod Bit Word256) a).',
                     '| OutputNonce : prim Word32 (S (S (Conf Word256)))',
                     '| OutputNonce => "outputNonce"']:
        p.require(source, fragment, 'Coq primitive type/identity')
    definition(port, 'nonce', '(bool * hash256) + hash256')
    definition(port, 'encodeNonce', '''cast (option_map (fun x : nonce =>
      match x return tySem (Conf Word256) with
      | inl (odd, w) => inl (toBit odd, from_hash256 w)
      | inr h => inr (encodeHash h) end) n)''')
    sem = p.definition(source, 'sem')
    if sem.count('| OutputNonce =>') != 1 or sem.count('| OutputScriptHash =>') != 1:
        raise ValueError('ambiguous nonce primitive case')
    equal(sem.split('| OutputNonce =>', 1)[1].split('| OutputScriptHash =>', 1)[0],
          'atOutput (fun txo => encodeNonce (txoNonce txo))', 'primitive semantics')

    literal = coq / 'C/jet_elements_output_nonce_literal.v'
    p.require(read(literal), 'Local Notation ConfNonce := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word256).',
              'whole nonce sum shape')
    definition(literal, 'native_hash_word_literal', '''haskell_to_word 8 (haskell_word256_integer
      (haskell_be256_run (hash256_to_bytelist h) (haskell_word256_from_integer 0)))''')
    definition(literal, 'nonce_payload_literal', '''match n with
      | inl (odd, w) => inl ((if odd then inr tt else inl tt), native_hash_word_literal w)
      | inr h => inr (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h))) end''')
    definition(literal, 'encode_nonce_literal', 'match n with None => inl tt | Some v => inr (nonce_payload_literal v) end')
    definition(literal, 'word_indexed_value_literal', '''Some
      (match hd_error (skipn (Z.to_nat (haskell_from_word depth a)) values) with
       | None => inl tt | Some v => inr (enc v) end)''')
    definition(literal, 'elements_output_nonce_literal_spec', '''word_indexed_value_literal 5
      (fun txo => encode_nonce_literal (txoNonce txo)) (sigTxOut (Elements.envTx environment)) a''')
    statement(literal, 'output_nonce_literal_index_range', '(a : tySem Word32) : 0 <= haskell_from_word 5 a < 4294967296.')

    old = coq / 'C/jet_elements_asset_jets.v'
    definition(old, 'elements_output_nonce_spec', 'Primitive.Combinators.prim Elements.OutputNonce')
    definition(old, 'nonce_conf', '''match x with
      | inl (odd, w) => Confidential (Point odd w) tt | inr h => Explicit h end''')
    definition(old, 'conf_prefix', '''match c with | Explicit _ => Int.repr 1
      | Confidential (Point odd _) _ => if odd then Int.repr 3 else Int.repr 2 end''')
    definition(old, 'nonce_prefix', 'match n with Some x => conf_prefix (nonce_conf x) | None => Int.repr 0 end')
    definition(old, 'nonce_words', 'match n with Some x => asset_words (nonce_conf x) | None => repeat Int.zero 8 end')
    definition(old, 'nonce_rep', r'''(n <> None -> uint32_array_at m b ofs (nonce_words n)) /\
      Mem.load Mint32 m b (ofs + 32) = Some (Vint (nonce_prefix n))''')
    definition(old, 'elements_output_nonce_result', '''match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
      | Some txo => inr (encode_nonce (txoNonce txo)) | None => inl tt end''')
    prefix = ': application_jet_local_spec_sep f_simplicity_output_nonce elements_ge Elements.env Word32 '
    rep = '''(indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => nonce_rep m b ofs (txoNonce txo)) 248 144 8 704) '''
    statement(old, 'elements_output_nonce_local_spec', prefix +
        '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word256))) ' + rep +
        '(fun a environment => @elements_output_nonce_spec (PrimitivePrimSem option_Monad_Zero) a environment).')
    statement(literal, 'elements_output_nonce_literal_local_spec', prefix +
        '(Ty.Sum Ty.Unit (Ty.Sum Ty.Unit ConfNonce)) ' + rep + 'elements_output_nonce_literal_spec.')
    definition(coq / 'C/jet_elements_asset_helper.v', 'nonce_cells', '''
      if Int.eq (Int.repr 0) pfx then Some false :: repeat None 258
      else Some true :: asset_cells pfx xs''')

    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'//[^\n]*|/\*.*?\*/', '', cpath.read_text(), flags=re.S)
    def cbody(name, expected):
        found = list(re.finditer(r'\b(?:bool|void)\s+' + re.escape(name) + r'\s*\([^)]*\)\s*\{', c))
        if len(found) != 1:
            raise ValueError('missing/ambiguous actual nonce C function')
        start, end, depth = found[0].end(), found[0].end(), 1
        while end < len(c) and depth:
            depth += (c[end] == '{') - (c[end] == '}')
            end += 1
        if depth:
            raise ValueError('unterminated C function')
        equal(c[start:end-1], expected, name)
    cbody('simplicity_output_nonce', '''uint_fast32_t i = simplicity_read32(&src);
      if (writeBit(dst, i < env->tx->numOutputs)) { nonce(dst, &env->tx->output[i].nonce); }
      else { skipBits(dst, 259); } return true;''')
    cbody('nonce', '''if (writeBit(dst, NONE != nonce->prefix)) {
      if (writeBit(dst, EXPLICIT == nonce->prefix)) { skipBits(dst, 1); }
      else { writeBit(dst, ODD_Y == nonce->prefix); } writeHash(dst, &nonce->data);
      } else { skipBits(dst, 1+1+256); }''')
    p.require(read(repo / 'C/elements/txEnv.h'), 'NONE = 0, EXPLICIT = 1, EVEN_Y = 2, ODD_Y = 3', 'C prefix tags')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jets=['Elements.OutputNonce'], native_word_not_field_element=True,
             absent_explicit_and_parity_cases_reviewed=True, whole_contracts_reviewed=True,
             caller_environment_construction_proved=False, formal_host_library_equivalence=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
