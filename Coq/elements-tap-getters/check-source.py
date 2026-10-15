"""Selected raw-key/byte-index source correspondence, not a proof checker.

Preserve the original nullable-128 relation and execution proof while reviewing
the explicit 255 generalization. No host-library or caller-construction claim.
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
    shared = load('tap_hash_source', HERE.parent / 'elements-hash-literal/check-source.py')
    r = shared.check(repo, coq, coq / 'C/jet_haskell_hash_word.v', coq / 'C/jet_elements_hash_literal.v')
    p = load('tap_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(a, b, label):
        if p.compact(a) != p.compact(b):
            raise ValueError('tap-getter source differs: ' + label)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous definition: ' + name)
        equal(found[0], expected, name)

    def line(code, start, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(start) + r'\s*=([^\n]*)$', code)
        if len(found) != 1:
            raise ValueError('missing/ambiguous Haskell clause: ' + start)
        equal(found[0], expected, start)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Theorem|Lemma)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous full contract: ' + name)
        equal(found[0], expected, name)

    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    for tag, name, domain, codomain, body in [
        ('InternalKey', 'internalKey', '()', 'PubKey',
         'element . return . encodeKey . tapInternalKey $ envTap env'),
        ('Tappath', 'tappath', 'Word8', '(S Word256)',
         'return . cast . fmap encodeHash . listToMaybe . flip drop (tappath (envTap env)) . fromInteger . fromWord8')]:
        p.require(catalog, tag + ' :: TransactionJet ' + domain + ' ' + codomain, 'catalog type')
        line(catalog, 'specificationTransaction ' + tag, 'primitive Prim.' + tag)
        p.require(hs, tag + ' :: Prim ' + domain + ' ' + codomain, 'primitive type')
        line(hs, 'primName ' + tag, '"' + name + '"')
        line(hs, 'interpret ' + tag, body)
    line(hs, 'encodeKey (Schnorr.PubKey x)', 'toWord256 . toInteger $ x')
    schnorr = read(repo / 'Haskell/Core/Simplicity/LibSecp256k1/Schnorr.hs')
    p.require(schnorr, 'import Simplicity.Word', 'native Word256 import')
    found = re.findall(r'(?m)^data PubKey\s*=([^\n]*)$', schnorr)
    if len(found) != 1:
        raise ValueError('missing/ambiguous PubKey carrier')
    equal(found[0], 'PubKey Word256', 'raw four-limb key, not FE/point')
    line(schnorr, 'put (PubKey x)', 'put x')
    numeric = read(repo / 'Haskell/Core/Simplicity/Word.hs')
    line(numeric, 'put (Word256 a3 a2 a1 a0)', 'put a3 >> put a2 >> put a1 >> put a0')
    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    for fragment in ['tapInternalKey :: PubKey', 'tappath :: [Hash256]']:
        p.require(data, fragment, 'tap field carrier')
    words = read(repo / 'Haskell/Core/Simplicity/Ty/Word.hs')
    line(words, 'fromWord8', 'fromWord word8')
    # Shared guard checks the recursive word shape and bit injections.
    p.require(words, 'type Word8 = Vector8 Bit', 'eight-bit index')
    portpath = coq / 'C/jet_elements_prim.v'
    port = read(portpath)
    for fragment in ['; tapInternalKey : hash256', '; tappath : list hash256',
                     '| Tappath : prim Word8 (S Word256)', '| InternalKey : prim Unit Word256',
                     '| Tappath => "tappath"', '| InternalKey => "internalKey"']:
        p.require(port, fragment, 'Coq carrier/identity')
    sem = p.definition(port, 'sem')
    for tag, following, expected in [
        ('Tappath', 'InternalKey', '''fun i : Word8 => Some (cast (option_map encodeHash
            (nth_error (tappath (envTap e)) (Z.to_nat (toZ i)))))'''),
        ('InternalKey', 'OutputAsset', 'fun _ => Some (from_hash256 (tapInternalKey (envTap e)))')]:
        if sem.count('| ' + tag + ' =>') != 1 or sem.count('| ' + following + ' =>') != 1:
            raise ValueError('ambiguous primitive case')
        equal(sem.split('| ' + tag + ' =>', 1)[1].split('| ' + following + ' =>', 1)[0], expected, tag)
    literal = coq / 'C/jet_elements_tap_getters_literal.v'
    definition(literal, 'haskell_encode_pubkey', '''haskell_to_word 8 (haskell_word256_integer
      (haskell_be256_run (hash256_to_bytelist h) (haskell_word256_from_integer 0)))''')
    definition(literal, 'elements_internal_key_literal_spec',
               'Some (haskell_encode_pubkey (tapInternalKey (Elements.envTap environment)))')
    definition(literal, 'word_indexed_digest_literal', '''Some
      (match hd_error (skipn (Z.to_nat (haskell_from_word depth a)) values) with
       | None => inl tt | Some h => inr (haskell_to_word 8
         (haskell_integer_hash256 (hash256_to_bytelist h))) end)''')
    definition(literal, 'elements_tappath_literal_spec',
               'word_indexed_digest_literal 3 (tappath (Elements.envTap environment)) a')
    statement(literal, 'nth_error_is_list_to_maybe_drop',
              '{A : Type} (xs : list A) n : nth_error xs n = hd_error (skipn n xs).')
    statement(literal, 'tappath_literal_index_range',
              '(a : tySem Word8) : 0 <= haskell_from_word 3 a < 256.')
    indexed = coq / 'C/jet_elements_tappath_local.v'
    key = coq / 'C/jet_elements_hash_field_jets.v'
    definition(indexed, 'elements_tappath_spec', 'Primitive.Combinators.prim Elements.Tappath')
    definition(key, 'elements_internal_key_spec', 'Primitive.Combinators.prim Elements.InternalKey')
    definition(coq / 'C/jet_elements_hash_getter_local.v', 'hash_getter_rep', r'''
      exists be ebase bt tbase,
        env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= tbase /\ tbase + psz <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + pdelta) = Some (Vptr bt (Ptrofs.repr tbase)) /\
        uint32_array_at m bt (tbase + hdelta) (hash256_reg (hash_of e)) /\
        fp = [(be, ebase + pdelta, ebase + pdelta + 8); (bt, tbase + hdelta, tbase + hdelta + 32)]''')
    key_prefix = ': application_jet_local_spec_sep f_simplicity_internal_key elements_ge Elements.env Ty.Unit Word256 '
    key_rep = '(hash_getter_rep (fun e => tapInternalKey (Elements.envTap e)) 8 104 176) '
    statement(key, 'elements_internal_key_local_spec', key_prefix + key_rep +
              '(fun a environment => @elements_internal_key_spec (PrimitivePrimSem option_Monad_Zero) a environment).')
    statement(literal, 'elements_internal_key_literal_local_spec', key_prefix + key_rep + 'elements_internal_key_literal_spec.')
    nullable = coq / 'C/jet_elements_tappath_nullable.v'
    # Exact original predicate (source SHA256 3bf756ed25aa63ebd6b2bd8155ffcd336
    # 20df78043820523b271b82f7c32f768). No dependence on a temporary base path.
    original_body = r'''exists be ebase bt tbase bp pbase,
      env = Vptr be (Ptrofs.repr ebase) /\
      (length (tappath (Elements.envTap e)) <= 128)%nat /\
      0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
      0 <= tbase /\ tbase + 176 <= Ptrofs.max_unsigned /\
      0 <= pbase /\ pbase + 32 * Z.of_nat (length (tappath (Elements.envTap e))) <= Ptrofs.max_unsigned /\
      Mem.load Mptr m be (ebase + 8) = Some (Vptr bt (Ptrofs.repr tbase)) /\
      (0 < Z.of_nat (length (tappath (Elements.envTap e))) ->
       Mem.load Mptr m bt (tbase + 0) = Some (Vptr bp (Ptrofs.repr pbase))) /\
      Mem.load Mint8unsigned m bt (tbase + 168) =
        Some (Vint (Int.repr (Z.of_nat (length (tappath (Elements.envTap e)))))) /\
      (forall j h, nth_error (tappath (Elements.envTap e)) j = Some h ->
        hash_elem_rep m bp (pbase + 32 * Z.of_nat j) h) /\
      fp = [(be, ebase + 8, ebase + 16); (bt, tbase + 0, tbase + 8);
            (bp, pbase, pbase + 32 * Z.of_nat (length (tappath (Elements.envTap e))))]'''
    definition(nullable, 'elements_tappath_env_rep_bounded', original_body.replace('<= 128', '<= limit'))
    definition(nullable, 'elements_tappath_env_rep_nullable', 'elements_tappath_env_rep_bounded 128')
    definition(nullable, 'elements_tappath_env_rep_u8', 'elements_tappath_env_rep_bounded 255')
    statement(nullable, 'elements_tappath_nullable_128_unchanged',
              'm env e fp : elements_tappath_env_rep_nullable m env e fp <-> ' + original_body + '.')
    prefix = ': application_jet_local_spec_sep f_simplicity_tappath elements_ge Elements.env Word8 (Ty.Sum Ty.Unit Word256) '
    target = '(fun a environment => @elements_tappath_spec (PrimitivePrimSem option_Monad_Zero) a environment).'
    for version in ['nullable', 'u8']:
        rep = 'elements_tappath_env_rep_' + version + ' '
        statement(nullable, 'elements_tappath_' + version + '_local_spec', prefix + rep + target)
        statement(literal, 'elements_tappath_' + version + '_literal_local_spec', prefix + rep + 'elements_tappath_literal_spec.')
    statement(nullable, 'elements_tappath_bounded_local_spec',
              '(limit : nat) (Hlimit : (limit <= 255)%nat) ' + prefix + '(elements_tappath_env_rep_bounded limit) ' + target)
    # No new execution premise is slipped into the reused C proof. Its only
    # proof-body change is the bound supplied by the new explicit parameter.
    def proof(code, name):
        found = re.findall(r'\b(?:Lemma|Theorem)\s+' + re.escape(name) + r'\b.*?\bProof\.(.*?)\bQed\.', code, re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous execution proof: ' + name)
        return found[0]
    body = p.compact(proof(read(nullable), 'elements_tappath_bounded_local_spec'))
    if hashlib.sha256(body.encode()).hexdigest() != 'e123c18958a81a1a5dc38a6343b1980b984b823641bc36948cb8eebc340bceaf':
        raise ValueError('actual execution proof differs beyond the generalized byte bound')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jets=['Elements.InternalKey', 'Elements.Tappath'],
             original_nullable_128_preserved=True, c_byte_length_bound=255,
             null_pointer_allowed_for_empty_path=True, whole_contracts_reviewed=True,
             caller_cache_construction_proved=False, formal_host_library_equivalence=False,
             normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
