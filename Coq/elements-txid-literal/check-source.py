"""Selected transaction_id source correspondence, not caller/hash correctness.

Retain the existing logical domain and cached-hash representation. Review both
the complete no-witness serialization and its transitive selected serializers;
checking the primitive name alone would not identify this specification.
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
    # This already reviews the packed-field carrier, clearPrf, native nonce
    # carrier and the four-limb hash decoder. Do not assert FE arithmetic.
    r = load('txid_shared_carriers', HERE.parent / 'elements-asset-literal/check-source.py').check(repo)
    p = load('txid_source_parser', coq / 'check-secp-predicates-specification.py')
    paths = []

    def read(path):
        paths.append(path)
        return p.read_code(path)

    def equal(actual, expected, name):
        if p.compact(actual) != p.compact(expected):
            raise ValueError('transaction_id source differs: ' + name)

    def line(text, name, expected):
        found = re.findall(r'(?m)^\s*' + re.escape(name) + r'\s*=([^\n]*)$', text)
        if len(found) != 1:
            raise ValueError('missing/ambiguous transaction_id clause: ' + name)
        equal(found[0], expected, name)

    def definition(path, name, expected):
        found = re.findall(r'\b(?:Definition|Fixpoint|Let)\s+' + re.escape(name) +
                           r"(?![\w']).*?:=(.*?)\.\s*(?:\n|$)", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous transaction_id definition: ' + name)
        equal(found[0], expected, name)

    def statement(path, name, expected):
        found = re.findall(r'\b(?:Lemma|Theorem)\s+' + re.escape(name) +
                           r"(?![\w'])(.*?)\bProof\.", read(path), re.S)
        if len(found) != 1:
            raise ValueError('missing/ambiguous transaction_id contract: ' + name)
        equal(found[0], expected, name)

    hs = read(repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs')
    catalog = read(repo / 'Haskell/Simplicity/Elements/Jets.hs')
    p.require(catalog, 'TransactionId :: TransactionJet () Word256', 'catalog type')
    p.require(hs, 'TransactionId :: Prim () Word256', 'primitive type')
    line(catalog, 'specificationTransaction TransactionId', 'primitive Prim.TransactionId')
    line(hs, 'primName TransactionId', '"transactionId"')
    line(hs, 'interpret TransactionId', 'element . return . encodeHash . txid $ tx')
    line(hs, 'tx', 'envTx env')
    line(hs, 'element', 'const')
    line(hs, 'encodeHash', 'toWord256 . integerHash256')

    data = read(repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs')
    # These clauses deliberately retain the original big-endian confidential
    # carriers, distinct from the little-endian transaction scalar fields.
    for name, expected in [
        ('putFE', 'put . fe_pack'),
        ('putAsset (Asset (Explicit h))', 'putWord8 0x01 >> put h'),
        ('putAsset (Asset (Confidential (Point by x) _))', 'putWord8 (if by then 0x0b else 0x0a) >> putFE x'),
        ('putAmount (Amount (Explicit v))', 'putWord8 0x01 >> putWord64be v'),
        ('putAmount (Amount (Confidential (Point by x) _))', 'putWord8 (if by then 0x09 else 0x08) >> putFE x'),
        ('put (Nonce (Right h))', 'putWord8 0x01 >> put h'),
        ('put (Nonce (Left (by, x)))', 'putWord8 (if by then 0x03 else 0x02) >> put x'),
        ('putMaybeConfidential _ Nothing', 'putWord8 0x00'),
        ('putMaybeConfidential p (Just a)', 'p a'),
        ('putNonce', 'putMaybeConfidential put'),
        ('txid', 'bslDoubleHash . runPutLazy . putNoWitnessTx')]:
        line(data, name, expected)
    start, stop = 'putNoWitnessTx :: Putter SigTx', 'txid :: SigTx -> Hash256'
    if data.count(start) != 1 or data.count(stop) != 1:
        raise ValueError('ambiguous no-witness serialization boundary')
    equal(data.split(start, 1)[1].split(stop, 1)[0], '''
putNoWitnessTx tx = do
  putWord32le $ sigTxVersion tx
  putWord8 0
  putVarInt (V.length (sigTxIn tx))
  mapM_ putInput (sigTxIn tx)
  putVarInt (V.length (sigTxOut tx))
  mapM_ putOutput (sigTxOut tx)
  putWord32le $ sigTxLock tx
 where
  putVarInt x | x < 0 = error "putVarInt: negative value"
              | x <= 0xFC = putWord8 (fromIntegral x)
              | x <= 0xFFFF = putWord8 0xFD >> putWord16le (fromIntegral x)
              | x <= 0xFFFFFFFF = putWord8 0xFE >> putWord32le (fromIntegral x)
              | x <= 0xFFFFFFFFFFFFFFFF = putWord8 0xFF >> putWord64le (fromIntegral x)
  putInput txi = do
    put (opHash (sigTxiPreviousOutpoint txi))
    putWord32le (flags .|. opIndex (sigTxiPreviousOutpoint txi))
    putVarInt (BSL.length (sigTxiScriptSig txi))
    putLazyByteString (sigTxiScriptSig txi)
    putWord32le (sigTxiSequence txi)
    putIssuance (sigTxiIssuance txi)
   where
    issuanceFlag | isJust (sigTxiIssuance txi) = 0x80000000
                 | otherwise = 0
    peginFlag | isJust (sigTxiPegin txi) = 0x40000000
              | otherwise = 0
    flags = issuanceFlag .|. peginFlag
    putIssuance Nothing = return ()
    putIssuance (Just (Left new)) = do
      put (0 :: Word256)
      put (newIssuanceContractHash new)
      putIssuanceAmount (clearAmountPrf (newIssuanceAmount new))
      putIssuanceAmount (clearAmountPrf (newIssuanceTokenAmount new))
    putIssuance (Just (Right re)) = do
      put (reissuanceBlindingNonce re)
      put (reissuanceEntropy re)
      putIssuanceAmount (clearAmountPrf (reissuanceAmount re))
      putWord8 0
    putIssuanceAmount (Amount (Explicit 0)) = putWord8 0
    putIssuanceAmount amt = putAmount amt
  putOutput txo = do
    putAsset (clearAssetPrf (txoAsset txo))
    putAmount (clearAmountPrf (txoAmount txo))
    putNonce (txoNonce txo)
    putVarInt (BSL.length (txoScript txo))
    putLazyByteString (txoScript txo)
''', 'complete no-witness serialization')

    digest = read(repo / 'Haskell/Core/Simplicity/Digest.hs')
    line(digest, 'put (Hash256 bs)', 'putShortByteString bs')
    line(digest, 'bslDoubleHash', 'bsHash . encode . bslHash')
    line(digest, 'bsHash', 'bslHash . BSL.fromStrict')
    line(digest, 'bslHash', 'ivHash . IV . pushChunks sha256Incremental . padSHA1')
    words = read(repo / 'Haskell/Core/Simplicity/Word.hs')
    line(words, 'put (Word256 a3 a2 a1 a0)', 'put a3 >> put a2 >> put a1 >> put a0')

    port = coq / 'C/jet_elements_prim.v'
    # No new serializer is introduced or silently substituted for the primitive
    # port. The exact reviewed bodies are the ones used in the C endpoint.
    ports = {
        'putHash256': 'hash256_to_bytelist x',
        'putLE': 'map (fun i => Byte.repr (z / two_power_nat (i * Byte.wordsize))) (seq 0 n)',
        'putBE': 'rev (putLE n z)',
        'putWord8': '[Byte.repr z]',
        'putVarInt': '''if Z.leb x 252 then putWord8 x else
          if Z.leb x 65535 then putWord8 253 ++ putLE 2 x else
          if Z.leb x 4294967295 then putWord8 254 ++ putLE 4 x else
          putWord8 255 ++ putLE 8 x''',
        'putFE': 'putHash256 x',
        'putAsset': '''match a with
          | Explicit h => putWord8 1 ++ putHash256 h
          | Confidential (Point odd x) _ => putWord8 (if odd then 11 else 10) ++ putFE x end''',
        'putAmount': '''match a with
          | Explicit v => putWord8 1 ++ putBE 8 (Int64.unsigned v)
          | Confidential (Point odd x) _ => putWord8 (if odd then 9 else 8) ++ putFE x end''',
        'putNonce': '''match n with | None => putWord8 0
          | Some (inr h) => putWord8 1 ++ putHash256 h
          | Some (inl (odd, x)) => putWord8 (if odd then 3 else 2) ++ putHash256 x end''',
        'putIssuanceAmount': '''match a with
          | Explicit v => if Int64.eq v Int64.zero then putWord8 0 else putAmount a
          | Confidential _ _ => putAmount a end''',
        'zeroHash256Bytes': 'repeat Byte.zero 32',
        'putTxIssuance': '''match i with | None => []
          | Some (inl new) => zeroHash256Bytes ++ putHash256 (newIssuanceContractHash new) ++
            putIssuanceAmount (clearPrf (newIssuanceAmount new)) ++
            putIssuanceAmount (clearPrf (newIssuanceTokenAmount new))
          | Some (inr re) => putHash256 (reissuanceBlindingNonce re) ++ putHash256 (reissuanceEntropy re) ++
            putIssuanceAmount (clearPrf (reissuanceAmount re)) ++ putWord8 0 end''',
        'isSome': 'match o with Some _ => true | None => false end',
        'putTxInput': '''let issuanceFlag := if isSome (sigTxiIssuance txi) then 2147483648 else 0 in
          let peginFlag := if isSome (sigTxiPegin txi) then 1073741824 else 0 in
          let flags := Z.lor issuanceFlag peginFlag in
          putHash256 (opHash (sigTxiPreviousOutpoint txi)) ++
          putLE 4 (Z.lor flags (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi)))) ++
          putVarInt (Zlength (sigTxiScriptSig txi)) ++ sigTxiScriptSig txi ++
          putLE 4 (Int.unsigned (sigTxiSequence txi)) ++ putTxIssuance (sigTxiIssuance txi)''',
        'putTxOutput': '''putAsset (clearPrf (txoAsset txo)) ++ putAmount (clearPrf (txoAmount txo)) ++
          putNonce (txoNonce txo) ++ putVarInt (Zlength (txoScript txo)) ++ txoScript txo''',
        'putNoWitnessTx': '''putLE 4 (Int.unsigned (sigTxVersion tx)) ++ putWord8 0 ++
          putVarInt (Zlength (sigTxIn tx)) ++ concat (map putTxInput (sigTxIn tx)) ++
          putVarInt (Zlength (sigTxOut tx)) ++ concat (map putTxOutput (sigTxOut tx)) ++
          putLE 4 (Int.unsigned (sigTxLock tx))''',
        'byteStringDoubleHash': 'byteStringHash (hash256_to_bytelist (byteStringHash x))',
        'txid': 'byteStringDoubleHash (putNoWitnessTx tx)'}
    for name, expected in ports.items():
        definition(port, name, expected)
    for fragment in ['| TransactionId : prim Unit Word256.',
                     '| TransactionId => "transactionId"',
                     'let tx := envTx e in',
                     '| TransactionId => fun _ => Some (encodeHash (txid tx))']:
        p.require(read(port), fragment, 'selected primitive port')
    p.require(read(port), '''Record sigTx : Set :=
      { sigTxVersion : int ; sigTxIn : list sigTxInput ; sigTxOut : list txOutput
      ; sigTxLock : int ; sigTxInBounds : (0 < Zlength sigTxIn < Int.modulus)%Z
      ; sigTxOutBounds : (0 <= Zlength sigTxOut < Int.modulus)%Z }.''',
      'unchanged represented transaction domain')
    for fragment in ['sigTxiScriptSig_bound : Zlength sigTxiScriptSig < Int.modulus',
                     'txoScript_bound : Zlength txoScript < Int.modulus']:
        p.require(read(port), fragment, 'unchanged represented script bounds')

    endpoint = coq / 'C/jet_elements_transaction_id_literal.v'
    definition(endpoint, 'elements_transaction_id_literal_spec',
               'elements_hash_literal_spec (fun e => txid (Elements.envTx e))')
    original = coq / 'C/jet_elements_hash_field_jets.v'
    definition(original, 'elements_transaction_id_spec', 'Primitive.Combinators.prim Elements.TransactionId')
    rep = '(hash_getter_rep (fun e => txid (Elements.envTx e)) 0 664 760)'
    for path, name, spec in [
        (endpoint, 'elements_transaction_id_literal_local_spec', 'elements_transaction_id_literal_spec'),
        (original, 'elements_transaction_id_local_spec',
         '(fun a environment => @elements_transaction_id_spec (PrimitivePrimSem option_Monad_Zero) a environment)')]:
        statement(path, name, ': application_jet_local_spec_sep f_simplicity_transaction_id '
                  'elements_ge Elements.env Ty.Unit Word256 ' + rep + ' ' + spec + '.')
    statement(original, 'elements_transaction_id_getter_body', ''' :
      elements_wrapper_shape f_simplicity_transaction_id (elements_simple_rest
        (elements_hash_mid_write32s _tx _elementsTransaction _txid)).''')
    statement(original, 'elements_transaction_txid_at',
              ': elements_field_at _elementsTransaction _txid 664.')
    definition(coq / 'C/jet_elements_hash_getter_local.v', 'hash_getter_rep', r'''
      exists be ebase bt tbase, env = Vptr be (Ptrofs.repr ebase) /\
        0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
        0 <= tbase /\ tbase + psz <= Ptrofs.max_unsigned /\
        Mem.load Mptr m be (ebase + pdelta) = Some (Vptr bt (Ptrofs.repr tbase)) /\
        uint32_array_at m bt (tbase + hdelta) (hash256_reg (hash_of e)) /\
        fp = [(be, ebase + pdelta, ebase + pdelta + 8); (bt, tbase + hdelta, tbase + hdelta + 32)]''')

    cpath = repo / 'C/elements/elementsJets.c'
    paths.append(cpath)
    c = re.sub(r'/\*.*?\*/|//[^\n]*', '', cpath.read_text(), flags=re.S)
    found = re.findall(r'\bbool\s+simplicity_transaction_id\s*\([^)]*\)\s*\{([^{}]*)\}', c, re.S)
    if len(found) != 1:
        raise ValueError('missing/ambiguous C transaction_id body')
    equal(found[0], '(void) src; write32s(dst, env->tx->txid.s, 8); return true;', 'complete C body')
    r['source_sha256'].update({str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in set(paths)})
    r.update(selected_jets=['Elements.TransactionId'], selected_primitive='Elements.TransactionId',
        canonical_serialization_source_review_complete=True, whole_contracts_reviewed=True,
        caller_environment_construction_proved=False, caller_cached_transaction_id_proved=False,
        formal_host_library_equivalence=False, normal_registration=False, kernel_checked_by_this_tool=False)
    return r


if __name__ == '__main__':
    print(json.dumps(check(Path(sys.argv[1]).resolve()), indent=2))
