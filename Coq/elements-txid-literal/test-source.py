"""Read-only transaction serialization and whole-C contract corruptions."""
import importlib.util
from pathlib import Path
import sys
from unittest.mock import patch

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sp = importlib.util.spec_from_file_location('txid_source_negative', HERE / 'check-source.py')
g = importlib.util.module_from_spec(sp)
sp.loader.exec_module(g)
repo = Path(sys.argv[1]).resolve()
coq = repo / 'Coq'
data = repo / 'Haskell/Elements/Simplicity/Elements/DataTypes.hs'
hs = repo / 'Haskell/Elements/Simplicity/Elements/Primitive.hs'
catalog = repo / 'Haskell/Simplicity/Elements/Jets.hs'
digest = repo / 'Haskell/Core/Simplicity/Digest.hs'
words = repo / 'Haskell/Core/Simplicity/Word.hs'
port = coq / 'C/jet_elements_prim.v'
local = coq / 'C/jet_elements_transaction_id_literal.v'
old = coq / 'C/jet_elements_hash_field_jets.v'
rep = coq / 'C/jet_elements_hash_getter_local.v'
c = repo / 'C/elements/elementsJets.c'
fixtures = [
    (catalog, 'specificationTransaction TransactionId = primitive Prim.TransactionId',
              'specificationTransaction TransactionId = primitive Prim.ScriptCMR'),
    (hs, 'interpret TransactionId = element . return . encodeHash . txid $ tx',
         'interpret TransactionId = element . return . encodeHash . tapleafHash $ envTap env'),
    (data, 'putWord32le $ sigTxVersion tx', 'putWord32be $ sigTxVersion tx'),
    (data, 'putWord32le $ sigTxLock tx', 'putWord32be $ sigTxLock tx'),
    (data, 'putWord8 0\n  putVarInt (V.length (sigTxIn tx))', 'putWord8 1\n  putVarInt (V.length (sigTxIn tx))'),
    (data, 'putVarInt (V.length (sigTxIn tx))', 'putVarInt (V.length (sigTxOut tx))'),
    (data, 'mapM_ putOutput (sigTxOut tx)', 'mapM_ putOutput (V.reverse (sigTxOut tx))'),
    (data, 'x <= 0xFC', 'x < 0xFC'),
    (data, 'putWord8 0xFD >> putWord16le', 'putWord8 0xFD >> putWord16be'),
    (data, 'putWord8 0xFE >> putWord32le', 'putWord8 0xFF >> putWord32le'),
    (data, 'x <= 0xFFFFFFFFFFFFFFFF', 'x < 0xFFFFFFFFFFFFFFFF'),
    (data, 'putWord32le (flags .|. opIndex', 'putWord32le (flags .&. opIndex'),
    (data, '= 0x80000000', '= 0x40000000'),
    (data, '= 0x40000000', '= 0x20000000'),
    (data, 'putLazyByteString (sigTxiScriptSig txi)', 'put (bslHash (sigTxiScriptSig txi))'),
    (data, 'put (0 :: Word256)', 'put (1 :: Word256)'),
    (data, 'putIssuanceAmount (Amount (Explicit 0)) = putWord8 0',
           'putIssuanceAmount (Amount (Explicit 0)) = putAmount (Amount (Explicit 0))'),
    (data, 'putIssuanceAmount (clearAmountPrf (reissuanceAmount re))\n      putWord8 0',
           'putIssuanceAmount (clearAmountPrf (reissuanceAmount re))\n      putWord8 1'),
    (data, 'putAsset (clearAssetPrf (txoAsset txo))', 'putAsset (txoAsset txo)'),
    (data, 'putNonce (txoNonce txo)\n    putVarInt', 'putNonce Nothing\n    putVarInt'),
    (data, 'putWord64be v', 'putWord64le v'),
    (data, 'if by then 0x09 else 0x08', 'if by then 0x08 else 0x09'),
    (data, 'if by then 0x03 else 0x02', 'if by then 0x02 else 0x03'),
    (data, 'txid = bslDoubleHash . runPutLazy . putNoWitnessTx', 'txid = bslHash . runPutLazy . putNoWitnessTx'),
    (digest, 'bslDoubleHash = bsHash . encode . bslHash', 'bslDoubleHash = bsHash . encode'),
    (digest, 'put (Hash256 bs) = putShortByteString bs', 'put (Hash256 bs) = putShortByteString (BSS.reverse bs)'),
    (words, 'put (Word256 a3 a2 a1 a0) = put a3 >> put a2 >> put a1 >> put a0',
            'put (Word256 a3 a2 a1 a0) = put a0 >> put a1 >> put a2 >> put a3'),
    (port, 'if Z.leb x 252 then', 'if Z.ltb x 252 then'),
    (port, 'z / two_power_nat (i * Byte.wordsize)', 'z / two_power_nat (i * Byte.wordsize + 8)'),
    (port, 'rev (putLE n z)', 'putLE n z'),
    (port, 'putWord8 253 ++ putLE 2 x', 'putWord8 253 ++ putLE 4 x'),
    (port, 'putWord8 255 ++ putLE 8 x', 'putWord8 255 ++ putBE 8 x'),
    (port, 'then 2147483648 else 0', 'then 1073741824 else 0'),
    (port, 'then 1073741824 else 0', 'then 536870912 else 0'),
    (port, 'Z.lor issuanceFlag peginFlag', 'Z.land issuanceFlag peginFlag'),
    (port, 'repeat Byte.zero 32', 'repeat Byte.zero 31'),
    (port, 'if Int64.eq v Int64.zero then putWord8 0', 'if Int64.eq v Int64.zero then putWord8 1'),
    (port, 'clearPrf (newIssuanceTokenAmount new)', 'clearPrf (newIssuanceAmount new)'),
    (port, 'clearPrf (reissuanceAmount re)) ++ putWord8 0', 'clearPrf (reissuanceAmount re)) ++ putWord8 1'),
    (port, 'concat (map putTxOutput (sigTxOut tx))', 'concat (map putTxOutput (rev (sigTxOut tx)))'),
    (port, 'byteStringHash (hash256_to_bytelist (byteStringHash x))', 'byteStringHash x'),
    (port, 'byteStringDoubleHash (putNoWitnessTx tx)', 'byteStringHash (putNoWitnessTx tx)'),
    (port, '0 < Zlength sigTxIn < Int.modulus', '0 < Zlength sigTxIn < 65536'),
    (port, 'txoScript_bound : Zlength txoScript < Int.modulus', 'txoScript_bound : Zlength txoScript < 65536'),
    (local, 'elements_hash_literal_spec (fun e => txid (Elements.envTx e))',
            'elements_hash_literal_spec (fun e => tapScriptCMR (Elements.envTap e))'),
    (rep, 'uint32_array_at m bt (tbase + hdelta) (hash256_reg (hash_of e))',
          'True'),
    (c, 'write32s(dst, env->tx->txid.s, 8);', 'write32s(dst, env->taproot->scriptCMR.s, 8);'),
]
for path, name in [(local, 'elements_transaction_id_literal_local_spec'),
                   (old, 'elements_transaction_id_local_spec')]:
    text = path.read_text()
    start = text.index('Theorem ' + name)
    stop = text.index('Proof.', start)
    statement = text[start:stop]
    for a, b in [('application_jet_local_spec_sep', 'False -> application_jet_local_spec_sep'),
                 ('application_jet_local_spec_sep', 'application_jet_local_spec'),
                 ('f_simplicity_transaction_id', 'f_simplicity_script_cmr'),
                 ('elements_ge Elements.env', 'ge0 Elements.env'),
                 ('elements_ge Elements.env', 'elements_ge Bitcoin.env'),
                 ('Ty.Unit Word256', 'Word32 Word256'),
                 ('0 664 760', '0 632 760'),
                 ('hash_getter_rep (fun e => txid (Elements.envTx e))', '(fun _ _ _ _ => True)')]:
        assert a in statement, (name, a)
        fixtures.append((path, statement, statement.replace(a, b, 1)))
original = Path.read_text
g.check(repo)
for path, a, b in fixtures:
    text = original(path)
    # Several serializer expressions also occur in unrelated sighash helpers.
    # Mutate the selected no-witness block, not its first textual look-alike.
    if path == data:
        start = text.index('putNoWitnessTx :: Putter SigTx')
        stop = text.index('txid :: SigTx -> Hash256', start)
        block = text[start:stop]
        if a in block:
            a, b = block, block.replace(a, b, 1)
    assert a in text, ('inactive txid fixture', path, a)
    altered = text.replace(a, b, 1)
    assert altered != text
    def read(self, *args, **kw):
        return altered if self == path else original(self, *args, **kw)
    with patch.object(Path, 'read_text', read):
        try:
            g.check(repo)
        except ValueError:
            pass
        else:
            raise AssertionError('accepted transaction_id source corruption: ' + a)
g.check(repo)
print(str(len(fixtures)) + ' transaction serialization/cached-value/whole-C corruptions rejected')
