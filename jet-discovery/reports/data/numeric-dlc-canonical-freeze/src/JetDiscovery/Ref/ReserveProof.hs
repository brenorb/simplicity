-- | BIP127 byte-oriented virtual-transaction reference. The UTXO view passed to
-- this client verifier must be authenticated against the chosen Bitcoin chain.
module JetDiscovery.Ref.ReserveProof(commitment,sighashAll,wireProof,signatures,verifySignatures) where
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx(sha256,hashToBytes,taggedSha256,putCompactSize)
import JetDiscovery.Ref.BitcoinGrowth(le32,le64)
import qualified JetDiscovery.Ref.Bip340 as R

commitment message=hashToBytes(sha256(C.pack "Proof-of-Reserves: "<>message))
outpoint(Outpoint txid index)=hashToBytes txid<>le32(toInteger index)
string bytes=runPut(putCompactSize(fromIntegral(B.length bytes)))<>bytes
script=BL.toStrict.sigTxiScript
sha=hashToBytes.sha256

-- Standard BIP341 ALL (0x01), all inputs/no annex, keypath spend, epoch0.
sighashAll tx index=hashToBytes(taggedSha256 "TapSighash" message)
 where
  inputs=V.toList(sigTxIn tx);outputs=V.toList(sigTxOut tx)
  message=B.pack[0,1]<>le32(toInteger(sigTxVersion tx))<>le32(toInteger(sigTxLock tx))
   <>sha(B.concat[outpoint(sigTxiPreviousOutpoint i)|i<-inputs])
   <>sha(B.concat[le64(toInteger(sigTxiValue i))|i<-inputs])
   <>sha(B.concat[string(script i)|i<-inputs])
   <>sha(B.concat[le32(toInteger(sigTxiSequence i))|i<-inputs])
   <>sha(B.concat[le64(toInteger(txoValue o))<>string(BL.toStrict(txoScript o))|o<-outputs])
   <>B.singleton 0<>le32(toInteger index)
signatures tx secret1 secret2=[R.sign secret1(sighashAll tx 1)(B.replicate 32 0),R.sign secret2(sighashAll tx 2)(B.replicate 32 0)]
verifySignatures tx key1 key2 signatures'=case signatures' of
 [a,b]->R.verify(R.bytesFromInt key1)(sighashAll tx 1)a&&R.verify(R.bytesFromInt key2)(sighashAll tx 2)b
 _->False

-- Canonical supported full proof transport, including the two actual 65-byte
-- keypath signatures with ALL flag and an empty phantom-input witness.
wireProof tx signatures'=case signatures' of
 [a,b]|B.length a==64&&B.length b==64&&V.length(sigTxIn tx)==3&&V.length(sigTxOut tx)==1
       &&all(BL.null.sigTxiScriptSig)(V.toList(sigTxIn tx))->le32(toInteger(sigTxVersion tx))<>B.pack[0,1,3]
   <>B.concat[outpoint(sigTxiPreviousOutpoint i)<>B.singleton 0<>le32(toInteger(sigTxiSequence i))|i<-V.toList(sigTxIn tx)]
   <>B.singleton 1<>B.concat[le64(toInteger(txoValue o))<>string(BL.toStrict(txoScript o))|o<-V.toList(sigTxOut tx)]
   <>B.singleton 0<>B.pack[1,65]<>a<>B.singleton 1<>B.pack[1,65]<>b<>B.singleton 1<>le32(toInteger(sigTxLock tx))
 _->error "BIP127 bounded transport expects two64-byte signatures"
