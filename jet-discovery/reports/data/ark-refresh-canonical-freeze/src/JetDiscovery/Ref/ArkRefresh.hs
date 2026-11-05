-- | Test-only exact Bark hArk Taproot/template reference.
-- Bark revision5a7dbf9f2cd64dcdb65e3465080727e24dfe111d, MIT,
-- Copyright2026 The Bark Contributors; source retained as inert text.
module JetDiscovery.Ref.ArkRefresh
 (keyAgg,keyAggSecret,scriptNumber,delayedScript,timelockScript,hashSignScript
 ,tapLeaf,tapBranch,tapOutput,tapSecret,pubkeyPolicy,harkLeafPolicy,harkForfeitPolicy
 ,defaultMessage,wireTx,txidBytes) where
import qualified Data.ByteString as B
import qualified Data.List as L
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx(sha256,hashToBytes,putCompactSize,unhex)
import JetDiscovery.Ref.BitcoinGrowth(le32,le64,sha256d)
import qualified JetDiscovery.Ref.Bip340 as R
import JetDiscovery.Ref.SilentPayment(compressed,decodeCompressed)
import JetDiscovery.Corpus.Ripemd(ripemd160Ref)

coefficients keys=[if Just p==second then 1 else R.intFromBytes(R.taggedHash "KeyAgg coefficient"(ell<>p))`mod`R.n|p<-ordered]
 where
  ordered=L.sort keys;ell=R.taggedHash "KeyAgg list"(B.concat ordered)
  second=L.find(/=head ordered)ordered
keyAgg keys
 |null ordered||any((==Nothing).decodeCompressed)ordered=error "invalid Bark aggregate keys"
 |point==Nothing=error "infinite Bark aggregate key"
 |otherwise=point
 where
  ordered=L.sort keys
  point=foldl R.pointAdd Nothing(zipWith(\pk coefficient->R.pointMul(decodeCompressed pk)coefficient)ordered(coefficients ordered))
keyAggSecret secrets=sum(zipWith(*)ordered(coefficients(map(compressed.R.pointMul R.gPt)ordered)))`mod`R.n
 where ordered=L.sortOn(compressed.R.pointMul R.gPt)secrets
string b=runPut(putCompactSize(fromIntegral(B.length b)))<>b
scriptNumber value
 |value<0=error "negative script number"
 |value==0=B.singleton 0
 |value<=16=B.singleton(fromInteger(value+0x50))
 |otherwise=let bytes=B.pack(digits value)
                positive=if B.last bytes>=128 then B.snoc bytes 0 else bytes
            in B.singleton(fromIntegral(B.length positive))<>positive
 where digits 0=[];digits x=fromInteger(x`mod`256):digits(x`div`256)
delayedScript delay public=scriptNumber delay<>unhex "b27520"<>R.bytesFromInt public<>unhex "ac"
timelockScript height public=scriptNumber height<>unhex "b17520"<>R.bytesFromInt public<>unhex "ac"
hashSignScript hash public=unhex "82012088a914"<>ripemd160Ref hash<>unhex "8820"<>R.bytesFromInt public<>unhex "ac"
tapLeaf script=R.taggedHash "TapLeaf"(B.singleton 0xc0<>string script)
tapBranch a b=R.taggedHash "TapBranch"(min a b<>max a b)
rootOf []=B.empty
rootOf [a]=tapLeaf a
rootOf [a,b]=tapBranch(tapLeaf a)(tapLeaf b)
rootOf _=error "bounded Bark Taproot has at most two leaves"
tapOutput internal leaves
 |t>=R.n||point==Nothing=error "invalid Bark tap tweak"
 |otherwise=point
 where
  x=R.xOnly internal;t=R.intFromBytes(R.taggedHash "TapTweak"(R.bytesFromInt x<>rootOf leaves))
  point=R.pointAdd(R.liftX x)(R.pointMul R.gPt t)
tapSecret secret leaves
 |t>=R.n||result==0=error "invalid Bark private tap tweak"
 |otherwise=result
 where
  result=(evenSecret+t)`mod`R.n
  evenSecret=case R.pointMul R.gPt secret of Just p|R.hasEvenY p->secret;_->R.n-secret
  t=R.intFromBytes(R.taggedHash "TapTweak"(R.bytesFromInt(R.pubkeyOf secret)<>rootOf leaves))
pubkeyPolicy user server delay=tapOutput aggregate[delayedScript delay(R.xOnly user)]
 where aggregate=keyAgg(map compressed[user,server])
harkLeafPolicy user server expiry hash=tapOutput aggregate[timelockScript expiry(R.xOnly server),hashSignScript hash(R.xOnly aggregate)]
 where aggregate=keyAgg(map compressed[user,server])
harkForfeitPolicy user server delay hash=tapOutput aggregate[hashSignScript hash(R.xOnly server),delayedScript delay(R.xOnly user)]
 where aggregate=keyAgg(map compressed[user,server])

-- Exact BIP341 DEFAULT keypath, or scriptpath with no code separator/annex.
defaultMessage tx index scriptLeaf=R.taggedHash "TapSighash" message
 where
  inputs=V.toList(sigTxIn tx);outputs=V.toList(sigTxOut tx)
  outpoint i=let Outpoint h n=sigTxiPreviousOutpoint i in hashToBytes h<>le32(toInteger n)
  sha=hashToBytes.sha256
  ext=case scriptLeaf of Nothing->B.empty;Just h->h<>B.singleton 0<>le32 0xffffffff
  spendType=case scriptLeaf of Nothing->0;Just _->2
  message=B.pack[0,0]<>le32(toInteger(sigTxVersion tx))<>le32(toInteger(sigTxLock tx))
   <>sha(B.concat(map outpoint inputs))<>sha(B.concat[le64(toInteger(sigTxiValue i))|i<-inputs])
   <>sha(B.concat[string(BL.toStrict(sigTxiScript i))|i<-inputs])
   <>sha(B.concat[le32(toInteger(sigTxiSequence i))|i<-inputs])
   <>sha(B.concat[le64(toInteger(txoValue o))<>string(BL.toStrict(txoScript o))|o<-outputs])
   <>B.singleton spendType<>le32(toInteger index)<>ext
txidBytes=sha256d.runPut.putNoWitnessTx
wireTx tx stacks
 |length stacks/=V.length(sigTxIn tx)=error "Bark witness stack count"
 |otherwise=B.take 4 unsigned<>B.pack[0,1]<>B.take(B.length unsigned-8)(B.drop 4 unsigned)
  <>B.concat[runPut(putCompactSize(fromIntegral(length stack)))<>B.concat(map string stack)|stack<-stacks]
  <>B.drop(B.length unsigned-4)unsigned
 where unsigned=runPut(putNoWitnessTx tx)
