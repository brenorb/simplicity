-- | Independent byte/Integer BIP352 and BIP374 reference and test-only signing.
module JetDiscovery.Ref.SilentPayment
 ( compressed,decodeCompressed,evenSecret,inputHash,derive,prove374,verify374
 , p2pkhScript,p2pkhScriptSig,legacySighash,ecdsaDER70
 ) where
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Bits(xor,shiftR)
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes(SigTx(..),SigTxInput(..),putNoWitnessTx)
import JetDiscovery.Tx(sha256,hashToBytes,unhex)
import JetDiscovery.Corpus.Ripemd(ripemd160Ref)
import JetDiscovery.Ref.BitcoinGrowth(le32,sha256d)
import qualified JetDiscovery.Ref.Bip340 as R

compressed(Just(x,y))=B.singleton(if even y then 2 else 3)<>R.bytesFromInt x
compressed Nothing=error "compressed infinity"
decodeCompressed raw
 | B.length raw/=33||B.head raw `notElem`[2,3]=Nothing
 | otherwise=case R.liftX(R.intFromBytes(B.tail raw))of
    Just(x,y)->Just(x,if B.head raw==2 then y else R.p-y)
    _->Nothing
evenSecret d=case R.pointMul R.gPt d of Just p|R.hasEvenY p->d;_->R.n-d
validScalar x=x>0&&x<R.n
inputHash outpoints aggregate
 | null outpoints=error "BIP352 needs an eligible input"
 | not(validScalar result)=error "invalid BIP352 input hash scalar"
 | otherwise=result
 where result=R.intFromBytes(R.taggedHash "BIP0352/Inputs"(minimum outpoints<>compressed aggregate))

-- Exactly one P2TR input and one compressed P2PKH input; one recipient, k=0.
-- Outpoints are already in canonical 36-byte wire order, not display order.
derive a0 a1 outpoints scan spend=(R.xOnly output,compressed shared,inputHash outpoints aggregate)
 where
  a=(evenSecret a0+a1)`mod`R.n
  aggregate=R.pointMul R.gPt a
  h=inputHash outpoints aggregate
  shared=R.pointMul scan((h*a)`mod`R.n)
  tweak=R.intFromBytes(R.taggedHash "BIP0352/SharedSecret"(compressed shared<>le32 0))
  output=if validScalar tweak then R.pointAdd spend(R.pointMul R.gPt tweak) else error "invalid BIP352 output tweak"

challenge a b c r1 r2 message=R.intFromBytes(R.taggedHash "BIP0374/challenge"
 (B.concat(map compressed[a,b,c,R.gPt,r1,r2])<>message))`mod`R.n
prove374 secret base message
 | not(validScalar secret)||base==Nothing||B.length message/=32=error "invalid BIP374 prover input"
 | nonce==0=error "BIP374 nonce zero"
 | not(verify374 a base c(e,s)message)=error "generated BIP374 proof failed"
 | otherwise=(c,(e,s))
 where
  a=R.pointMul R.gPt secret;c=R.pointMul base secret
  aux=R.taggedHash "BIP0374/aux"(B.replicate 32 0)
  t=B.pack(B.zipWith xor(R.bytesFromInt secret)aux)
  nonce=R.intFromBytes(R.taggedHash "BIP0374/nonce"(t<>compressed a<>compressed c<>message))`mod`R.n
  r1=R.pointMul R.gPt nonce;r2=R.pointMul base nonce
  e=challenge a base c r1 r2 message;s=(nonce+e*secret)`mod`R.n
verify374 a b c(e,s)message=all(/=Nothing)[a,b,c]&&e>=0&&e<R.n&&s>=0&&s<R.n
 &&r1/=Nothing&&r2/=Nothing&&e==challenge a b c r1 r2 message
 where
  r1=R.pointAdd(R.pointMul R.gPt s)(R.pointMul a((R.n-e)`mod`R.n))
  r2=R.pointAdd(R.pointMul b s)(R.pointMul c((R.n-e)`mod`R.n))

p2pkhScript key=unhex "76a914"<>ripemd160Ref(hashToBytes(sha256(compressed key)))<>unhex "88ac"
p2pkhScriptSig der key
 | B.length der/=70=error "DER70 bound"
 | otherwise=B.singleton 71<>der<>unhex "0121"<>compressed key
legacySighash tx scriptCode=sha256d(runPut(putNoWitnessTx unsigned)<>le32 1)
 where unsigned=tx{sigTxIn=V.imap(\i input->input{sigTxiScriptSig=if i==1 then BL.fromStrict scriptCode else BL.empty})(sigTxIn tx)}
powm _ 0 _=1
powm a e m|even e=let h=powm a(e`div`2)m in h*h`mod`m
           |otherwise=a*powm a(e-1)m`mod`m
inverse x=powm x(R.n-2)R.n

-- Public deterministic nonces are ONLY for these non-production test vectors.
-- Generate a low-S canonical DER70 ECDSA signature for the actual legacy input.
ecdsaDER70 secret message=case[der|(der,True)<-map candidate[1..]]of der:_->der;_->error "DER70 search"
 where
  m=R.intFromBytes message`mod`R.n
  integer value=let raw=B.dropWhile(==0)(R.bytesFromInt value)
                    positive=if B.head raw>=128 then B.cons 0 raw else raw
                in B.pack[2,fromIntegral(B.length positive)]<>positive
  candidate k=let r=R.xOnly(R.pointMul R.gPt k)`mod`R.n
                  s0=inverse k*(m+r*secret)`mod`R.n;s=min s0(R.n-s0)
                  body=integer r<>integer s;der=B.pack[0x30,fromIntegral(B.length body)]<>body
                  check=R.pointAdd(R.pointMul R.gPt(m*inverse s`mod`R.n))
                    (R.pointMul(R.pointMul R.gPt secret)(r*inverse s`mod`R.n))
              in(der,r>0&&s>0&&B.length der==70&&check/=Nothing&&R.xOnly check`mod`R.n==r)
