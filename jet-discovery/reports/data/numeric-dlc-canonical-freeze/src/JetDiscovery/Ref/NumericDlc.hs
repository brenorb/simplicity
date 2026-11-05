-- | Test-only byte/Integer numeric DLC oracle and ECDSA adaptor reference.
-- Algorithms: dlcspecs revision9cd9148938c616690c79d99ec6f330e213c246c5,
-- ECDSA-adaptor.md, Oracle.md and NumericOutcomeCompression.md, CC-BY4.0.
-- Public deterministic nonces below are fixtures, never production signing.
module JetDiscovery.Ref.NumericDlc
 (Adaptor(..),parseAdaptor,serializeAdaptor,encrypt,verifyAdaptor,decrypt,recover
 ,oracleMessage,oracleAttest,oraclePoint,compressed,decodeCompressed,inverse,ecdsaVerify
 ,cetSighash,derSignature,wireCet) where
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Ref.BitcoinGrowth(le32,le64,sha256d)
import JetDiscovery.Tx(putCompactSize,hashToBytes)
import qualified JetDiscovery.Ref.Bip340 as R
import JetDiscovery.Ref.SilentPayment(compressed,decodeCompressed)

data Adaptor=Adaptor {encryptedR::R.Pt,nonceR::R.Pt,encryptedS::Integer,proofE::Integer,proofS::Integer} deriving Show
powm _ 0 _=1
powm a e m|even e=let x=powm a(e`div`2)m in x*x`mod`m
           |otherwise=a*powm a(e-1)m`mod`m
inverse a=powm a(R.n-2)R.n
canonical a=a>=0&&a<R.n
nonzero a=a>0&&a<R.n
validPoint Nothing=False
validPoint(Just(x,y))=x>=0&&x<R.p&&y>=0&&y<R.p&&(y*y-x*x*x-7)`mod`R.p==0
neg= fmap(\(x,y)->(x,(R.p-y)`mod`R.p))
challenge x y z ag ay=R.intFromBytes(R.taggedHash "DLEQ"(B.concat(map compressed[x,y,z,ag,ay])))`mod`R.n
serializeAdaptor(Adaptor r ra sa e s)=compressed r<>compressed ra<>B.concat(map R.bytesFromInt[sa,e,s])
parseAdaptor raw
 |B.length raw/=162=Nothing
 |r==Nothing||ra==Nothing||not(nonzero sa&&canonical e&&canonical s)=Nothing
 |otherwise=Just(Adaptor r ra sa e s)
 where
  r=decodeCompressed(B.take 33 raw);ra=decodeCompressed(B.take 33(B.drop 33 raw))
  scalar offset=R.intFromBytes(B.take 32(B.drop offset raw))
  sa=scalar 66;e=scalar 98;s=scalar 130
encrypt secret y message nonce proofNonce
 |not(all nonzero[secret,nonce,proofNonce])||y==Nothing||B.length message/=32=error "DLC fixture inputs"
 |not(nonzero sa)||R.xOnly r`mod`R.n==0=error "DLC fixture degenerate signature"
 |not(verifyAdaptor(R.pointMul R.gPt secret)y message result)=error "DLC fixture adaptor verification"
 |otherwise=result
 where
  ra=R.pointMul R.gPt nonce;r=R.pointMul y nonce
  sa=inverse nonce*(R.intFromBytes message+(R.xOnly r`mod`R.n)*secret)`mod`R.n
  e=challenge ra y r(R.pointMul R.gPt proofNonce)(R.pointMul y proofNonce)
  s=(proofNonce+e*nonce)`mod`R.n;result=Adaptor r ra sa e s
verifyAdaptor x y message(Adaptor r ra sa e s)=all validPoint[x,y,r,ra]
 &&B.length message==32&&nonzero sa&&canonical e&&canonical s&&ag/=Nothing&&ay/=Nothing
 &&e==challenge ra y r ag ay&&check==ra
 where
  ag=R.pointAdd(R.pointMul R.gPt s)(neg(R.pointMul ra e))
  ay=R.pointAdd(R.pointMul y s)(neg(R.pointMul r e))
  si=inverse sa;m=R.intFromBytes message`mod`R.n;rr=R.xOnly r`mod`R.n
  check=R.pointAdd(R.pointMul R.gPt(m*si`mod`R.n))(R.pointMul x(rr*si`mod`R.n))
decrypt(Adaptor r _ sa _ _) y
 |not(nonzero y)=error "DLC fixture decryption key"
 |otherwise=(R.xOnly r`mod`R.n,min s(R.n-s))
 where s=sa*inverse y`mod`R.n
recover y(Adaptor r _ sa _ _)(rr,s)
 |r==Nothing||rr/=R.xOnly r`mod`R.n||not(nonzero s)=Nothing
 |candidatePoint==y=Just candidate
 |neg candidatePoint==y=Just((R.n-candidate)`mod`R.n)
 |otherwise=Nothing
 where candidate=inverse s*sa`mod`R.n;candidatePoint=R.pointMul R.gPt candidate
ecdsaVerify x message(r,s)=validPoint x&&nonzero r&&nonzero s&&point/=Nothing&&R.xOnly point`mod`R.n==r
 where si=inverse s;point=R.pointAdd(R.pointMul R.gPt(R.intFromBytes message*si`mod`R.n))(R.pointMul x(r*si`mod`R.n))

-- Exact BIP143 ALL01, one P2WSH funding input and no OP_CODESEPARATOR.
cetSighash witnessScript tx
 |V.length(sigTxIn tx)/=1=error "DLC one-input BIP143 bound"
 |otherwise=sha256d(le32(toInteger(sigTxVersion tx))<>sha256d(outpoint input)
   <>sha256d(le32(toInteger(sigTxiSequence input)))<>outpoint input<>string witnessScript
   <>le64(toInteger(sigTxiValue input))<>le32(toInteger(sigTxiSequence input))
   <>sha256d(B.concat[le64(toInteger(txoValue o))<>string(BL.toStrict(txoScript o))|o<-V.toList(sigTxOut tx)])
   <>le32(toInteger(sigTxLock tx))<>le32 1)
 where
  input=sigTxIn tx V.!0
  outpoint i=let Outpoint txid index=sigTxiPreviousOutpoint i
             in hashToBytes txid<>le32(toInteger index)
  string b=runPut(putCompactSize(fromIntegral(B.length b)))<>b
derSignature(r,s)
 |not(nonzero r&&nonzero s)||s>R.n`div`2=error "DLC DER expects canonical low-S signature"
 |otherwise=B.pack[0x30,fromIntegral(B.length body)]<>body<>B.singleton 1
 where
  integer a=let bytes=B.dropWhile(==0)(R.bytesFromInt a)
                positive=if B.head bytes>=128 then B.cons 0 bytes else bytes
            in B.pack[2,fromIntegral(B.length positive)]<>positive
  body=integer r<>integer s
wireCet witnessScript tx signatures
 |V.length(sigTxIn tx)/=1||V.length(sigTxOut tx)/=2||length signatures/=2=error "DLC complete CET wire bound"
 |not(BL.null(sigTxiScriptSig(sigTxIn tx V.!0)))=error "DLC CET empty scriptSig bound"
 |otherwise=B.take 4 unsigned<>B.pack[0,1]<>B.take(B.length unsigned-8)(B.drop 4 unsigned)
    <>B.pack[4,0]<>B.concat(map string(map derSignature signatures++[witnessScript]))<>B.drop(B.length unsigned-4)unsigned
 where
  unsigned=runPut(putNoWitnessTx tx)
  string b=runPut(putCompactSize(fromIntegral(B.length b)))<>b

oracleMessage digit
 |digit<0||digit>9=error "DLC decimal digit"
 |otherwise=R.taggedHash "DLC/oracle/attestation/v0"(C.pack(show digit))
oraclePoint public noncePoint digit=R.pointAdd noncePoint(R.pointMul public challenge')
 where challenge'=R.intFromBytes(R.taggedHash "BIP0340/challenge"
          (R.bytesFromInt(R.xOnly noncePoint)<>R.bytesFromInt(R.xOnly public)<>oracleMessage digit))`mod`R.n
oracleAttest secret nonce digit
 |not(nonzero secret&&nonzero nonce)=error "DLC oracle fixture scalar"
 |not(R.verify(R.bytesFromInt(R.xOnly public))(oracleMessage digit)signature)=error "DLC oracle fixture verify"
 |otherwise=(noncePoint,s)
 where
  public=R.liftX(R.pubkeyOf secret)
  secret'=case R.pointMul R.gPt secret of Just p|R.hasEvenY p->secret;_->R.n-secret
  noncePoint=R.liftX(R.pubkeyOf nonce)
  nonce'=case R.pointMul R.gPt nonce of Just p|R.hasEvenY p->nonce;_->R.n-nonce
  e=R.intFromBytes(R.taggedHash "BIP0340/challenge"
      (R.bytesFromInt(R.xOnly noncePoint)<>R.bytesFromInt(R.xOnly public)<>oracleMessage digit))`mod`R.n
  s=(nonce'+e*secret')`mod`R.n
  signature=R.bytesFromInt(R.xOnly noncePoint)<>R.bytesFromInt s
