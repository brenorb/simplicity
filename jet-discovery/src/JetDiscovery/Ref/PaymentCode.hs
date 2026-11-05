-- | Complete bounded BIP47 v1 client model. Private keys remain local client
-- inputs. This module never executes the native expression for its HMAC/hash.
module JetDiscovery.Ref.PaymentCode where
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Bits(xor)
import Data.Serialize(runPut)
import Simplicity.Bitcoin.DataTypes
import JetDiscovery.Tx
import JetDiscovery.Ref.BitcoinGrowth(sha256d,le32)
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as K
import qualified JetDiscovery.Ref.NumericDlc as E
import qualified JetDiscovery.Ref.HmacSha512 as H

data Parameters=Parameters{noticeRaw::B.ByteString,noticePrefix::B.ByteString,noticeSuffix::B.ByteString
 ,noticeHash::B.ByteString,designatedPublic::R.Pt,outpointHashRaw::B.ByteString,outpointIndex::Integer
 ,bobCode::B.ByteString,bobNotification::R.Pt}
data Selected=First|Later Integer Integer deriving(Eq,Show)
data ClientProof=ClientProof{notificationPrivate::Integer,aliceCode::B.ByteString,selected::Selected}deriving(Eq,Show)
validScalar x=x>0&&x<R.n
codePublic code=K.decodeCompressed(B.take 33(B.drop 2 code))
codeValid code=B.length code==80&&B.take 2 code==unhex "0100"&&B.drop 67 code==B.replicate 13 0&&codePublic code/=Nothing
codeChain=B.take 32.B.drop 35
codeChild code index
 |not(codeValid code)||index<0||index>=2^31||il>=R.n=Nothing
 |otherwise=R.pointAdd(codePublic code)(R.pointMul R.gPt il)
 where digest=H.hmacSha512(codeChain code)(B.take 33(B.drop 2 code)<>B.drop 28(R.bytesFromInt index));il=R.intFromBytes(B.take 32 digest)
blind code mask= B.take 3 code<>B.pack(B.zipWith xor(B.take 64(B.drop 3 code))mask)<>B.drop 67 code
noticeAuthenticate parameters private code=validScalar private&&codeValid code
 &&R.pointMul R.gPt private==bobNotification parameters&&secret/=Nothing
 &&sha256d(noticePrefix parameters<>blind code mask<>noticeSuffix parameters)==noticeHash parameters
 where
  secret=R.pointMul(designatedPublic parameters)private
  x=R.bytesFromInt(R.xOnly secret)
  mask=H.hmacSha512(outpointHashRaw parameters<>le32(outpointIndex parameters))x
paymentKey proof=case selected proof of
 First->Just(0,notificationPrivate proof)
 Later i key|i>=1&&i<=9->Just(i,key)
            |otherwise->Nothing
paymentPoint parameters proof=do
 (index,private)<-paymentKey proof
 if not(validScalar private)||not(noticeAuthenticate parameters(notificationPrivate proof)(aliceCode proof))then Nothing else do
  expected<-codeChild(bobCode parameters)index
  if R.pointMul R.gPt private/=Just expected then Nothing else do
   sender<-codeChild(aliceCode proof)0
   secret<-R.pointMul(Just sender)private
   let scalar=R.intFromBytes(hashToBytes(sha256(R.bytesFromInt(fst secret))))
   if not(validScalar scalar)then Nothing else R.pointAdd(Just expected)(R.pointMul R.gPt scalar)
paymentScript parameters proof=K.p2pkhScript(paymentPoint parameters proof)
legacyAll0 tx script=sha256d(runPut(putNoWitnessTx tx{sigTxIn=V.imap(\i input->input{sigTxiScriptSig=if i==0 then BL.fromStrict script else BL.empty})(sigTxIn tx)})<>le32 1)
parseDerAll signature
 |B.length signature<9||B.last signature/=1=Nothing
 |B.head der/=0x30||fromIntegral(B.index der 1)/=B.length der-2=Nothing
 |otherwise=do
  (r,pos)<-integer 2
  (s,end)<-integer pos
  if end==B.length der&&validScalar r&&validScalar s&&s<=R.n`div`2 then Just(r,s)else Nothing
 where
  der=B.init signature
  integer position
   |position+2>B.length der||B.index der position/=2=Nothing
   |otherwise=let size=fromIntegral(B.index der(position+1));bytes=B.take size(B.drop(position+2)der)
              in if size==0||B.length bytes/=size||B.head bytes>=128||(size>1&&B.head bytes==0&&B.index bytes 1<128)
                 then Nothing else Just(R.intFromBytes bytes,position+2+size)
scriptSignature raw
 |B.null raw||B.head raw>75=Nothing
 |otherwise=let size=fromIntegral(B.head raw);signature=B.take size(B.tail raw);after=B.drop(1+size)raw
            in if B.length after/=34||B.head after/=33 then Nothing else do
             point<-K.decodeCompressed(B.tail after)
             values<-parseDerAll signature
             Just(Just point,values)
verifyLegacy0 tx=case scriptSignature(BL.toStrict(sigTxiScriptSig(sigTxIn tx V.!0)))of
 Just(public,sig)->K.p2pkhScript public==BL.toStrict(sigTxiScript(sigTxIn tx V.!0))&&E.ecdsaVerify public(legacyAll0 tx(K.p2pkhScript public))sig
 _->False
paymentTx parameters proof value=unsigned{sigTxIn=V.map(\input->input{sigTxiScriptSig=BL.fromStrict(K.p2pkhScriptSig signature fundingPublic)})(sigTxIn unsigned)}
 where
  fundingSecret=19;fundingPublic=R.pointMul R.gPt fundingSecret;fundingScript=K.p2pkhScript fundingPublic
  index=case paymentKey proof of Just(i,_)->i;_->0
  unsigned=mkTx 2[mkInput(dummyOutpoint(fromInteger index))51000(BL.fromStrict fundingScript)0xfffffffe]
   [mkOutput value(paymentScript parameters proof)]0
  signature=K.ecdsaDER70 fundingSecret(legacyAll0 unsigned fundingScript)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
fixture=do
 fixtureRows<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth8/bip47-notification-fixture.tsv"
 accounts<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth8/bip47-accounts.tsv"
 payments<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth8/bip47-all-payments.tsv"
 let field name=case[v|[k,v]<-fixtureRows,k==name]of[v]->unhex v;_->error name
     raw=field "notification_raw";bcode=unhex((accounts!!1)!!1)
 parsed<-either fail return(parseRawTx raw)
 let tx0=rawToSigTx parsed;[input]=V.toList(sigTxIn tx0)
     Just(designated,_)=scriptSignature(BL.toStrict(sigTxiScriptSig input))
     point=K.decodeCompressed(field "bob_B0")
     Outpoint h index=sigTxiPreviousOutpoint input
     parameters=Parameters raw(B.take(B.length raw-84)raw)(B.drop(B.length raw-4)raw)(sha256d raw)designated(hashToBytes h)(toInteger index)bcode point
     tx=tx0{sigTxIn=V.map(\i->i{sigTxiTxo=TxOutput 0(BL.fromStrict(K.p2pkhScript designated))})(sigTxIn tx0)}
 if codeChild bcode 0/=point||map roScript(rtOuts parsed)/=[K.p2pkhScript point,unhex "6a4c50"<>field "blinded_payload"]
    ||runPut(putNoWitnessTx tx)/=raw||not(verifyLegacy0 tx)||hashToBytes h<>le32(toInteger index)/=field "outpoint_raw"
 then error "BIP47 canonical source notification/point/signature mismatch"
 else return(parameters,accounts,payments,fixtureRows)
