module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Data.Serialize(runPut)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.FFI.Jets as C
import Simplicity.Bitcoin.DataTypes
import Simplicity.Ty.Word(fromWord32)
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes(w32,w256ToBytes)
import qualified JetDiscovery.Ref.PaymentCode as P
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as K
import JetDiscovery.Ref.BitcoinGrowth(sha256d,le32)
import qualified JetDiscovery.Ref.HmacSha512 as H
import System.Exit(exitFailure)
assert name ok=do putStrLn(name++"="++show ok);unless ok exitFailure
main=do
 (parameters,accounts,payments,rows)<-P.fixture
 let field name=case[v|[k,v]<-rows,k==name]of[v]->unhex v;_->error name
     alice=unhex((accounts!!0)!!1);bob=unhex((accounts!!1)!!1)
     b0=R.intFromBytes(field "bob_b0");a0=R.intFromBytes(field "alice_a0");a0Public=K.decodeCompressed(field "alice_A0")
     zero=B.replicate 32 0
 assert "complete source accounts2/paymentcases10"(length accounts==2&&length payments==10)
 mapM_(\[name,payload,public,_,private]->assert("source "++name++" exact private/public account")(K.compressed(R.pointMul R.gPt(R.intFromBytes(unhex private)))==unhex public&&P.codeValid(unhex payload)))accounts
 assert "exact Alice child0 source public/private"(R.pointMul R.gPt a0==a0Public&&P.codeChild alice 0==a0Public)
 let pointA=R.pointMul(P.bobNotification parameters)(R.intFromBytes(field "designated_input_private"))
     pointB=R.pointMul(P.designatedPublic parameters)b0
     secret=R.bytesFromInt(R.xOnly pointB)
     key=P.outpointHashRaw parameters<>le32(P.outpointIndex parameters)
     mask=H.hmacSha512 key secret
 assert "actual designated input public/private and ECDH agree"(R.pointMul R.gPt(R.intFromBytes(field "designated_input_private"))==P.designatedPublic parameters&&pointA==pointB&&secret==field "ecdh_x")
 assert "exact published notification HMAC/unblinding/wire digest"(mask==field "mask"&&P.blind alice mask==field "blinded_payload"&&P.noticeAuthenticate parameters b0 alice&&P.noticeHash parameters==field "notification_txid_raw")
 parsed<-either fail return(parseRawTx(P.noticeRaw parameters))
 let notification=rawToSigTx parsed
     Just envNotice=mkEnv notification 0 defaultTap(hashFromInteger 1)
     expectedHash=P.outpointHashRaw parameters;expectedIndex=P.outpointIndex parameters
     wirePrimitive env op=case(C.input_prev_outpoint env(w32 0),Prim.primSem Prim.InputPrevOutpoint(w32 0)env,op)of
      (Just(Right(h,i)),Just(Right(hs,is)),Outpoint raw j)->w256ToBytes h==hashToBytes raw&&w256ToBytes hs==hashToBytes raw&&fromWord32 i==toInteger j&&fromWord32 is==toInteger j
      _->False
 assert "actual C/Haskell notification primitive is raw source outpoint"(wirePrimitive envNotice(sigTxiPreviousOutpoint(sigTxIn notification V.!0))&&hashToBytes(opHash(sigTxiPreviousOutpoint(sigTxIn notification V.!0)))==expectedHash&&toInteger(opIndex(sigTxiPreviousOutpoint(sigTxIn notification V.!0)))==expectedIndex)
 wires<-mapM(\row->case row of
  [index,private,public,shared,_,pubhash,_,_,derivedTweak]->do
   let i=read index;bi=R.intFromBytes(unhex private);biPublic=K.decodeCompressed(unhex public)
       point=R.pointMul a0Public bi;other=R.pointMul biPublic a0
       scalar=hashToBytes(sha256(R.bytesFromInt(R.xOnly point)))
       proof=P.ClientProof b0 alice(if i==0 then P.First else P.Later i bi)
       expected=unhex "76a914"<>unhex pubhash<>unhex "88ac"
       tx=P.paymentTx parameters proof 50000
       raw=runPut(putNoWitnessTx tx)
       Just env=mkEnv tx 0 defaultTap(hashFromInteger 1)
   putStrLn("source"++index++" ECDH-x="++hex(R.bytesFromInt(R.xOnly point))++" SHA256-x="++hex scalar++" publishedS="++shared)
   assert("source"++index++" full HD child/private and ECDH/raw-x/SHA256-tweak")(R.pointMul R.gPt bi==biPublic&&P.codeChild bob i==biPublic&&point==other&&R.bytesFromInt(R.xOnly point)==unhex shared&&scalar==unhex derivedTweak)
   assert("source"++index++" exact published payment-address script")(P.paymentScript parameters proof==expected)
   assert("source"++index++" actual standard legacy payment signature")(P.verifyLegacy0 tx)
   rebuilt<-either fail return(parseRawTx raw)
   assert("source"++index++" complete payment wire/C primitive boundary")(runPut(putNoWitnessTx(rawToSigTx rebuilt))==raw&&wirePrimitive env(sigTxiPreviousOutpoint(sigTxIn tx V.!0))&&case C.output_script_hash env(w32 0)of Just(Right h)->w256ToBytes h==hashToBytes(sha256 expected);_->False)
   return(index,hex raw)
  _->fail "BIP47 payment columns")payments
 writeFile "vendor-specs/bitcoin-growth8/bip47-derived-payment-wires.tsv"("index\traw_signed_payment\n"++concat[i++"\t"++raw++"\n"|(i,raw)<-wires])
