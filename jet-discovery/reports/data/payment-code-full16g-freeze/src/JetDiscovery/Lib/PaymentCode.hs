{-# LANGUAGE ScopedTypeVariables,RankNTypes #-}
-- | BIP47 v1 private-client notification recovery and incoming-payment match.
-- Secrets are private local-client inputs, never an onchain witness proposal.
module JetDiscovery.Lib.PaymentCode
 (entry,Proof,Code,Selection,clientKernel,publicChild,proofW)where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes(SigTx(..),SigTxInput(..))
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.TaprootTx1 as T
import qualified JetDiscovery.Lib.Ripemd160 as RI
import qualified JetDiscovery.Lib.HmacSha512 as H
import qualified JetDiscovery.Ref.PaymentCode as Ref
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SilentPayment as K
import JetDiscovery.Types
import JetDiscovery.Tx

type GE=(Word256,Word256)
type CKey=(Word8,Word256)
type Code=(CKey,Word256)
-- Index0 uses the SAME notification private-key value. Other indices have a
-- distinct private-key field and must be1..9; there is no duplicate index0 key.
type Selection=Either()(Word8,Word256)
type Proof=(Word256,(Code,Selection))
type Payment=(Word8,(Word256,Code))
same :: (Assert t,TyC x,TyC y) => t x y -> t x y -> t x()
same a b=(a&&&b)>>>eq>>>verify
scalar :: Assert t => t Word256()
scalar=(((konst(w256 0)&&&iden)>>>A.lt word256>>>verify)&&&((iden&&&konst(w256 R.n))>>>A.lt word256>>>verify))>>>unit
normalize :: Assert t => t(GE,Word256)GE
normalize=S.gej_normalize>>>verify
generate :: Assert t => t Word256 GE
generate=(iden&&&konst(pointW R.gPt,w256 1))>>>S.scale>>>normalize
decompress :: Assert t => t CKey GE
decompress=(((check&&&iden)>>>ih)>>>(((oh&&&konst(w8 3))>>>eq)&&&ih)>>>S.decompress>>>verify)
 where
  check=(((or((oh&&&konst(w8 2))>>>eq)((oh&&&konst(w8 3))>>>eq))>>>verify)
    &&&((ih&&&konst(w256 R.p))>>>A.lt word256>>>verify))>>>unit
sha32 :: Assert t => t Word256 Word256
sha32=((unit>>>ctx8Init)&&&iden)>>>ctx8Add32>>>ctx8Finalize
-- One explicitly shared HMAC frontend and CKD term can serve both Bob and
-- Alice. It remains an ordinary witness-free expression, not a global DAG CAF.
publicChild :: forall t. Assert t => t H.HmacInput Word512 -> t(Code,Word32)(GE,Word256)
publicChild hmac=(((indexCheck&&&iden)>>>ih)>>>parentDigest)>>>((ilCheck&&&iden)>>>ih)>>>(child&&&(ih>>>ih))
 where
  indexCheck :: t(Code,Word32)()
  indexCheck=(ih&&&konst(w32(2^31)))>>>A.lt word32>>>verify
  parentDigest :: t(Code,Word32)(GE,Word512)
  parentDigest=(ooh>>>decompress)&&&((oih&&&((ooh>>>oh)&&&((ooh>>>ih)&&&ih)))>>>hmac)
  ilCheck :: t(GE,Word512)()
  ilCheck=(ioh&&&konst(w256 R.n))>>>A.lt word256>>>verify
  child :: t(GE,Word512)GE
  child=(((konst(w256 1)&&&(oh&&&konst(w256 1)))&&&ioh)>>>S.linear_combination_1>>>normalize)
choosePayment :: Assert t => t Proof(Word8,Word256)
choosePayment=(iih&&&oh)>>>match(konst(w8 0)&&&ih)other
 where
  other=((((konst(w8 1)&&&ooh)>>>A.le word8>>>verify)
     &&&((ooh&&&konst(w8 9))>>>A.le word8>>>verify))&&&oh)>>>ih
blindCode :: Assert t => t(Code,Word512)(Word8,(Word256,Word256))
blindCode=(oh>>>oh>>>oh)&&&((((oh>>>oh>>>ih)&&&(ih>>>oh))>>>W.bitwise_xor word256)
 &&&(((oh>>>ih)&&&(ih>>>ih))>>>W.bitwise_xor word256))
noticeWireHash :: Assert t => Ref.Parameters -> t(Word8,(Word256,Word256))Word256
noticeWireHash parameters=(iden&&&(unit>>>ctx8Init>>>T.appendConst(Ref.noticePrefix parameters<>unhex "0100")))
 >>>T.append oh ctx8Add1>>>T.append ioh ctx8Add32>>>T.append iih ctx8Add32
 >>>T.constant(B.replicate 13 0<>Ref.noticeSuffix parameters)>>>ih>>>ctx8Finalize>>>sha32
noticePhase :: forall t. Assert t => t(H.Key36,Word256)Word512 -> Ref.Parameters -> t Proof Payment
noticePhase hmac parameters=(((privateCheck&&&authenticated)&&&result)>>>ih)
 where
  privateCheck :: t Proof()
  privateCheck=((oh>>>scalar)&&&same(oh>>>generate)(konst(pointW(Ref.bobNotification parameters))))>>>unit
  secretX :: t Proof Word256
  secretX=(oh&&&konst(pointW(Ref.designatedPublic parameters),w256 1))>>>S.scale>>>normalize>>>oh
  mask :: t Proof Word512
  mask=(((konst(w256FromBytes(Ref.outpointHashRaw parameters))&&&(konst(w32(Ref.outpointIndex parameters))>>>bswap32)))&&&secretX)>>>hmac
  authenticated :: t Proof()
  authenticated=same(((ioh&&&mask)>>>blindCode)>>>noticeWireHash parameters)(konst(w256FromBytes(Ref.noticeHash parameters)))
  result :: t Proof Payment
  result=(choosePayment&&&ioh)>>>(ooh&&&(oih&&&ih))
bobPhase :: forall t. Assert t => t(Code,Word32)GE -> Code -> t Payment(Word256,Code)
bobPhase derive bob=(((ioh>>>scalar)&&&same(ioh>>>generate)expected)&&&(ih))>>>ih
 where
  expected :: t Payment GE
  expected=(konst bob&&&(konst(w16 0)&&&(konst(w8 0)&&&oh)))>>>derive
alicePhase :: Assert t => t(Code,Word32)GE -> t(Word256,Code)(Word256,GE)
alicePhase derive=oh&&&((ih&&&konst(w32 0))>>>derive)
paymentPoint :: forall t. Assert t => t(Word256,GE)GE
paymentPoint=pair>>>(((ih>>>scalar)&&&iden)>>>ih)
 >>>(((konst(w256 1)&&&(oh&&&konst(w256 1)))&&&ih)>>>S.linear_combination_1>>>normalize)
 where
  pair :: t(Word256,GE)(GE,Word256)
  pair=(oh>>>generate)&&&(((oh&&&(ih&&&konst(w256 1)))>>>S.scale>>>normalize>>>oh)>>>sha32)
prefix :: Assert t => t GE Word8
prefix=((ih>>>S.fe_is_odd)&&&unit)>>>cond(konst(w8 3))(konst(w8 2))
hash160Point :: forall t. Assert t => t GE RI.W5
hash160Point=pubHash>>>((RI.ivT&&&block)>>>RI.ripemd160Compress)
 where
  pubHash :: t GE Word256
  pubHash=(iden&&&(unit>>>ctx8Init))>>>T.append prefix ctx8Add1>>>T.append oh ctx8Add32>>>ih>>>ctx8Finalize
  word :: Int -> t Word256 Word32
  word i=RI.pick(i>=4)(RI.pick(odd(i`div`2))(RI.pick(odd i)iden))>>>bswap32
  block :: t Word256(Vector16 Word32)
  block=RI.mk16([word i|i<-[0..7]]++[konst(w32 0x80)]++P.replicate 5(konst(w32 0))++[konst(w32 256),konst(w32 0)])
p2pkhScriptHash :: Assert t => t GE Word256
p2pkhScriptHash=hash160Point>>>(iden&&&(unit>>>ctx8Init>>>T.appendConst(unhex "76a914")))
 >>>T.append oh ctxAddLE32>>>T.append ioh ctxAddLE32>>>T.append iioh ctxAddLE32
 >>>T.append(ih>>>ih>>>ih>>>oh)ctxAddLE32>>>T.append(ih>>>ih>>>ih>>>ih)ctxAddLE32
 >>>T.constant(unhex "88ac")>>>ih>>>ctx8Finalize
clientKernel :: forall t. (Simplicity t,Primitive t) => Ref.Parameters -> t Proof()
clientKernel parameters=noticePhase h36 parameters>>>bobPhase derive(codeW(Ref.bobCode parameters))>>>alicePhase derive
 >>>paymentPoint>>>p2pkhScriptHash>>>actualPayment
 where
  h36 :: t(H.Key36,Word256)Word512
  h36=H.hmac36x32
  h37 :: t H.HmacInput Word512
  h37=H.hmac37
  derive :: t(Code,Word32)GE
  derive=publicChild h37>>>oh
  actualPayment :: t Word256()
  actualPayment=(same iden(konst(w32 0)>>>primitive Prim.OutputScriptHash>>>verify)
   &&&same(konst(w32 0)>>>primitive Prim.OutputValue>>>verify)(konst(w64 50000))
   &&&same(unit>>>Tx.numOutputs)(konst(w32 1))&&&same(unit>>>Tx.numInputs)(konst(w32 1))
   &&&same(unit>>>primitive Prim.CurrentIndex)(konst(w32 0)))>>>unit
pointW(Just(x,y))=(w256 x,w256 y)
pointW Nothing=error "invalid fixed BIP47 point"
codeW :: B.ByteString -> Code
codeW code
 | B.length code/=80||B.take 2 code/=unhex "0100"||B.drop 67 code/=B.replicate 13 0=error "BIP47 code outside canonical v1/features0/reserved0 binary schema"
 | otherwise=((w8(toInteger(B.index code 2)),w256FromBytes(B.take 32(B.drop 3 code))),w256FromBytes(B.take 32(B.drop 35 code)))
proofW :: Ref.ClientProof -> Proof
proofW proof=(scalarWord(Ref.notificationPrivate proof),(codeW(Ref.aliceCode proof),case Ref.selected proof of
 Ref.First->Left()
 Ref.Later i private
  | i<0||i>=256->error "BIP47 selection index not representable by Word8"
  | otherwise->Right(w8 i,scalarWord private)))
 where
  scalarWord value
   | value<0||value>=2^256=error "BIP47 private input not representable by Word256"
   | otherwise=w256 value
resign tx=tx{sigTxIn=V.map(\input->input{sigTxiScriptSig=BL.fromStrict(K.p2pkhScriptSig signature public)})(sigTxIn tx)}
 where public=R.pointMul R.gPt 19;signature=K.ecdsaDER70 19(Ref.legacyAll0 tx(K.p2pkhScript public))
entry :: IO Entry
entry=do
 (parameters,accounts,payments,_)<-Ref.fixture
 let code=unhex((accounts!!0)!!1);b0=R.intFromBytes(unhex((payments!!0)!!1))
     make row=let i=read(row!!0);private=R.intFromBytes(unhex(row!!1))in Ref.ClientProof b0 code(if i==0 then Ref.First else Ref.Later i private)
     proofs=map make payments
     env proof value=mkEnv(Ref.paymentTx parameters proof value)0 defaultTap
     vector name environment proof expected=Vector name environment(proofW proof)expected
     first=proofs!!0;second=proofs!!1
     wrongCode=case R.pointMul R.gPt 31 of Just p->B.take 2 code<>K.compressed(Just p)<>B.drop 35 code;_->error "code"
     wrongChain=B.take 35 code<>B.singleton(B.index code 35+1)<>B.drop 36 code
     wrongPayTx=let tx=Ref.paymentTx parameters first 50000
               in resign(tx{sigTxOut=V.singleton(mkOutput 50000(K.p2pkhScript(R.pointMul R.gPt 29)))})
 return(Entry "app-bip47-notification-payment-client"
  "BIP47 v1 private client: full notification recovery, both public-HD derivations and actual incoming P2PKH payment match"
  "BIP47 pinned a0c977f3755da6476b955677ca9318334a2432c4; full linked SamouraiDev gist beddb67cf219ead27b8b1380a3b084b8dde51093; deployed HMAC order independently pinned Drongo/Dojo"
  BitcoinApp(Derived "All10 published address/ECDH cases, exact complete signed notification; actual standard signed payment fixtures derive each source P2PKH address; independent byte/Word64 HMAC reference and real C primitive boundary checks")
  ["PRIVATE CLIENT MODE: production receiver private keys are local interpreter inputs and must remain offchain; this is not a proposed public Bitcoin witness/covenant or outsourced zero-knowledge proof",
   "Authenticated client supplies the actual prior notification txid/bytes and current incoming-payment Bitcoin primitive view; chain/UTXO/finality/normal transaction validity and human sender identity are external client boundaries",
   "Exact v1/features0/noBitmessage binary payment code, one canonical P2PKH designated input and two-output complete published notification; source input amount/chain confirmation are not assumed proven",
   "Both notification mask and reconstructed complete signed notification hash use the same actual private0/code fields; HMAC key is raw36-byte serialized outpoint, data is ECDH-x32, matching full vectors and both primary implementations despite contradictory receiver prose",
   "Index0 reuses the single actual notification private-key field; indices1..9 supply one distinct child private key checked against Bob's actual HMAC-SHA512 CKDpub; no duplicate index0 private reopening",
   "Recovered Alice public code is curve/canonical checked and derives child0 with full HMAC-SHA512; actual ECDH with Bob's checked private child yields nonzero canonical SHA256 scalar and exact compressed P2PKH recipient",
   "One actual one-input/one-output payment must pay exactly50000sats to that computed script; amount is authenticated client request, not a protocol-wide amount rule; native environment is a client view, not a Simplicity spend of the P2PKH funding input",
   "All10 source addresses/private-public children/shared ECDH-x cases are exercised; gist uppercase S_i denotes raw ECDH-x, not the SHA256 payment tweak; setup mnemonic/seed/account decoding remains external",
   "Master/identity setup and Base58Check transport decoding are external; the prior notification binary prefix/suffix and designated input/outpoint are authenticated program constants extracted from the complete actual source transaction",
   "One structured witness with projection-based reuse; explicitly shared witness-free HMAC37/CKD frontend used twice, with no whole-application/global compiled-DAG cache; one group regardless of index/role/parameter"]
  (boundProgram(clientKernel parameters))
  ([vector("full published index"++show i++" notification/payment match")(env proof 50000)proof Accept|(i,proof)<-zip[0::Int ..]proofs]
   ++[vector "wrong notification private key"(env second 50000)(second{Ref.notificationPrivate=b0+1})Reject,
      vector "noncanonical notification private scalar n"(env second 50000)(second{Ref.notificationPrivate=R.n})Reject,
      vector "different valid-curve Alice public code"(env first 50000)(first{Ref.aliceCode=wrongCode})Reject,
      vector "different Alice chaincode"(env first 50000)(first{Ref.aliceCode=wrongChain})Reject,
      vector "wrong actual Bob child private key"(env second 50000)(second{Ref.selected=Ref.Later 1(R.intFromBytes(unhex((payments!!1)!!1))+1)})Reject,
      vector "noncanonical Bob child private scalar n"(env second 50000)(second{Ref.selected=Ref.Later 1 R.n})Reject,
      vector "fresh valid incoming transaction diverted from derived payee"(mkEnv wrongPayTx 0 defaultTap)first Reject,
      vector "fresh valid incoming transaction underpays requested amount"(env first 49999)first Reject,
      vector "duplicate index0 private role forbidden by canonical witness schema"(env first 50000)(first{Ref.selected=Ref.Later 0 b0})Reject]))
