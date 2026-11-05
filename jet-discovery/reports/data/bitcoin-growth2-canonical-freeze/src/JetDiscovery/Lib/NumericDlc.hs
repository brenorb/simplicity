{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Client-mode complete two-digit standard P2WSH numeric DLC CET verifier.
-- Published ECDSA adaptor/oracle/CET algorithms: dlcspecs9cd9148938c616690c79d99ec6f330e213c246c5, CC-BY4.0.
module JetDiscovery.Lib.NumericDlc(entry,Proof,AdaptorW,adaptorKernel,numericKernel,numericDlc) where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Vector as V
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes(SigTx(..),SigTxInput(..),Outpoint(..))
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer(ctxWith)
import JetDiscovery.Corpus.ContractExpansion(ecdsaVerify)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.NumericDlc as Ref
import qualified JetDiscovery.Ref.BitcoinGrowth as Wire

type GE=(Word256,Word256)
type AdaptorW=(GE,(GE,(Word256,(Word256,Word256))))
type Proof=((Word8,Word8),((Word256,Word256),(AdaptorW,AdaptorW)))
type AdaptorInput=((GE,GE),(Word256,AdaptorW))
type DleqInput=((GE,(GE,GE)),(Word256,Word256))
type DleqChallenge=(GE,(GE,(GE,(GE,GE))))
type Settlement=((GE,Word256),((AdaptorW,AdaptorW),Word256))

same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b=(a&&&b)>>>eq>>>verify
scalar :: Assert t => t Word256()
scalar=(iden&&&konst(w256 R.n))>>>A.lt word256>>>verify
nonzero :: Assert t => t Word256 Word256
nonzero=(((scalar&&&((iden&&&konst(w256 0))>>>eq>>>not iden>>>verify))>>>unit)&&&iden)>>>ih
point :: Assert t => t GE()
point=(((oh&&&konst(w256 R.p))>>>A.lt word256>>>verify)
 &&&((ih&&&konst(w256 R.p))>>>A.lt word256>>>verify)&&&(S.ge_is_on_curve>>>verify))>>>unit
toJ :: (Core t,TyC a) => t a GE -> t a(GE,Word256)
toJ p=p&&&konst(w256 1)
normalize :: Assert t => t(GE,Word256)GE
normalize=S.gej_normalize>>>verify
prefix :: Assert t => t GE Word8
prefix=(ih>>>S.fe_is_odd)&&&unit>>>cond(konst(w8 3))(konst(w8 2))
start :: (Assert t,TyC a) => String -> t a(a,Ctx8)
start tag=iden&&&(unit>>>ctx8InitTag tag)
append :: (Assert t,TyC a,TyC b) => t a b -> t(Ctx8,b)Ctx8 -> t(a,Ctx8)(a,Ctx8)
append f jet=oh&&&((ih&&&(oh>>>f))>>>jet)
appendPoint :: (Assert t,TyC a) => t a GE -> t(a,Ctx8)(a,Ctx8)
appendPoint p=append(p>>>prefix)ctx8Add1>>>append(p>>>oh)ctx8Add32
challenge :: Assert t => t DleqChallenge Word256
challenge=start "DLEQ">>>appendPoint oh>>>appendPoint ioh>>>appendPoint iioh
 >>>appendPoint(ih>>>ih>>>ih>>>oh)>>>appendPoint(ih>>>ih>>>ih>>>ih)
 >>>ih>>>ctx8Finalize>>>S.scalar_normalize
dleq :: forall t. Assert t => t DleqInput()
dleq=(canonical&&&same hash e)>>>unit
 where
  x :: t DleqInput GE
  x=ooh
  y :: t DleqInput GE
  y=oh>>>ih>>>oh
  z :: t DleqInput GE
  z=oh>>>ih>>>ih
  e :: t DleqInput Word256
  e=ioh
  s :: t DleqInput Word256
  s=iih
  ag :: t DleqInput GE
  ag=(((e>>>S.scalar_negate)&&&toJ x)&&&s)>>>S.linear_combination_1>>>normalize
  ay :: t DleqInput GE
  ay=((s&&&toJ y)>>>S.scale)&&&(((e>>>S.scalar_negate)&&&toJ z)>>>S.scale)>>>S.gej_add>>>normalize
  hash :: t DleqInput Word256
  hash=(x&&&(y&&&(z&&&(ag&&&ay))))>>>challenge
  canonical :: t DleqInput()
  canonical=((x>>>point)&&&(y>>>point)&&&(z>>>point)&&&(e>>>scalar)&&&(s>>>scalar))>>>unit

adaptorKernel :: forall t. Assert t => t AdaptorInput()
adaptorKernel=(checks&&&proof&&&linear)>>>unit
 where
  x :: t AdaptorInput GE
  x=ooh
  y :: t AdaptorInput GE
  y=oih
  m :: t AdaptorInput Word256
  m=ioh>>>S.scalar_normalize
  r :: t AdaptorInput GE
  r=iioh
  ra :: t AdaptorInput GE
  ra=ih>>>ih>>>ih>>>oh
  sa :: t AdaptorInput Word256
  sa=ih>>>ih>>>ih>>>ih>>>oh
  es :: t AdaptorInput(Word256,Word256)
  es=ih>>>ih>>>ih>>>ih>>>ih
  checks :: t AdaptorInput()
  checks=((x>>>point)&&&(y>>>point)&&&(r>>>point)&&&(ra>>>point)&&&(sa>>>nonzero>>>unit)
    &&&(r>>>oh>>>S.scalar_normalize>>>nonzero>>>unit))>>>unit
  proof :: t AdaptorInput()
  proof=((ra&&&(y&&&r))&&&es)>>>dleq
  mul :: t(Word256,Word256)Word256
  mul=S.scalar_multiply
  -- Carry the actual inverse once; u1/u2 use projections of this value.
  linear :: t AdaptorInput()
  linear=(iden&&&(sa>>>S.scalar_invert))>>>same
    (((((oh>>>r>>>oh>>>S.scalar_normalize)&&&ih)>>>mul)&&&toJ(oh>>>x))
       &&&(((oh>>>m)&&&ih)>>>mul)>>>S.linear_combination_1>>>normalize)
    (oh>>>ra)

appendConst :: Assert t => B.ByteString -> t Ctx8 Ctx8
appendConst bytes|B.null bytes=iden
 |otherwise=piece n(B.take n bytes)>>>appendConst(B.drop n bytes)
 where
  n=P.head[k|k<-[32,16,8,4,2,1],k<=B.length bytes]
  piece 32 b=ctxWith(konst(w256FromBytes b))ctx8Add32
  piece 16 b=ctxWith(konst(toWord128(R.intFromBytes b)))ctx8Add16
  piece 8 b=ctxWith(konst(w64(R.intFromBytes b)))ctx8Add8
  piece 4 b=ctxWith(konst(w32(R.intFromBytes b)))ctx8Add4
  piece 2 b=ctxWith(konst(w16(R.intFromBytes b)))ctx8Add2
  piece _ b=ctxWith(konst(w8(R.intFromBytes b)))ctx8Add1
doubleHash :: Assert t => t Word256 Word256
doubleHash=((unit>>>ctx8Init)&&&iden)>>>ctx8Add32>>>ctx8Finalize
outpoint :: (Assert t,Primitive t,TyC a) => t a(Word256,Word32)
outpoint=konst(w32 0)>>>primitive Prim.InputPrevOutpoint>>>verify
outValue :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
outValue i=konst(w32 i)>>>primitive Prim.OutputValue>>>verify
value :: (Assert t,Primitive t,TyC a) => t a Word64
value=konst(w32 0)>>>primitive Prim.InputValue>>>verify

-- Complete standard BIP143 ALL01 message. All variable fields come from the
-- actual CET; constant script bytes are checked against the actual UTXO/output hashes.
cetMessage :: (Assert t,Primitive t) => B.ByteString -> [B.ByteString] -> t()Word256
cetMessage ws destinations=ctx8Init
 >>>ctxWith(primitive Prim.Version)ctxAddLE32
 >>>ctxWith prevouts ctx8Add32>>>appendConst(Wire.sha256d(Wire.le32 0xfffffffe))
 >>>ctxWith(outpoint>>>oh)ctx8Add32>>>ctxWith(outpoint>>>ih)ctxAddLE32
 >>>appendConst(B.singleton(fromIntegral(B.length ws))<>ws)
 >>>ctxWith value ctxAddLE64>>>appendConst(Wire.le32 0xfffffffe)
 >>>ctxWith outputs ctx8Add32>>>ctxWith(primitive Prim.LockTime)ctxAddLE32
 >>>appendConst(Wire.le32 1)>>>ctx8Finalize>>>doubleHash
 where
  prevouts=ctx8Init>>>ctxWith(outpoint>>>oh)ctx8Add32>>>ctxWith(outpoint>>>ih)ctxAddLE32>>>ctx8Finalize>>>doubleHash
  outputs=ctx8Init>>>L.foldr(>>>)iden[ctxWith(outValue(toInteger i))ctxAddLE64>>>appendConst(B.singleton(fromIntegral(B.length script))<>script)|(i,script)<-zip[0..]destinations]>>>ctx8Finalize>>>doubleHash

digitMessage :: Assert t => t Word8 Word256
digitMessage=(((iden&&&konst(w8 10))>>>A.lt word8>>>verify)&&&iden)>>>ih
 >>>((unit>>>ctx8InitTag "DLC/oracle/attestation/v0")&&&((iden&&&konst(w8 48))>>>A.add word8>>>ih))>>>ctx8Add1>>>ctx8Finalize
signaturePoint :: Assert t => Integer -> Integer -> t Word8 GE
signaturePoint public nonce=(unit>>>ctx8InitTag "BIP0340/challenge">>>appendConst(R.bytesFromInt nonce<>R.bytesFromInt public))
 &&&digitMessage>>>ctx8Add32>>>ctx8Finalize>>>S.scalar_normalize
 >>>((iden&&&konst(pointW(R.liftX public),w256 1))>>>S.scale)&&&konst(pointW(R.liftX nonce),w256 1)
 >>>S.gej_add>>>normalize
attest :: Assert t => Integer -> Integer -> t(Word8,Word256)GE
attest public nonce=((oh>>>signaturePoint public nonce)&&&(ih>>>nonzero))
 >>>(same oh(ih>>>S.generate>>>normalize)&&&oh)>>>ih
oracleAggregate :: Assert t => Integer -> [Integer] -> t((Word8,Word8),(Word256,Word256))(GE,Word256)
oracleAggregate public nonces=
 (((((ooh&&&ioh)>>>attest public(nonces P.!!0))>>>toJ iden)
     &&&(((oih&&&iih)>>>attest public(nonces P.!!1))>>>toJ iden))>>>S.gej_add>>>normalize)
 &&&((ioh&&&iih)>>>S.scalar_add>>>nonzero)
lowS :: Assert t => t Word256 Word256
lowS=((iden&&&konst(w256(R.n`div`2)))>>>A.le word256)&&&iden>>>cond iden S.scalar_negate
decrypted :: Assert t => t(AdaptorW,Word256)(Word256,Word256)
decrypted=(ooh>>>oh>>>S.scalar_normalize)&&&((oh>>>ih>>>ih>>>oh)&&&(ih>>>S.scalar_invert)>>>S.scalar_multiply>>>lowS)
settle :: forall t. Assert t => [GE] -> t Settlement()
settle keys=(check 0&&&check 1)>>>unit
 where
  adaptor :: t AdaptorInput()
  adaptor=adaptorKernel
  plaintext :: t((GE,Word256),(Word256,Word256))()
  plaintext=ecdsaVerify
  decrypt :: t(AdaptorW,Word256)(Word256,Word256)
  decrypt=decrypted
  one :: Int -> t Settlement AdaptorW
  one 0=iooh
  one _=ioih
  check :: Int -> t Settlement()
  check i=((((konst(keys P.!!i)&&&ooh)&&&(iih&&&one i))>>>adaptor)
    &&&(((konst(keys P.!!i)&&&iih)&&&((one i&&&oih)>>>decrypt))>>>plaintext))>>>unit

widen8 :: Core t => t Word8 Word64
widen8=konst(w32 0)&&&(konst(w16 0)&&&(konst(w8 0)&&&iden))
payout :: Assert t => t(Word8,Word8)Word64
payout=((((oh>>>widen8)&&&konst(w64 10))>>>A.multiply word64>>>ih)&&&(ih>>>widen8))
 >>>A.add word64>>>ih>>>(iden&&&konst(w64 1))>>>A.add word64>>>ih
 >>>(iden&&&konst(w64 1000))>>>A.multiply word64>>>ih

numericDlc :: (Simplicity t,Primitive t) => Proof -> t()()
numericDlc proof=witness proof>>>numericKernel
numericKernel :: forall t. (Assert t,Primitive t) => t Proof()
numericKernel=((preflight&&&iden)>>>ih)
 >>>(((oh&&&ioh)>>>oracleAggregate oraclePublic oracleNonces)&&&(iih&&&(unit>>>cetMessage witnessScript destinations)))
 >>>settle(map(pointW.R.pointMul R.gPt)partySecrets)
 where
  preflight :: t Proof()
  preflight=(shape&&&outputs&&&amounts)>>>unit
  shape :: t Proof()
  shape=(same(unit>>>Tx.numInputs)(konst(w32 1))&&&same(unit>>>Tx.numOutputs)(konst(w32 2))
   &&&same(unit>>>primitive Prim.Version)(konst(w32 2))&&&same(unit>>>primitive Prim.LockTime)(konst(w32 900000))
   &&&same(outpoint>>>oh)(konst(w256FromBytes(hashToBytes fundingHash)))&&&same(outpoint>>>ih)(konst(w32 0))
   &&&same(konst(w32 0)>>>primitive Prim.InputSequence>>>verify)(konst(w32 0xfffffffe))
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptSigHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 B.empty))))
   &&&same(konst(w32 0)>>>primitive Prim.InputAnnexHash>>>verify)(konst(Left()))
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 fundingScript)))))>>>unit
  outputs :: t Proof()
  outputs=L.foldr(\(i,script)rest->(same(konst(w32 i)>>>primitive Prim.OutputScriptHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 script))))&&&rest)>>>unit)unit(zip[0..]destinations)
  amounts :: t Proof()
  amounts=(same value(konst(w64 102000))&&&same(outValue 0)(oh>>>payout)
   &&&same(outValue 1)((konst(w64 101000)&&&(oh>>>payout))>>>A.subtract word64>>>ih))>>>unit

pointW(Just(x,y))=(w256 x,w256 y)
pointW Nothing=error "DLC infinity fixture"
adaptorW(Ref.Adaptor r ra sa e s)=(pointW r,(pointW ra,(w256 sa,(w256 e,w256 s))))
partySecrets=L.sortOn(Ref.compressed.R.pointMul R.gPt)[11,22]
oracleSecret=37
oraclePublic=R.pubkeyOf oracleSecret
oracleNonces=map R.pubkeyOf[101,103]
fundingHash=hashFromInteger 0xd1c000127
witnessScript=B.singleton 0x52<>B.concat[B.singleton 33<>Ref.compressed(R.pointMul R.gPt d)|d<-partySecrets]<>unhex "52ae"
fundingScript=unhex "0020"<>hashToBytes(sha256 witnessScript)
destinations=[unhex "0014"<>B.replicate 20 0x11,unhex "0014"<>B.replicate 20 0x22]

entry :: IO Entry
entry=return(Entry "app-numeric-dlc-adaptor-cet"
 "Complete two-digit numeric DLC P2WSH CET with exact oracle transcript and two ECDSA adaptor signatures"
 "dlcspecs9cd9148938c616690c79d99ec6f330e213c246c5: Oracle.md,NumericOutcomeCompression.md,ECDSA-adaptor.md,Transactions.md; BIP143ALL01"
 BitcoinApp(Derived "Standard-wire single-input P2WSH2of2 CET, exact BIP143ALL signatures and numeric oracle/adaptor math; all11 official ECDSA-adaptor cases separately inventoried")
 ["CLIENT MODE: verifies a standard Bitcoin P2WSH DLC transaction in a client-supplied primitive environment, not a Simplicity leaf controlling this P2WSH output",
  "Client authenticates the actual funding UTXO, negotiated contract and signed oracle announcement/nonces; no chain membership, funding construction, negotiation or oracle reputation claim",
  "One committed funding outpoint/index0,102000sats, lexicographically sorted compressed2of2 funding keys, empty scriptSig/no annex, version2,sequenceFFFFFFFE,cet_locktime900000",
  "Two unsigned decimal digits with fixed per-digit oracle nonces; exact DLC/oracle/attestation/v0 UTF8 message then BIP340challenge; both signature scalars checked and summed, nonzero aggregate encryption point/key",
  "Uncompressed numeric domain00..99, payoutA=(value+1)*1000,payoutB=101000-payoutA; both outputs >=1000 dust, fixed payout_serial_id order and two committed P2WPKH scripts; funding includes1000-sat fee",
  "Both full ECDSA adaptor DLEQs and sa^-1(mG+rX)=Ra checked; y=sum oracle scalars decrypts actual low-S ECDSAs, which are independently verified on exact actual BIP143ALL01 CET digest",
  "Canonical decoded proof carries one logical structured witness; final DER+ALL witness transport is a client codec boundary, independently serialized/parsed by tooling",
  "No compressed payout intervals, multi-oracle threshold, refunds or complete DLC setup/exchange protocol claim; one meaningful full numeric settlement verifier, helpers receive no extra group"]
 (boundProgram numericKernel)vectors)
 where
  make d0 d1 delta wrongScript alter nonce=
   let (_,s0)=Ref.oracleAttest oracleSecret 101 d0;(_,s1)=Ref.oracleAttest oracleSecret 103 d1
       y=(s0+s1)`mod`R.n;enc=R.pointMul R.gPt y
       a=(d0*10+d1+1)*1000
       scripts=if wrongScript then[destinations P.!!1,destinations P.!!1]else destinations
       tx=alter(mkTx 2[mkInput(Outpoint fundingHash 0)102000(BL.fromStrict fundingScript)0xfffffffe]
          [mkOutput(fromInteger(a+delta))(scripts P.!!0),mkOutput(fromInteger(101000-a-delta))(scripts P.!!1)]900000)
       msg=Ref.cetSighash witnessScript tx
       signatures=[Ref.encrypt secret enc msg(nonce+toInteger i*2)(nonce+toInteger i*2+1)|(i,secret)<-zip[0..]partySecrets]
       proof=((w8 d0,w8 d1),((w256 s0,w256 s1),(adaptorW(signatures P.!!0),adaptorW(signatures P.!!1))))
   in(mkEnv tx 0 defaultTap,proof,tx,signatures,y)
  (goodEnv,good,_,_,_)=make 4 2 0 False P.id 211
  (zeroEnv,zero,_,_,_)=make 0 0 0 False P.id 223
  (maxEnv,maxProof,_,_,_)=make 9 9 0 False P.id 227
  (payoutEnv,badPayout,_,_,_)=make 4 2 1 False P.id 229
  (scriptEnv,badScript,_,_,_)=make 4 2 0 True P.id 233
  (lockEnv,badLock,_,_,_)=make 4 2 0 False(\tx->tx{sigTxLock=899999})239
  (seqEnv,badSeq,_,_,_)=make 4 2 0 False(\tx->tx{sigTxIn=V.map(\i->i{sigTxiSequence=0xffffffff})(sigTxIn tx)})241
  (fundEnv,badFunding,_,_,_)=make 4 2 0 False(\tx->tx{sigTxIn=V.map(\i->i{sigTxiPreviousOutpoint=dummyOutpoint 0})(sigTxIn tx)})251
  (digits,((s0,s1),(a,b)))=good
  (rr,(ra,(sa,(e,s))))=a
  vectors=[Vector "complete oracle digits42 with two real adaptors" goodEnv good Accept,
   Vector "numeric lower endpoint00" zeroEnv zero Accept,
   Vector "numeric upper endpoint99" maxEnv maxProof Accept,
   Vector "fresh valid adaptors cannot change negotiated payout" payoutEnv badPayout Reject,
   Vector "fresh valid adaptors cannot divert actual payout script" scriptEnv badScript Reject,
   Vector "fresh valid adaptors cannot change negotiated maturity" lockEnv badLock Reject,
   Vector "fresh valid adaptors cannot disable maturity with final sequence" seqEnv badSeq Reject,
   Vector "fresh valid adaptors cannot substitute funding outpoint" fundEnv badFunding Reject,
   Vector "oracle scalar changed at its single occurrence" goodEnv(digits,((w256 1,s1),(a,b)))Reject,
   Vector "nondecimal digit10" goodEnv((w8 10,snd digits),((s0,s1),(a,b)))Reject,
   Vector "noncanonical oracle scalar n" goodEnv(digits,((w256 R.n,s1),(a,b)))Reject,
   Vector "adaptor proof challenge changed at single occurrence" goodEnv(digits,((s0,s1),((rr,(ra,(sa,(w256 1,s)))),b)))Reject,
   Vector "noncanonical adaptor DLEQ challenge n" goodEnv(digits,((s0,s1),((rr,(ra,(sa,(w256 R.n,s)))),b)))Reject,
   Vector "noncanonical adaptor DLEQ response n" goodEnv(digits,((s0,s1),((rr,(ra,(sa,(e,w256 R.n)))),b)))Reject,
   Vector "noncanonical adaptor encrypted response n" goodEnv(digits,((s0,s1),((rr,(ra,(w256 R.n,(e,s)))),b)))Reject]
