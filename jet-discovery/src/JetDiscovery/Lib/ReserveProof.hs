{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Complete supported BIP127 client-mode virtual transaction predicate.
-- This transaction is deliberately not broadcastable. Primitive input amounts
-- and scripts represent the client's externally authenticated Bitcoin UTXO view.
module JetDiscovery.Lib.ReserveProof(entry,reserveProof,reserveKernel,Proof) where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
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
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as EC
import qualified JetDiscovery.Ref.ReserveProof as Ref

type Sig=(Word256,Word256)
type Keys=((Word256,Sig),(Word256,Sig))
type Proof=(Buffer511 Word8,Keys)
type ReserveInput=(Word256,Keys)
type Hashes=(Word256,(Word256,(Word256,Word256)))
type Verification=(Keys,Hashes)
same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b=(a&&&b)>>>eq>>>verify
checkedAdd :: (Assert t,TyC a) => t a Word64 -> t a Word64 -> t a Word64
checkedAdd a b=(a&&&b)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
outpoint :: (Assert t,Primitive t,TyC a) => Integer -> t a(Word256,Word32)
outpoint i=konst(w32 i)>>>primitive Prim.InputPrevOutpoint>>>verify
value :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
value i=konst(w32 i)>>>primitive Prim.InputValue>>>verify
scriptHash :: (Assert t,Primitive t,TyC a) => Integer -> t a Word256
scriptHash i=konst(w32 i)>>>primitive Prim.InputScriptHash>>>verify
outputValue :: (Assert t,Primitive t,TyC a) => t a Word64
outputValue=konst(w32 0)>>>primitive Prim.OutputValue>>>verify
bswap128 :: Core t => t Word128 Word128
bswap128=(ih>>>bswap64)&&&(oh>>>bswap64)
bswap256 :: Core t => t Word256 Word256
bswap256=(ih>>>bswap128)&&&(oh>>>bswap128)
appendConst :: Assert t => B.ByteString -> t Ctx8 Ctx8
appendConst bytes|B.null bytes=iden
 |otherwise=piece n(B.take n bytes)>>>appendConst(B.drop n bytes)
 where
  n=P.head[k|k<-[32,16,8,4,2,1],k<=B.length bytes]
  number=EC.intFromBytes
  piece 32 b=ctxWith(konst(w256FromBytes b))ctx8Add32
  piece 16 b=ctxWith(konst(toWord128(number b)))ctx8Add16
  piece 8 b=ctxWith(konst(w64(number b)))ctx8Add8
  piece 4 b=ctxWith(konst(w32(number b)))ctx8Add4
  piece 2 b=ctxWith(konst(w16(number b)))ctx8Add2
  piece _ b=ctxWith(konst(w8(number b)))ctx8Add1
append :: (Assert t,TyC a,TyC b) => t a b -> t(Ctx8,b)Ctx8 -> t(a,Ctx8)(a,Ctx8)
append f jet=oh&&&((ih&&&(oh>>>f))>>>jet)
applyCtx :: (Assert t,TyC a) => t Ctx8 Ctx8 -> t(a,Ctx8)(a,Ctx8)
applyCtx f=oh&&&(ih>>>f)
p2trHash :: Assert t => t Word256 Word256
p2trHash=(((unit>>>ctx8Init)&&&konst(w16 0x5120)>>>ctx8Add2)&&&iden)>>>ctx8Add32>>>ctx8Finalize
commitment :: Assert t => t(Buffer511 Word8)Word256
commitment=((unit>>>ctx8Init>>>appendConst(C.pack "Proof-of-Reserves: "))&&&iden)>>>ctx8AddBuffer511>>>ctx8Finalize

prevoutsHash :: (Assert t,Primitive t) => t()Word256
prevoutsHash=ctx8Init>>>L.foldr(>>>)iden[step i|i<-[0..2]]>>>ctx8Finalize
 where
  step i=ctxWith(outpoint i>>>oh>>>bswap256)ctx8Add32>>>ctxWith(outpoint i>>>ih)ctxAddLE32
amountsHash :: (Assert t,Primitive t) => t()Word256
amountsHash=ctx8Init>>>L.foldr(>>>)iden[ctxWith(value i)ctxAddLE64|i<-[0..2]]>>>ctx8Finalize
scriptsHash :: Assert t => t(Word256,Word256)Word256
scriptsHash=(iden&&&(unit>>>ctx8Init>>>appendConst(unhex "0151225120")))
 >>>append oh ctx8Add32>>>applyCtx(appendConst(unhex "225120"))>>>append ih ctx8Add32>>>ih>>>ctx8Finalize
outputsHash :: (Assert t,Primitive t) => t()Word256
outputsHash=ctx8Init>>>ctxWith outputValue ctxAddLE64>>>appendConst(unhex "016a")>>>ctx8Finalize
hashes :: (Assert t,Primitive t) => t ReserveInput Hashes
hashes=(unit>>>prevoutsHash)&&&((unit>>>amountsHash)&&&(((iooh&&&iioh)>>>scriptsHash)&&&(unit>>>outputsHash)))

sigMessage :: Assert t => Integer -> t Hashes Word256
sigMessage index=(iden&&&(unit>>>ctx8InitTag "TapSighash">>>appendConst(unhex "00010200000000000000")))
 >>>append oh ctx8Add32>>>append ioh ctx8Add32>>>append iioh ctx8Add32
 >>>applyCtx(appendConst(hashToBytes(sha256(B.replicate 12 0xff))))
 >>>append (ih>>>ih>>>ih) ctx8Add32>>>applyCtx(appendConst(B.singleton 0))
 >>>append(konst(w32 index))ctxAddLE32>>>ih>>>ctx8Finalize

reserveProof :: (Simplicity t,Primitive t) => Word256 -> Proof -> t()()
reserveProof expected proof=witness proof>>>reserveKernel expected
reserveKernel :: (Assert t,Primitive t) => Word256 -> t Proof()
reserveKernel expected=((oh>>>commitment)&&&ih)
 >>>((preflight expected&&&iden)>>>ih)>>>((ih&&&hashes)>>>signatures)
preflight :: forall t. (Assert t,Primitive t) => Word256 -> t ReserveInput()
preflight expected=(same oh(konst expected)&&&shape&&&commit&&&utxos&&&total&&&unique)>>>unit
 where
  shape :: t ReserveInput()
  shape=(same(unit>>>Tx.numInputs)(konst(w32 3))&&&same(unit>>>Tx.numOutputs)(konst(w32 1))
   &&&same(unit>>>primitive Prim.Version)(konst(w32 2))&&&same(unit>>>primitive Prim.LockTime)(konst(w32 0))
   &&&L.foldr(\i rest->(same(konst(w32 i)>>>primitive Prim.InputSequence>>>verify)(konst(w32 0xffffffff))
      &&&same(konst(w32 i)>>>primitive Prim.InputScriptSigHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 B.empty))))
      &&&same(konst(w32 i)>>>primitive Prim.InputAnnexHash>>>verify)(konst(Left()))&&&rest)>>>unit)unit[0..2])>>>unit
  commit :: t ReserveInput()
  commit=(same(outpoint 0>>>oh)(oh>>>bswap256)&&&same(outpoint 0>>>ih)(konst(w32 0))
   &&&same(value 0)(konst(w64 0))&&&same(scriptHash 0)(konst(w256FromBytes(hashToBytes(sha256(unhex "51"))))))>>>unit
  utxos :: t ReserveInput()
  utxos=(same(scriptHash 1)(iooh>>>p2trHash)&&&same(scriptHash 2)(iioh>>>p2trHash)
   &&&same(konst(w32 0)>>>primitive Prim.OutputScriptHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256(unhex "6a"))))))>>>unit
  total :: t ReserveInput()
  total=(same outputValue(checkedAdd(value 1)(value 2))
    &&&((outputValue&&&konst(w64 2100000000000000))>>>A.le word64>>>verify)
    &&&((konst(w64 0)&&&outputValue)>>>A.lt word64>>>verify))>>>unit
  unique :: t ReserveInput()
  unique=L.foldr(\(a,b)rest->(((outpoint a&&&outpoint b)>>>eq>>>not iden>>>verify)&&&rest)>>>unit)unit[(0,1),(0,2),(1,2)]
signatures :: Assert t => t Verification()
signatures=((((ooh>>>oh)&&&(ih>>>sigMessage 1))&&&(ooh>>>ih))>>>S.bip_0340_verify)
 &&&((((oih>>>oh)&&&(ih>>>sigMessage 2))&&&(oih>>>ih))>>>S.bip_0340_verify)>>>unit

sigWords raw=(w256FromBytes(B.take 32 raw),w256FromBytes(B.drop 32 raw))
entry :: IO Entry
entry=return(Entry "app-reserve-ownership-and-sum" "BIP127 client-mode two-reserve ownership and exact-sum proof with standard BIP341 ALL signatures"
 "BIP127 v1.0.0; normative single-SHA commitment; reports/BIP127-MISMATCH.md records pinned BDK SHA256d incompatibility"
 BitcoinApp(Derived "Exact virtual transaction, canonical supported keypath proof encoding, independently constructed BIP341 ALL signatures; no official BIP127 vectors published")
 ["CLIENT MODE: the proof transaction deliberately has a nonexistent commitment input and cannot be broadcast; this is not a redeemable escrow or proof of solvency",
  "Client must populate the primitive environment from the actual proof transaction and an externally authenticated, block-specific UTXO view; the predicate does not independently prove chain membership or unspentness",
  "Exactly three inputs: canonical zero-valued OP_TRUE phantom metadata, plus two P2TR keypath reserve inputs; one OP_RETURN output equals exact reserve sum, no miner fee",
  "Version2, locktime0, all sequencesFFFFFFFF, all scriptSigs empty, no annex; decoded witness format is empty for input0 and one65-byte ALL signature for each reserve input",
  "Every standard BIP341 ALL digest field is constructed from actual virtual transaction/UTXO fields; both different input-index messages are checked, duplicate outpoints rejected",
  "Fixed public challenge Some Message, <=511-byte UTF-8 message boundary; commitment is single SHA256 of Proof-of-Reserves prefix plus message, raw digest bytes used in wire outpoint",
  "Proof wire/parser and chain-view acquisition are client boundaries; all public values are trusted only through that authenticated view, never because a witness claims a reserve amount",
  "Budget fractions for this intrinsically invalid virtual transaction are analysis comparisons, not onchain deployability claims"]
 (boundProgram(reserveKernel(w256FromBytes expected)))vectors)
 where
  message=C.pack "Some Message";expected=Ref.commitment message
  keys=[11,22]::[Integer]
  pk i=EC.pubkeyOf(keys P.!!i)
  p2tr x=unhex "5120"<>EC.bytesFromInt x
  make commitmentBytes duplicate delta nonempty=
   let op=Outpoint(hashFromBytes(B.reverse commitmentBytes))0
       a=mkInput(dummyOutpoint 1)50000(BL.fromStrict(p2tr(pk 0)))0xffffffff
       b=if duplicate then a else mkInput(dummyOutpoint 2)60000(BL.fromStrict(p2tr(pk 1)))0xffffffff
       total=if duplicate then 100000 else 110000
       tx0=mkTx 2[mkInput op 0(BL.fromStrict(unhex "51"))0xffffffff,a,b][mkOutput(total+delta)(unhex "6a")]0
       tx=if nonempty then tx0{sigTxIn=V.imap(\i input->if i==1 then input{sigTxiScriptSig=BL.fromStrict(unhex "00")}else input)(sigTxIn tx0)}else tx0
       second=if duplicate then keys P.!!0 else keys P.!!1
       sigs=Ref.signatures tx(keys P.!!0)second
       proof=(buffer511FromBytes message,((w256(pk 0),sigWords(P.head sigs)),(w256(EC.pubkeyOf second),sigWords(sigs P.!!1))))
   in(mkEnv tx 0 defaultTap,proof,tx,sigs)
  (goodEnv,good,_,_)=make expected False 0 False
  (duplicateEnv,duplicate,_,_)=make expected True 0 False
  double=hashToBytes(sha256 expected)
  (bdkEnv,bdk,_,_)=make double False 0 False
  (feeEnv,fee,_,_)=make expected False 1 False
  (scriptEnv,scriptProof,_,_)=make expected False 0 True
  (m,((a,sa),(b,sb)))=good
  vectors=[Vector "two real ownership signatures and exact reserve sum" goodEnv good Accept,
   Vector "same actual reserve duplicated with fresh valid signatures" duplicateEnv duplicate Reject,
   Vector "BDK double-SHA commitment with fresh valid signatures" bdkEnv bdk Reject,
   Vector "nonzero virtual fee with fresh valid signatures" feeEnv fee Reject,
   Vector "nonempty P2TR scriptSig with fresh valid signatures" scriptEnv scriptProof Reject,
   Vector "reserve signature slots exchanged" goodEnv(m,((a,sb),(b,sa)))Reject,
   Vector "different audit message reuses old signatures" goodEnv(buffer511FromBytes(C.pack "Other Message"),((a,sa),(b,sb)))Reject]
