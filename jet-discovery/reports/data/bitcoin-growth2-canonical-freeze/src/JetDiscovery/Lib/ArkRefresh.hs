{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Exact bounded current Bark hArk completion-certificate client verifier.
-- Real Taproot/MuSig2-derived keys, BIP341 DEFAULT and current HASH160 scripts.
module JetDiscovery.Lib.ArkRefresh(entry,Proof,arkKernel,arkProof) where
import Prelude hiding(drop,take,not,and,or)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as S
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes(Outpoint(..))
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.Ripemd160 as RI
import qualified JetDiscovery.Lib.TaprootTx1 as T
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.ArkRefresh as A
import qualified JetDiscovery.Ref.ArkRefreshPackage as P

type Sig=(Word256,Word256)
type Sigs=(Sig,(Sig,(Sig,Sig)))
type Proof=(Word32,(Word256,Sigs))
type Hashed=(Word256,(Word256,(Word256,Sigs))) -- expiry leaf, user unlock leaf, server unlock leaf, signatures
type Five=(Word256,(Word256,(Word256,(Word256,Word256))))
type Globals=(Five,Sigs) -- node Q, leaf A Q, leaf B Q, forfeit Q, leaf A script hash
type NodeState=((Word256,Five),(Sig,(Sig,Sig)))
type LeafState=((Word256,(Word256,(Word256,Word256))),(Sig,Sig))
same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b=(a&&&b)>>>eq>>>verify
sha32 :: Assert t => t Word256 Word256
sha32=((unit>>>ctx8Init)&&&iden)>>>ctx8Add32>>>ctx8Finalize
hash160 :: forall t. Assert t => t Word256 RI.W5
hash160=sha32>>>((RI.ivT&&&block)>>>RI.ripemd160Compress)
 where
  word :: Int -> t Word256 Word32
  word i=RI.pick(i>=4)(RI.pick(odd(i`div`2))(RI.pick(odd i)iden))>>>bswap32
  block :: t Word256(Vector16 Word32)
  block=RI.mk16([word i|i<-[0..7]]++[konst(w32 0x80)]++replicate 5(konst(w32 0))++[konst(w32 256),konst(w32 0)])
-- Current heights fit a minimal positive three-byte Script number.
expiryLeaf :: Assert t => t Word32 Word256
expiryLeaf=(iden&&&(unit>>>ctx8InitTag "TapLeaf">>>T.appendConst(unhex "c02803")))
 >>>T.append(ih>>>ih)ctx8Add1>>>T.append(ih>>>oh)ctx8Add1>>>T.append(oh>>>ih)ctx8Add1
 >>>T.constant(unhex "b17520"<>R.bytesFromInt(R.pubkeyOf P.serverSecret)<>unhex "ac")>>>ih>>>ctx8Finalize
unlockLeaf :: Assert t => Integer -> t RI.W5 Word256
unlockLeaf public=(iden&&&(unit>>>ctx8InitTag "TapLeaf">>>T.appendConst(unhex "c03d82012088a914")))
 >>>T.append oh ctxAddLE32>>>T.append ioh ctxAddLE32>>>T.append iioh ctxAddLE32
 >>>T.append(ih>>>ih>>>ih>>>oh)ctxAddLE32>>>T.append(ih>>>ih>>>ih>>>ih)ctxAddLE32
 >>>T.constant(unhex "8820"<>R.bytesFromInt public<>unhex "ac")>>>ih>>>ctx8Finalize
branch :: Assert t => t(Word256,Word256)Word256
branch=(((oh&&&ih)>>>Arith.le word256)&&&iden>>>cond iden(ih&&&oh))
 >>>(iden&&&(unit>>>ctx8InitTag "TapBranch"))>>>T.append oh ctx8Add32>>>T.append ih ctx8Add32>>>ih>>>ctx8Finalize
tweak :: Assert t => Integer -> t Word256 Word256
tweak public=((unit>>>ctx8InitTag "TapTweak">>>T.appendConst(R.bytesFromInt public))&&&iden)>>>ctx8Add32>>>ctx8Finalize
 >>>((((iden&&&konst(w256 R.n))>>>Arith.lt word256>>>verify)&&&iden)>>>ih)
 >>>(((konst(w256 1)&&&konst(pointW(R.liftX public),w256 1)))&&&iden)
 >>>S.linear_combination_1>>>S.gej_normalize>>>verify>>>oh
prepare :: Assert t => t Proof Hashed
prepare=(oh>>>expiryLeaf)&&&(((ioh>>>hash160)&&&(ih>>>ih))
 >>>((oh>>>unlockLeaf(R.xOnly P.newAggregate))&&&((oh>>>unlockLeaf(R.pubkeyOf P.serverSecret))&&&ih)))
globals :: forall t. Assert t => t Hashed Globals
globals=(root&&&(leafA&&&(leafB&&&(forfeit&&&ioh))))&&&(ih>>>ih>>>ih)
 where
  node :: t(Word256,Word256)Word256
  node=branch
  root :: t Hashed Word256
  root=oh>>>tweak(R.xOnly P.nodeAggregate)
  leafA :: t Hashed Word256
  leafA=(oh&&&ioh)>>>node>>>tweak(R.xOnly P.newAggregate)
  leafB :: t Hashed Word256
  leafB=(oh&&&konst(w256FromBytes(A.tapLeaf(A.hashSignScript P.otherHash(R.xOnly P.otherAggregate)))))
   >>>node>>>tweak(R.xOnly P.otherAggregate)
  forfeit :: t Hashed Word256
  forfeit=(iioh&&&konst(w256FromBytes(A.tapLeaf(A.delayedScript P.exitDelta(R.pubkeyOf P.oldUserSecret)))))
   >>>node>>>tweak(R.xOnly P.oldAggregate)
p2trHash :: Assert t => t Word256 Word256
p2trHash=((unit>>>ctx8Init>>>T.appendConst(unhex "5120"))&&&iden)>>>ctx8Add32>>>ctx8Finalize
inputData :: (Core t,TyC a) => t a(Word256,Word32) -> t a Word64 -> t a Word256 -> t a Word32 -> t a Word32 -> t a Word32 -> t a T.Input
inputData op val key sq ver lock=op&&&(val&&&(key&&&(sq&&&(ver&&&lock))))
frame :: (Core t,TyC a) => t a Word256 -> Integer -> Integer -> t a Word256 -> Integer -> t a T.Out -> t a T.Out -> t a T.TxData
frame previous idx value key sq a b=inputData(previous&&&konst(w32 idx))(konst(w64 value))key(konst(w32 sq))(konst(w32 3))(konst(w32 0))&&&(a&&&b)
out :: (Core t,TyC a) => Integer -> t a Word256 -> t a T.Out
out value key=konst(w64 value)&&&key
zeroOut :: (Core t,TyC a) => t a T.Out
zeroOut=konst(w64 0,w256 0)
roundData :: forall t. (Assert t,Primitive t) => t Word256 T.TxData
roundData=inputData op actualValue(konst(w256(R.xOnly P.fundingOutput)))sq ver lock
 &&&((vout 0&&&iden)&&&(vout 1&&&konst(w256(R.xOnly P.serverOutput))))
 where
  op :: t Word256(Word256,Word32)
  op=konst(w32 0)>>>primitive Prim.InputPrevOutpoint>>>verify
  actualValue=konst(w32 0)>>>primitive Prim.InputValue>>>verify
  sq=konst(w32 0)>>>primitive Prim.InputSequence>>>verify
  ver=unit>>>primitive Prim.Version
  lock=unit>>>primitive Prim.LockTime
  vout i=konst(w32 i)>>>primitive Prim.OutputValue>>>verify
roundCheck :: forall t. (Assert t,Primitive t) => t Globals()
roundCheck=(shape&&&funding&&&payouts)>>>unit
 where
  shape :: t Globals()
  shape=(same(unit>>>Tx.numInputs)(konst(w32 1))&&&same(unit>>>Tx.numOutputs)(konst(w32 2))
   &&&same(unit>>>primitive Prim.CurrentIndex)(konst(w32 0))
   &&&same(unit>>>primitive Prim.Version)(konst(w32 2))&&&same(unit>>>primitive Prim.LockTime)(konst(w32 0))
   &&&same(konst(w32 0)>>>primitive Prim.InputSequence>>>verify)(konst(w32 0xfffffffe))
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptSigHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256 B.empty))))
   &&&same(konst(w32 0)>>>primitive Prim.InputAnnexHash>>>verify)(konst(Left())))>>>unit
  funding :: t Globals()
  funding=(same(konst(w32 0)>>>primitive Prim.InputPrevOutpoint>>>verify)(konst(outpointW P.fundingPoint))
   &&&same(konst(w32 0)>>>primitive Prim.InputValue>>>verify)(konst(w64 P.roundValue))
   &&&same(konst(w32 0)>>>primitive Prim.InputScriptHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256(P.p2tr P.fundingOutput))))))>>>unit
  payouts :: t Globals()
  payouts=(same(konst(w32 0)>>>primitive Prim.OutputValue>>>verify)(konst(w64(P.newValue+P.otherValue)))
   &&&same(konst(w32 1)>>>primitive Prim.OutputValue>>>verify)(konst(w64 P.changeValue))
   &&&same(konst(w32 0)>>>primitive Prim.OutputScriptHash>>>verify)(ooh>>>p2trHash)
   &&&same(konst(w32 1)>>>primitive Prim.OutputScriptHash>>>verify)(konst(w256FromBytes(hashToBytes(sha256(P.p2tr P.serverOutput))))))>>>unit
runRound :: forall t. (Assert t,Primitive t) => t Globals NodeState
runRound=((roundCheck&&&sig)&&&result)>>>ih
 where
  rd :: t Globals T.TxData
  rd=ooh>>>roundData
  sig :: t Globals()
  sig=((konst(w256(R.xOnly P.fundingOutput))&&&((rd&&&konst(w256 0))>>>T.defaultMessage 2 False False))&&&ioh)>>>S.bip_0340_verify
  result :: t Globals NodeState
  result=((rd>>>T.txid 2 False)&&&oh)&&&(ih>>>ih)
runNode :: forall t. Assert t => t NodeState LeafState
runNode=(sig&&&result)>>>ih
 where
  root :: t NodeState Word256
  root=oh>>>ih>>>oh
  leafA :: t NodeState Word256
  leafA=oh>>>ih>>>ioh
  leafB :: t NodeState Word256
  leafB=oh>>>ih>>>iioh
  forfeit :: t NodeState Word256
  forfeit=oh>>>ih>>>ih>>>ih>>>ih>>>oh
  leafHash :: t NodeState Word256
  leafHash=oh>>>ih>>>ih>>>ih>>>ih>>>ih
  nd :: t NodeState T.TxData
  nd=frame ooh 0(P.newValue+P.otherValue)root 0(out P.newValue leafA)(out P.otherValue leafB)
  sig :: t NodeState()
  sig=((root&&&((nd&&&konst(w256 0))>>>T.defaultMessage 2 True False))&&&ioh)>>>S.bip_0340_verify
  result :: t NodeState LeafState
  result=((nd>>>T.txid 2 True)&&&(leafA&&&(forfeit&&&leafHash)))&&&(ih>>>ih)
runLeaf :: forall t. Assert t => t LeafState(Word256,Sig)
runLeaf=(sig&&&(forfeit&&&iih))>>>ih
 where
  leafA :: t LeafState Word256
  leafA=oh>>>ih>>>oh
  forfeit :: t LeafState Word256
  forfeit=oh>>>ih>>>ih>>>oh
  leafHash :: t LeafState Word256
  leafHash=oh>>>ih>>>ih>>>ih
  leafData :: t LeafState T.TxData
  leafData=frame ooh 0 P.newValue leafA 0(out P.newValue(konst(w256(R.xOnly P.newExit))))zeroOut
  sig :: t LeafState()
  sig=((konst(w256(R.xOnly P.newAggregate))&&&((leafData&&&leafHash)>>>T.defaultMessage 1 True True))&&&ioh)>>>S.bip_0340_verify
runForfeit :: Assert t => t(Word256,Sig)()
runForfeit=(((konst(w256(R.xOnly P.oldExit))&&&((forfeitData&&&konst(w256 0))>>>T.defaultMessage 1 True False))&&&ih)>>>S.bip_0340_verify)
 where
  forfeitData=frame(konst(w256FromBytes(rawOutpoint P.oldPoint)))0 P.oldValue(konst(w256(R.xOnly P.oldExit)))0xffffffff(out P.oldValue oh)zeroOut
arkProof :: (Simplicity t,Primitive t) => Proof -> t()()
arkProof proof=witness proof>>>arkKernel
arkKernel :: (Assert t,Primitive t) => t Proof()
arkKernel=((heightCheck&&&iden)>>>ih)>>>prepare>>>globals>>>runRound>>>runNode>>>runLeaf>>>runForfeit
 where
  heightCheck=(((konst(w32(P.tip+2*P.exitMargin+P.exitDelta))&&&oh)>>>Arith.le word32>>>verify)
   &&&((konst(w32 65536)&&&oh)>>>Arith.le word32>>>verify)
   &&&((oh&&&konst(w32(2^23)))>>>Arith.lt word32>>>verify))>>>unit
pointW(Just(x,y))=(w256 x,w256 y)
pointW Nothing=error "infinite hArk parameter"
outpointW(Outpoint h i)=(w256FromBytes(hashToBytes h),w32(toInteger i))
rawOutpoint(Outpoint h _)=hashToBytes h
sigW raw=(w256FromBytes(B.take 32 raw),w256FromBytes(B.drop 32 raw))
proofW p=case map sigW(P.pkgSignatures p)of
 [a,b,c,d]->(w32(P.pkgHeight p),(w256FromBytes(P.pkgPreimage p),(a,(b,(c,d)))))
 _->error "hArk four certificate signatures"
entry :: IO Entry
entry=return(Entry "app-ark-round-refresh"
 "Current Bark hArk complete two-leaf refresh certificate: real Taproot round/tree/leaf/forfeit, shared unlock and actual BIP341 signatures"
 "Bark5a7dbf9f2cd64dcdb65e3465080727e24dfe111d lib/{tree/signed,forfeit,vtxo/policy,musig}.rs and wallet round validation; MIT"
 BitcoinApp(Derived "Four actual standard Bitcoin wire transactions, current hArk scripts and MuSig2-derived keys; reference reproduces published eight-key Bark round output and official BIP341 DEFAULT vector")
 ["CLIENT COMPLETION CERTIFICATE: verifies current hArk round R->node D->user leaf L and old-VTXO->forfeit F; does not replace the interactive coordinator/nonce database or claim an onchain Simplicity spend",
  "Authenticated client supplies actual round primitive environment, prior old/liquidity UTXO state, negotiated two-leaf requests, setup/cosign keys and trusted chain tip800000; synthetic fixture outpoints are not livechain evidence",
  "Actual current Taproot/MuSig2-derived keypath and scriptpath DEFAULT signatures; sorted aggregate setup keys are fixed authenticated parameters, while every expiry/unlock-dependent Taproot output is computed in Simplicity",
  "Current hArk HashSign uses actual RIPEMD160(SHA256(preimage)), OP_SIZE32 and the exact script hash; same checked preimage drives the user's new leaf and conditional forfeit output; no independent witness reopening",
  "New expiry has minimal three-byte Script-number bound65536..2^23-1 and must satisfy trusted_tip+2*exit_margin+old_exit_delta; margin144/oldCSV144; chain monitoring and timely exits remain required",
  "Round input100000; actual tree79000 and server change20000;1000-sat round fee. Tree creates new49000/other30000 leaves; leaf preserves49000; forfeit preserves old50000 with userCSV recovery and serverhashclaim; version3 P2A zero anchors exactly follow current Bark templates",
  "Every R->D->L txid/outpoint/value/script and all four final aggregate signatures checked. Final signature validity is checked, not partial MuSig2 nonce/session exchange; fresh cosign key deletion remains setup assumption",
  "Canonical decoded certificate reconstructs real Bitcoin transactions and scriptpath control block; transport parsing, full old VTXO genesis, round confirmation/fork choice and external UTXO authentication are client boundaries",
  "Published seven-leaf serialization fixtures are outside this bounded two-leaf certificate; no downloaded Rust is executed and no whole interactive-protocol fairness proof is claimed"]
 (boundProgram arkKernel)vectors)
 where
  package height mutation=P.makePackage height(B.replicate 32 0x41)mutation
  good=package 802016 P.Honest
  vector name p expected=Vector name(mkEnv(P.pkgRound p)0 defaultTap)(proofW p)expected
  (height,(preimage,(a,(b,(c,d)))))=proofW good
  env=mkEnv(P.pkgRound good)0 defaultTap
  vectors=[vector "complete current hArk four-transaction certificate" good Accept,
   vector "fresh certificate at exact safe expiry-margin boundary"(package(P.tip+2*P.exitMargin+P.exitDelta)P.Honest)Accept,
   vector "fresh valid signatures but substituted round tree script"(package 802016 P.WrongRoundScript)Reject,
   vector "fresh valid signatures but wrong authenticated round input value"(package 802016 P.WrongRoundValue)Reject,
   vector "fresh valid package but wrong requested new amount"(package 802016 P.WrongNewAmount)Reject,
   vector "fresh valid node signature but wrong round link"(package 802016 P.WrongNodeLink)Reject,
   vector "fresh valid leaf signature but wrong node link"(package 802016 P.WrongLeafLink)Reject,
   vector "fresh valid forfeit signature but different unlock hash"(package 802016 P.WrongForfeitHash)Reject,
   vector "fresh valid forfeit signature but wrong prior VTXO"(package 802016 P.WrongForfeitInput)Reject,
   vector "fresh valid leaf signature but diverted new owner"(package 802016 P.WrongLeafOwner)Reject,
   vector "fresh complete package one block below safe expiry margin"(package(P.tip+2*P.exitMargin+P.exitDelta-1)P.Honest)Reject,
   Vector "preimage changes at its single proof occurrence" env(height,(w256 1,(a,(b,(c,d)))))Reject,
   Vector "node and forfeit certificate signatures exchanged" env(height,(preimage,(a,(d,(c,b)))))Reject,
   Vector "noncanonical final leaf signature scalar n" env(height,(preimage,(a,(b,((fst c,w256 R.n),d)))))Reject]
