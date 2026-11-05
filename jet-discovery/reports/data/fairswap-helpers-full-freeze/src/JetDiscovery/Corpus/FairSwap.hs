{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Native post-funding FairSwap lifecycle with complete bounded complaint
-- verification. Fixed circuit wiring follows formal Judge Algorithm8 rather
-- than the early prototype's attacker-selected input/output indices.
module JetDiscovery.Corpus.FairSwap(entries,SaleW,saleT,openingRoot,stateT,referenceAudit)where
import Prelude hiding(drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as BL
import qualified Data.Word as DW
import Data.Bits(testBit,xor)
import Simplicity.Digest(Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit hiding(xor)
import Simplicity.Programs.Generic(eq)
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term(Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Corpus.Apps(sigMsg,checkSigWith)
import JetDiscovery.Corpus.ContractExpansion(keccakFixed)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import JetDiscovery.Run(progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Bip
import qualified JetDiscovery.Ref.FairSwap as R
import JetDiscovery.Ref.Keccak(keccak256)
type Header=(Word256,(Word256,Word256))
type Sig=(Word256,Word256)
type Opening=(Word256,(Word256,(Word256,Word256)))
type Gate=(Opening,(Opening,Opening))
type Proof=Either Opening(Either Gate(Either Gate Gate))
type Accepted=Either(Word256,Sig)()
type Revealed=Either Sig(Either()(Sig,Proof))
type Action=Either Accepted(Word256,Revealed)
type SaleW=(Header,Action)
type Env=Hash256 -> Maybe Prim.PrimEnv
pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t(a,a)b
pick True=drop
pick False=take
byte256 :: Core t => Int -> t Word256 Word8
byte256 i=pick(testBit i 4)(pick(testBit i 3)(pick(testBit i 2)(pick(testBit i 1)(pick(testBit i 0)iden))))
bytes32 :: (Core t,TyC a) => t a Word256 -> [t a Word8]
bytes32 x=[x>>>byte256 i|i<-[0..31]]
{-# NOINLINE hash32Wrapped #-}
hash32Wrapped :: J.WrappedSimplicity Word256 Word256
hash32Wrapped=J.jetSubst(keccakFixed(bytes32 iden))
{-# NOINLINE hash64Wrapped #-}
hash64Wrapped :: J.WrappedSimplicity(Word256,Word256)Word256
hash64Wrapped=J.jetSubst(keccakFixed(bytes32 oh++bytes32 ih))
hash32 :: Simplicity t => t Word256 Word256
hash32=J.unwrap hash32Wrapped
hash64 :: Simplicity t => t(Word256,Word256)Word256
hash64=J.unwrap hash64Wrapped
same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b=(a&&&b)>>>eq>>>verify
ordered :: (Core t,TyC a) => Bool -> t(a,a)(a,a)
ordered True=ih&&&oh
ordered False=iden
-- Consume each sibling exactly once while preserving its authenticated node.
openingRoot :: Simplicity t => Int -> t Opening Word256
openingRoot i=(leaf&&&ih)>>>
 (((oh&&&ioh)>>>ordered(testBit i 0)>>>hash64)&&&iih)>>>
 (((oh&&&ioh)>>>ordered(testBit i 1)>>>hash64)&&&iih)>>>
 ordered(testBit i 2)>>>hash64
 where leaf=if i<4 then oh>>>hash32 else oh
decrypt :: (Simplicity t,TyC a) => Int -> t a Word256 -> t a Word256 -> t a Word256
decrypt i ciphertext key=(ciphertext&&&((konst(w256(toInteger domain))&&&key)>>>hash64))>>>W.bitwise_xor word256
 where domain=if i<4 then i else 4+i
stateT :: Assert t => Integer -> t(Header,Word256)Word256
stateT phase=(iden&&&(((unit>>>ctx8Init)&&&konst(toWord128(Bip.intFromBytes(C.pack "FairSwapNativeV1"))))>>>ctx8Add16))>>>
 (oh&&&((ih&&&konst(w8 phase))>>>ctx8Add1))>>>
 (oh&&&((ih&&&headerCommit)>>>ctx8Add32))>>>
 (oh&&&((ih&&&headerCipherRoot)>>>ctx8Add32))>>>
 (oh&&&((ih&&&headerFileRoot)>>>ctx8Add32))>>>
 ((ih&&&oih)>>>ctx8Add32)>>>ctx8Finalize
-- Typed projections in stateT's carried input ((Header,key),Ctx8).
headerCommit :: Core t => t((Header,Word256),Ctx8)Word256
headerCommit=take(take oh)
headerCipherRoot :: Core t => t((Header,Word256),Ctx8)Word256
headerCipherRoot=take(take ioh)
headerFileRoot :: Core t => t((Header,Word256),Ctx8)Word256
headerFileRoot=take(take iih)
seller=17;buyer=29
sellerScript=unhex "5120"<>Bip.bytesFromInt(Bip.pubkeyOf seller)
buyerScript=unhex "5120"<>Bip.bytesFromInt(Bip.pubkeyOf buyer)
scriptHash=w256FromBytes.hashToBytes.sha256
outValue :: (Assert t,Primitive t,TyC a) => t a Word64
outValue=konst(w32 0)>>>primitive Prim.OutputValue>>>verify
outScript :: (Assert t,Primitive t,TyC a) => t a Word256
outScript=konst(w32 0)>>>primitive Prim.OutputScriptHash>>>verify
pay :: (Assert t,Primitive t,TyC a) => B.ByteString -> t a ()
pay destination=(same outValue(konst(w64 100000))&&&same outScript(konst(scriptHash destination)))>>>unit
delay :: (Assert t,Primitive t,TyC a) => t a ()
delay=konst(w16 10)>>>TL.checkLockDistance
signature :: (Simplicity t,Primitive t,TyC a) => Integer -> t a Sig -> t a ()
signature sk sig=checkSigWith(w256(Bip.pubkeyOf sk))(unit>>>sigMsg)sig
-- Witness-free relation; every shared header/key/proof flows through projections.
saleT :: forall t. (Simplicity t,Primitive t) => t SaleW ()
saleT=(policy&&&iden)>>>ih>>>(ih&&&oh)>>>match accepted revealed
 where
  policy=(same(unit>>>Tx.numInputs)(konst(w32 2))&&&same(unit>>>Tx.numOutputs)(konst(w32 1))&&&same(unit>>>Tx.currentValue)(konst(w64 100000)))>>>unit
  accepted :: t(Accepted,Header)()
  accepted=(loadState((ih&&&konst(w256 0))>>>stateT 0)&&&iden)>>>ih>>>match reveal refund
  reveal :: t((Word256,Sig),Header)()
  reveal=(same(ooh>>>hash32)(ioh)&&&signature seller oih&&&
    same outValue(konst(w64 100000))&&&same outScript(stateScriptHash((ih&&&ooh)>>>stateT 1)))>>>unit
  refund :: t((),Header)()
  refund=(delay&&&pay buyerScript)>>>unit
  revealed :: t((Word256,Revealed),Header)()
  revealed=(loadState((ih&&&ooh)>>>stateT 1)&&&same(ooh>>>hash32)(ioh)&&&iden)>>>iih>>>
   (oih&&&(ooh&&&ih))>>>match acknowledge after
  acknowledge :: t(Sig,(Word256,Header))()
  acknowledge=(signature buyer oh&&&pay sellerScript)>>>unit
  after :: t(Either()(Sig,Proof),(Word256,Header))()
  after=match payout complain
  payout :: t((),(Word256,Header))()
  payout=(delay&&&pay sellerScript)>>>unit
  complain :: t((Sig,Proof),(Word256,Header))()
  complain=(signature buyer ooh&&&((oih&&&ih)>>>judge)&&&pay buyerScript)>>>unit
  judge :: t(Proof,(Word256,Header))()
  judge=match root(match(gate 4 0 1)(match(gate 5 2 3)(gate 6 4 5)))
  root :: t(Opening,(Word256,Header))()
  root=(same(oh>>>openingRoot 6)(iih>>>ioh)&&&
    ((decrypt 6 ooh ioh&&&(iih>>>iih))>>>eq>>>not iden>>>verify))>>>unit
  gate :: Int -> Int -> Int -> t(Gate,(Word256,Header))()
  gate output left right=(same(ooh>>>openingRoot output)(iih>>>ioh)&&&
    same(oioh>>>openingRoot left)(iih>>>ioh)&&&same(oiih>>>openingRoot right)(iih>>>ioh)&&&
    ((decrypt output(oh>>>ooh)ioh&&&((decrypt left(oh>>>iooh)ioh&&&decrypt right(oh>>>iioh)ioh)>>>hash64))>>>eq>>>not iden>>>verify))>>>unit
program :: SaleW -> Prog
program=boundProgram saleT
zeroSig=(w256 0,w256 0)
key=Bip.bytesFromInt 991
chunks=[Bip.bytesFromInt i|i<-[10..13]]
ciphers=R.cipherNodes key chunks
honestHeader=R.header key chunks
packHeader(a,(b,c))=(w256FromBytes a,(w256FromBytes b,w256FromBytes c))
packOpening(c,[a,b,d])=(w256FromBytes c,(w256FromBytes a,(w256FromBytes b,w256FromBytes d)))
packOpening _=error "FairSwap requires3Merkle siblings"
packGate cs output left right=(packOpening(R.opening cs output),(packOpening(R.opening cs left),packOpening(R.opening cs right)))
blank=(packHeader honestHeader,Left(Right()))
{-# NOINLINE saleCmr #-}
saleCmr=progCmr(program blank)
-- Every test spends genuine state-script collateral, with a separate fee input.
environment :: R.Header -> B.ByteString -> Bool -> DW.Word32 -> B.ByteString -> Integer -> Env
environment hdr currentKey phase sequence destination amount cmr=mkEnv tx 0(\_->stateTap cmr oldState)cmr
 where
  oldState=R.stateBytes(if phase then 1 else 0)hdr currentKey
  tx=mkTx 2[mkInput(dummyOutpoint 0)100000(BL.fromStrict(stateScript cmr oldState))sequence,
             mkInput(dummyOutpoint 1)1000 BL.empty sequence]
    [mkOutput(fromInteger amount)destination]0
revealEnv hdr supplied sequence cmr=environment hdr(B.replicate 32 0)False sequence
 (stateScript cmr(R.stateBytes 1 hdr supplied))100000 cmr
signed sk env=case env saleCmr of
 Just e->case J.fastEval(J.unwrap(J.jetSubst sigMsg))e()of
  Just msg->let s=Bip.sign sk(w256ToBytes msg)(B.replicate 32 0)in(w256FromBytes(B.take 32 s),w256FromBytes(B.drop 32 s))
  _->error "FairSwap native sig_all_hash"
 _->error "FairSwap environment"
referenceAudit=R.audit
entries :: [Entry]
entries=[Entry "app-fairswap-file-sale" "Native FairSwap funded file-sale lifecycle and complete bounded fraud judge"
 "Eckey dissertation chapter5 Algorithm8/section5.6; lEthDev/FairSwap 07f5664de64e232a0e1a8c0a84eefc223b45ae8b; reports/FAIRSWAP-NATIVE-SCOPE.md"
 BitcoinApp(Derived "independent byte-oriented4chunk circuit/encryption/Merkle/complaint reference; genuine native state outputs and sig_all_hash role authorization")
 ["full post-funding accepted/revealed lifecycle;4x32byte agreed file, fixed7node hash circuit and8leaf ciphertext tree; no extra count for branch/tree/kernel variants",
  "fixed buyer/seller/pricing/CSV10 profile; actual32byte state commitment and same executable leaf; exactly2inputs(one independent fee input),1output,100000sat collateral",
  "all complaint indices/circuit input wiring compile-time fixed; every opening authenticates to the same state-committed ciphertext root; all shared operands enter once",
  "CSV adapts lower deadline eligibility only: late reveal/refund and complaint/payout can race; timely monitoring/response/confirmation required; no strict upper timestamp deadline claim",
  "file delivery, funding/acceptance, credential identity and chain monitoring are external; no Solidity execution or claim that prototype missing wiring is faithfully copied"]
 program vectors]
 where
  acceptEnv=revealEnv honestHeader key 0
  reveal=Vector "accepted seller key reveal" acceptEnv(packHeader honestHeader,Left(Left(w256FromBytes key,signed seller acceptEnv)))Accept
  refundEnv=environment honestHeader(B.replicate 32 0)False 10 buyerScript 100000
  refund=Vector "accepted CSV refund buyer" refundEnv(packHeader honestHeader,Left(Right()))Accept
  ackEnv=environment honestHeader key True 0 sellerScript 100000
  ack=Vector "revealed buyer acknowledgement pays seller" ackEnv(packHeader honestHeader,Right(w256FromBytes key,Left(signed buyer ackEnv)))Accept
  payoutEnv=environment honestHeader key True 10 sellerScript 100000
  payout=Vector "revealed CSV seller payout" payoutEnv(packHeader honestHeader,Right(w256FromBytes key,Right(Left())))Accept
  mkComplaint name hdr cs proof expected=let env=environment hdr key True 0 buyerScript 100000 in
   Vector name env(packHeader hdr,Right(w256FromBytes key,Right(Right(signed buyer env,proof cs))))expected
  rootProof cs=Left(packOpening(R.opening cs 6))
  gate4 cs=Right(Left(packGate cs 4 0 1))
  gate5 cs=Right(Right(Left(packGate cs 5 2 3)))
  gate6 cs=Right(Right(Right(packGate cs 6 4 5)))
  changed i=[if j==i then B.pack(B.zipWith xor c(Bip.bytesFromInt 1))else c|(j,c)<-zip[0..]ciphers]
  fraud name index proof=let cs=changed index;hdr=(fst honestHeader,(R.cipherTree cs,snd(snd honestHeader))) in mkComplaint name hdr cs proof Accept
  shortRefund=environment honestHeader(B.replicate 32 0)False 9 buyerScript 100000
  badPay=environment honestHeader key True 0 buyerScript 100000
  badVal=environment honestHeader key True 0 sellerScript 99999
  wrongProof cs=Right(Left(packGate cs 4 2 3))
  mutateRoot cs=let(c,[a,b,d])=R.opening cs 6 in Left(packOpening(c,[B.pack(B.zipWith xor a(Bip.bytesFromInt 1)),b,d]))
  vectors=[reveal,refund,ack,payout,
   fraud "authenticated wrong root complaint" 6 rootProof,
   fraud "authenticated wrong gate4 complaint" 0 gate4,
   fraud "authenticated wrong gate5 complaint" 2 gate5,
   fraud "authenticated wrong gate6 complaint" 4 gate6]++
   [mkComplaint "honest root complaint rejects" honestHeader ciphers rootProof Reject,
    mkComplaint "honest gate4 complaint rejects" honestHeader ciphers gate4 Reject,
    mkComplaint "honest gate5 complaint rejects" honestHeader ciphers gate5 Reject,
    mkComplaint "honest gate6 complaint rejects" honestHeader ciphers gate6 Reject,
    mkComplaint "prototype unrelated circuit-input false complaint rejects" honestHeader ciphers wrongProof Reject,
    mkComplaint "Merkle sibling corruption rejects" honestHeader ciphers mutateRoot Reject,
    Vector "CSV9 refund rejects" shortRefund(packHeader honestHeader,Left(Right()))Reject,
    Vector "buyer cannot reveal for seller" acceptEnv(packHeader honestHeader,Left(Left(w256FromBytes key,signed buyer acceptEnv)))Reject,
    Vector "wrong revealed key opening rejects" ackEnv(packHeader honestHeader,Right(w256 992,Left(signed buyer ackEnv)))Reject,
    Vector "resigned seller payout diversion rejects" badPay(packHeader honestHeader,Right(w256FromBytes key,Left(signed buyer badPay)))Reject,
    Vector "resigned collateral loss rejects" badVal(packHeader honestHeader,Right(w256FromBytes key,Left(signed buyer badVal)))Reject,
    Vector "wrong key commitment reveal rejects" acceptEnv(packHeader honestHeader,Left(Left(w256 992,signed seller acceptEnv)))Reject,
    Vector "original assertion on changed transaction rejects" badPay(packHeader honestHeader,Right(w256FromBytes key,Left(signed buyer ackEnv)))Reject]
