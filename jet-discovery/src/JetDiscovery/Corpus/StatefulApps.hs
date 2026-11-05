{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Stateful native-BTC applications. A single input serializes each pool's
-- state; all continuation roots, amounts and destinations are checked in-script.
module JetDiscovery.Corpus.StatefulApps (entries,counter) where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Bits as Bits
import Data.Bits (testBit,setBit)
import Data.Serialize (runPut,putWord64be)
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg,checkSigWith)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.Kernels (sha256Pair)
import JetDiscovery.Lib.State
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R

type SigW=(Word256,Word256)
type Path=((Bit,Word256),(Bit,Word256))
type Proof=(Word256,(Word64,Path))
type RefProof=(Integer,Integer,[(Bool,BS.ByteString)])
keys=[17,29,41,53] :: [Integer]
pks=map R.pubkeyOf keys
other=unhex "0014"<>BS.replicate 20 0xdd
be64 n=runPut (putWord64be (fromInteger n))
leafRef (pk,b)=R.taggedHash "Simplicity/Pool/Leaf" (R.bytesFromInt pk<>be64 b)
pairRef a b=hashToBytes (sha256 (a<>b))
rootRef leaves=let [a,b,c,d]=map leafRef leaves in pairRef (pairRef a b) (pairRef c d)
proofRef leaves i=(fst (leaves!!i),snd (leaves!!i),[(odd i,hs!!(i `Bits.xor`1)),(testBit i 1,parents!!((i`div`2)`Bits.xor`1))])
 where hs=map leafRef leaves;parents=[pairRef (hs!!0) (hs!!1),pairRef (hs!!2) (hs!!3)]
proofW (pk,b,[(d0,h0),(d1,h1)])=(w256 pk,(w64 b,((bitW d0,w256FromBytes h0),(bitW d1,w256FromBytes h1))))
proofW _=error "two-level proof"
bitW b=if b then Right () else Left ()
replace i b xs=[if j==i then (pk,b) else (pk,v)|(j,(pk,v))<-zip [0..] xs]

add64 a b=(a&&&b)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
sub64 a b=(a&&&b)>>>A.subtract word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
outVal i=konst (w32 i)>>>primitive Prim.OutputValue>>>verify
outScript i=konst (w32 i)>>>primitive Prim.OutputScriptHash>>>verify
count n=((unit>>>Tx.numOutputs)&&&konst (w32 n))>>>eq>>>verify
same a b=(a&&&b)>>>eq>>>verify
outAmount i x=same (outVal i) x
outKey i key=same (outScript i) (((unit>>>ctx8Init)&&&konst (w16 0x5120)>>>ctx8Add2)&&&key>>>ctx8Add32>>>ctx8Finalize)
continue new value=(same (outScript 0) (stateScriptHash new)&&&outAmount 0 value)>>>unit

leaf :: Assert t => t (Word256,Word64) Word256
leaf=(((unit>>>ctx8InitTag "Simplicity/Pool/Leaf")&&&oh>>>ctx8Add32)&&&ih)>>>ctx8Add8>>>ctx8Finalize
node :: (Assert t,TyC a) => t a Word256 -> t a (Bit,Word256) -> t a Word256
node h p=((p>>>oh)&&&(h&&&(p>>>ih)))>>>cond ((ih&&&oh)>>>sha256Pair) sha256Pair
proofRootWith :: Assert t => t Proof Word64 -> t Proof Word256
proofRootWith balance=proofRootOn iden balance
proofRootOn :: (Assert t,TyC a) => t a Proof -> t a Word64 -> t a Word256
proofRootOn p balance=node (node (((p>>>oh)&&&balance)>>>leaf) (p>>>iioh)) (p>>>iiih)
proofRoot :: Assert t => t Proof Word256
proofRoot=proofRootWith ioh

poolExit :: (Simplicity t,Primitive t) => (Proof,SigW) -> t () ()
poolExit w=witness w>>>poolExitT
poolExitT :: (Simplicity t,Primitive t) => t (Proof,SigW) ()
poolExitT=(loadState old&&&authorized&&&count 2&&&continue new remaining&&&outAmount 1 balance&&&outKey 1 owner)>>>unit
 where
  p=oh;old=p>>>proofRoot;owner=p>>>oh;balance=p>>>ioh
  new=proofRootOn p (konst (w64 0))
  remaining=sub64 (unit>>>Tx.currentValue) balance
  authorized=((owner&&&(unit>>>sigMsg))&&&ih)>>>Secp.bip_0340_verify

poolDeposit :: (Simplicity t,Primitive t) => (Proof,Word64) -> t () ()
poolDeposit w=witness w>>>poolDepositT
poolDepositT :: (Simplicity t,Primitive t) => t (Proof,Word64) ()
poolDepositT=(loadState old&&&empty&&&positive&&&count 1&&&continue new amount)>>>unit
 where
  p=oh;d=ih;old=p>>>proofRoot
  empty=same (p>>>ioh) (konst (w64 0))
  positive=((konst (w64 0)&&&d)>>>A.lt word64)>>>verify
  new=proofRootOn p d
  amount=add64 (unit>>>Tx.currentValue) d

poolTransfer :: (Simplicity t,Primitive t) => ((Proof,Proof),(Word64,SigW)) -> t () ()
poolTransfer w=witness w>>>poolTransferT
poolTransferT :: (Simplicity t,Primitive t) => t ((Proof,Proof),(Word64,SigW)) ()
poolTransferT=(loadState old&&&positive&&&authorized&&&intermediateOk&&&count 1&&&continue new (unit>>>Tx.currentValue))>>>unit
 where
  s=take oh;r=take ih;a=drop oh
  old=s>>>proofRoot
  senderBal=sub64 (s>>>ioh) a
  intermediate=proofRootOn s senderBal
  intermediateOk=same intermediate (r>>>proofRoot)
  receiverBal=add64 (r>>>ioh) a
  new=proofRootOn r receiverBal
  positive=((konst (w64 0)&&&a)>>>A.lt word64)>>>verify
  authorized=(((s>>>oh)&&&(unit>>>sigMsg))&&&(drop ih))>>>Secp.bip_0340_verify

-- A full Merkle-distributor payout with an evolving claimed bitmap. Its
-- authenticated leaves commit index, beneficiary public key and amount.
type Coupon=(Word8,(Word256,(Word64,Path)))
couponLeaf :: Assert t => t (Word8,(Word256,Word64)) Word256
couponLeaf=((((unit>>>ctx8InitTag "Simplicity/Coupon")&&&oh>>>ctx8Add1)&&&ioh>>>ctx8Add32)&&&iih)>>>ctx8Add8>>>ctx8Finalize
couponRoot :: Assert t => t Coupon Word256
couponRoot=node (node ((oh&&&(ioh&&&iioh))>>>couponLeaf) (drop (drop (drop oh)))) (drop (drop (drop ih)))
couponRef (i,pk,amount)=R.taggedHash "Simplicity/Coupon" (BS.singleton (fromInteger i)<>R.bytesFromInt pk<>be64 amount)
couponLeaves=[(toInteger i,pks!!i,1000*(toInteger i+1))|i<-[0..3]]
couponHashes=map couponRef couponLeaves
couponRootRef=pairRef (pairRef (couponHashes!!0) (couponHashes!!1)) (pairRef (couponHashes!!2) (couponHashes!!3))
couponProof i=(toInteger i,(pks!!i,(1000*(toInteger i+1),[(odd i,couponHashes!!(i`Bits.xor`1)),(testBit i 1,parents!!((i`div`2)`Bits.xor`1))])))
 where parents=[pairRef (couponHashes!!0) (couponHashes!!1),pairRef (couponHashes!!2) (couponHashes!!3)]
couponW (i,(pk,(v,[(d0,h0),(d1,h1)])))=(w8 i,(w256 pk,(w64 v,((bitW d0,w256FromBytes h0),(bitW d1,w256FromBytes h1)))))
couponW _=error "coupon proof"
coupon :: (Simplicity t,Primitive t) => (Word256,Coupon) -> t () ()
coupon w=witness w>>>couponT
couponT :: (Simplicity t,Primitive t) => t (Word256,Coupon) ()
couponT=(loadState bits&&&membership&&&unclaimed&&&count 2&&&continue new remaining&&&outAmount 1 amount&&&outKey 1 owner)>>>unit
 where
  p=ih;bits=oh
  membership=same (p>>>couponRoot) (konst (w256FromBytes couponRootRef))
  -- Finite index range; no unchecked shift or high-bit truncation.
  mask=L.foldr (\i rest->(((p>>>oh)&&&konst (w8 i))>>>eq)&&&iden>>>cond (konst (w256 (2^i))) rest) failure [0..3]
  unclaimed=same ((bits&&&mask)>>>W.bitwise_and word256) (konst (w256 0))
  new=(bits&&&mask)>>>W.bitwise_or word256
  amount=p>>>iioh;owner=p>>>ioh
  remaining=sub64 (unit>>>Tx.currentValue) amount

-- Published bytes32 storage example: the low64-bit counter increments while
-- the other192 bits are preserved. Complete storage transition, not a wallet.
counter :: (Simplicity t,Primitive t) => Word256 -> t () ()
counter old=witness old>>>counterT
counterT :: (Simplicity t,Primitive t) => t Word256 ()
counterT=(loadState value&&&count 1&&&continue new (unit>>>Tx.currentValue))>>>unit
 where
  value=iden
  low=value>>>iih
  updated=(low&&&konst (w64 1))>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
  new=(value>>>oh)&&&((value>>>ioh)&&&updated)

sigW (Sig r s)=(w256 (toInteger r),w256 (toInteger s))
zeroSig=(w256 0,w256 0)
signFor sk prog makeEnv=case makeEnv (progCmr prog) >>= (\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of
 Just msg->sigW (signMsg sk (w256ToBytes msg));_->error "stateful signature environment"

-- An unrelated second input pays the fee, so claim balances do not silently
-- lose collateral on internal transfers or state updates.
stateEnv old value feeInput outs cmr=mkEnv transaction 0 (\_->stateTap cmr old) cmr
 where
  script=stateScript cmr old
  transaction=mkTx 2 [mkInput (dummyOutpoint 0) (fromInteger value) (BL.fromStrict script) 0xfffffffe,mkInput (dummyOutpoint 1) (fromInteger feeInput) (BL.fromStrict other) 0xfffffffe]
    [mkOutput (fromInteger v) s|(v,s)<-outs cmr] 0
stateOut dat value cmr=(value,stateScript cmr dat)

entries :: [Entry]
entries=[exitEntry,depositEntry,transferEntry,couponEntry,counterEntry]
 where
  leaves=zip pks [40000,30000,20000,10000]
  old=rootRef leaves
  -- Exit consumes the full authenticated claim and zeroes its leaf.
  exitP w=Prog (poolExit w)
  exitProof=proofW (proofRef leaves 1)
  exited=rootRef (replace 1 0 leaves)
  exitEnv value dest root=stateEnv old 100000 1000 (\cmr->[stateOut root value cmr,(30000,dest)])
  goodExit=exitEnv 70000 (unhex "5120"<>R.bytesFromInt (pks!!1)) exited
  exitSig sk e=signFor sk (exitP (exitProof,zeroSig)) e
  exitEntry=Entry "app-payment-pool-merkle-exit" "Authenticated payment-pool exit with collateral conservation" "CoinPool withdrawal/state-commitment pattern https://coinpool.dev/coinpool.pdf; native Bitcoin internal-key state commitment"
   BitcoinApp (Derived "independent four-leaf SHA256 tree, checked subtraction, transaction-bound BIP340 signatures; external input pays the fee")
   ["one full exit transition: authenticated claim is zeroed, claim value pays its committed key, and all other collateral remains in the continuing state", "four fixed leaves; depth2; no global account ledger or consensus jet is added"]
   (\w->exitP w)
   [Vector "member exits30000" goodExit (exitProof,exitSig (keys!!1) goodExit) Accept,
    Vector "wrong signer" goodExit (exitProof,exitSig (keys!!0) goodExit) Reject,
    Vector "remaining collateral short" (exitEnv 69999 (unhex "5120"<>R.bytesFromInt (pks!!1)) exited) (exitProof,exitSig (keys!!1) (exitEnv 69999 (unhex "5120"<>R.bytesFromInt (pks!!1)) exited)) Reject,
    Vector "claim redirected" (exitEnv 70000 other exited) (exitProof,exitSig (keys!!1) (exitEnv 70000 other exited)) Reject,
    Vector "old state replayed as continuation" (exitEnv 70000 (unhex "5120"<>R.bytesFromInt (pks!!1)) old) (exitProof,exitSig (keys!!1) (exitEnv 70000 (unhex "5120"<>R.bytesFromInt (pks!!1)) old)) Reject]
  -- Deposit inserts a funded claim into a proven zero-balance slot.
  emptyLeaves=zip pks [40000,30000,30000,0]
  emptyRoot=rootRef emptyLeaves
  depProof=proofW (proofRef emptyLeaves 3)
  credited=rootRef (replace 3 10000 emptyLeaves)
  depositEnv amount root=stateEnv emptyRoot 100000 11000 (\cmr->[stateOut root amount cmr])
  depositEntry=Entry "app-payment-pool-funded-deposit" "Funded insertion into an authenticated empty payment-pool slot" "CoinPool shared UTXO state transitions https://coinpool.dev/coinpool.pdf; bounded append-slot adaptation"
   BitcoinApp (Derived "independent SHA256 tree and actual additional funding input; positive/empty-slot/conservation negatives")
   ["one full deposit transition: zero-balance leaf becomes a positive funded claim; output value increases by exactly that amount", "consensus validates additional funding-input authorization and conservation; this program verifies the pool input"]
   (\(p,a)->Prog (poolDeposit (p,w64 a)))
   [Vector "funded10000 claim" (depositEnv 110000 credited) (depProof,10000) Accept,
    Vector "continuation not funded" (depositEnv 109999 credited) (depProof,10000) Reject,
    Vector "state root not updated" (depositEnv 110000 emptyRoot) (depProof,10000) Reject,
    Vector "zero deposit" (depositEnv 100000 emptyRoot) (depProof,0) Reject,
    Vector "occupied leaf" (stateEnv old 100000 11000 (\cmr->[stateOut credited 110000 cmr])) (proofW (proofRef leaves 1),10000) Reject]
  -- Two sequential proofs enforce both sides of an internal transfer.
  senderProof=proofW (proofRef leaves 0)
  debitedLeaves=replace 0 35000 leaves
  receiverProof=proofW (proofRef debitedLeaves 2)
  transferred=rootRef (replace 2 25000 debitedLeaves)
  transferP ((s,r),(a,sig))=Prog (poolTransfer ((s,r),(w64 a,sig)))
  transferEnv root value=stateEnv old 100000 1000 (\cmr->[stateOut root value cmr])
  goodTransfer=transferEnv transferred 100000
  trSig sk e=signFor sk (transferP ((senderProof,receiverProof),(5000,zeroSig))) e
  transferEntry=Entry "app-payment-pool-internal-transfer" "Two-proof payment-pool internal balance transfer" "CoinPool internal-transfer pattern https://coinpool.dev/coinpool.pdf; sequential authenticated Merkle updates"
   BitcoinApp (Derived "independent sender-debit then receiver-credit tree; signature binds actual transaction; collateral preserved exactly")
   ["one complete transfer transition: sender signature, positive amount, no underflow/overflow, receiver proof against the intermediate root", "four fixed leaves/depth2; an external input pays the fee so the claims remain fully collateralized"]
   (\w->transferP w)
   [Vector "transfer5000 from0 to2" goodTransfer ((senderProof,receiverProof),(5000,trSig (keys!!0) goodTransfer)) Accept,
    Vector "wrong sender signature" goodTransfer ((senderProof,receiverProof),(5000,trSig (keys!!1) goodTransfer)) Reject,
    Vector "receiver proof from stale root" goodTransfer ((senderProof,proofW (proofRef leaves 2)),(5000,trSig (keys!!0) goodTransfer)) Reject,
    Vector "collateral removed" (transferEnv transferred 99999) ((senderProof,receiverProof),(5000,trSig (keys!!0) (transferEnv transferred 99999))) Reject,
    Vector "overdraw sender" goodTransfer ((senderProof,receiverProof),(40001,trSig (keys!!0) goodTransfer)) Reject]
  -- Coupon campaign uses a fixed eligibility root and authenticated bitmap.
  coup=couponW (couponProof 2)
  couponEnv bitmap next value dest=stateEnv (R.bytesFromInt bitmap) 100000 1000 (\cmr->[stateOut (R.bytesFromInt next) value cmr,(3000,dest)])
  couponEntry=Entry "app-merkle-distributor-bitmap" "One-time Merkle-distributor native BTC claim with bitmap state" "Uniswap MerkleDistributor claimedBitMap pattern https://github.com/Uniswap/merkle-distributor/blob/master/contracts/MerkleDistributor.sol; SHA256/BIP340-key leaf adaptation"
   BitcoinApp (Derived "independent eligibility Merkle tree; index/key/amount committed in each leaf; bitmap transitions and actual payouts checked")
   ["four eligible claims; index0..3; root constant, evolving bitmap committed in the continuing internal key", "anyone may submit a proof; payout is forced to the leaf's beneficiary key; a separate input pays the fee"]
   (\(b,p)->Prog (coupon (w256 b,p)))
   [Vector "claim index2" (couponEnv 0 4 97000 (unhex "5120"<>R.bytesFromInt (pks!!2))) (0,coup) Accept,
    Vector "already claimed" (couponEnv 4 4 97000 (unhex "5120"<>R.bytesFromInt (pks!!2))) (4,coup) Reject,
    Vector "bitmap not advanced" (couponEnv 0 0 97000 (unhex "5120"<>R.bytesFromInt (pks!!2))) (0,coup) Reject,
    Vector "payout diverted" (couponEnv 0 4 97000 other) (0,coup) Reject,
    Vector "remaining collateral short" (couponEnv 0 4 96999 (unhex "5120"<>R.bytesFromInt (pks!!2))) (0,coup) Reject]
  counterEnv oldVal newVal=stateEnv (R.bytesFromInt oldVal) 100000 1000 (\cmr->[stateOut (R.bytesFromInt newVal) 100000 cmr])
  counterEntry=Entry "app-native-state-counter" "Native Bitcoin authenticated bytes32 storage counter" "Pinned simplicity-contracts bytes32_tr_storage.simf; internal-key commitment adaptation replaces TapData sibling"
   BitcoinApp (Derived "old/new state roots constructed independently with Integer secp256k1 arithmetic; full value-preserving storage output")
   ["complete storage transition, not a financial wallet; increments low64 bits, preserves upper192, rejects overflow", "single executable leaf with no siblings; all state/continuation key calculations execute inside Simplicity"]
   (\oldVal->Prog (counter (w256 oldVal)))
   [Vector "increment state" (counterEnv (2^128+41) (2^128+42)) (2^128+41) Accept,
    Vector "wrong next state" (counterEnv 41 43) 41 Reject,
    Vector "wrong old state witness" (counterEnv 41 42) 40 Reject,
    Vector "low64-bit overflow" (counterEnv (2^64-1) 0) (2^64-1) Reject]
