{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Bounded native collateral state machines inspired by pinned contract
-- specifications. Each logical witness enters once and flows by projections.
module JetDiscovery.Corpus.ContractGrowth where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BC
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Word as DW
import Data.Bits (testBit,(.|.))
import Data.Serialize (runPut,putWord64be)
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg,checkSigWith)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Corpus.ContractExpansion (keccakFixed)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.Keccak as K

type SigW=(Word256,Word256)
type Ledger=Vector16 Word64
type Input=(Word8,((Ledger,Ledger),((Word64,Word64),(SigW,SigW))))
type GW=(Integer,([Integer],[Integer]),(Integer,Integer),(SigW,SigW))
type GT t=t Input ()
type Kernel=forall t. (Simplicity t,Primitive t) => GT t
zeroSig=(w256 0,w256 0)
keys=[1101,2202,3303,4404]
pk i=w256 (R.pubkeyOf (keys H.!! i))
recipient i=unhex "0014"<>BS.replicate 20 (fromIntegral (0x40+i))
scriptHash=w256FromBytes . hashToBytes . sha256
sigW (Sig r s)=(w256 (toInteger r),w256 (toInteger s))
carrier=10000
pad xs=H.take 16 (xs++repeat 0)
ledger xs=case map w64 (pad xs) of
 [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p]->(((a,b),(c,d)),((e,f),(g,h))) `pair` (((i,j),(k,l)),((m,n),(o,p)))
 _->error "ledger16"
 where pair=(,)
encode (m,(a,b),(who,n),s)=(w8 m,((ledger a,ledger b),((w64 who,w64 n),s)))
program :: (Simplicity t,Primitive t) => GT t -> GW -> t () ()
program term w=witness (encode w)>>>term
pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t (a,a) b
pick False=take
pick True=drop
field :: Core t => Int -> t Ledger Word64
field i=pick (testBit i 3) (pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden)))
mode :: Core t => t Input Word8
mode=oh
old,new :: Core t => t Input Ledger
old=drop (take oh)
new=drop (take ih)
actor,amount :: Core t => t Input Word64
actor=drop (drop (take oh))
amount=drop (drop (take ih))
signature,payload :: Core t => t Input SigW
signature=drop (drop (drop oh))
payload=drop (drop (drop ih))
o i=old>>>field i
n i=new>>>field i
k :: (Core t,TyC a) => Integer -> t a Word64
k=konst . w64
same a b=(a&&&b)>>>eq>>>verify
add a b=(a&&&b)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
sub a b=(a&&&b)>>>A.subtract word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
le a b=(a&&&b)>>>A.le word64>>>verify
lt a b=(a&&&b)>>>A.lt word64>>>verify
nonzero a=lt (k 0) a
is a b=(a&&&b)>>>eq
select p a b=(p&&&iden)>>>cond a b
account a b=select (is actor (k 0)) a b
allChecks xs=L.foldl' (\a b->(a&&&b)>>>unit) unit xs
changes xs=allChecks [same (n i) (maybe (o i) id (lookup i xs))|i<-[0..15]]
choose branches=L.foldr (\(m,t) rest->select (is mode (konst (w8 m))) t rest) failure branches
stateHashRef :: Assert t => t Ledger Word256
stateHashRef=L.foldl' (\ctx i->(ctx&&&field i)>>>ctx8Add8) (unit>>>ctx8InitTag "JetDiscovery/ContractGrowth/State") [0..15]>>>ctx8Finalize
stateHashWrapped :: J.WrappedSimplicity Ledger Word256
stateHashWrapped=J.jetSubst stateHashRef
{-# NOINLINE stateHashWrapped #-}
stateHash :: Simplicity t => t Ledger Word256
stateHash=J.unwrap stateHashWrapped
stateRef xs=R.taggedHash "JetDiscovery/ContractGrowth/State" (BS.concat [runPut (putWord64be (fromInteger i))|i<-pad xs])
base :: (Simplicity t,Primitive t) => GT t
base=allChecks [same (unit>>>primitive P.CurrentIndex) (konst (w32 0)),loadState (old>>>stateHash),same (unit>>>Tx.currentValue) (add (o 0) (k carrier)),same (unit>>>Tx.numInputs) (konst (w32 2))]
outVal i=konst (w32 i)>>>primitive P.OutputValue>>>verify
outScript i=konst (w32 i)>>>primitive P.OutputScriptHash>>>verify
outCount v=same (unit>>>Tx.numOutputs) (konst (w32 v))
continuation :: (Simplicity t,Primitive t) => GT t
continuation=allChecks [same (outVal 0) (add (n 0) (k carrier)),same (outScript 0) (stateScriptHash (new>>>stateHash))]
inputFund a=same (konst (w32 1)>>>primitive P.InputValue>>>verify) (add a (k 1000))
noCash :: (Simplicity t,Primitive t) => GT t
noCash=allChecks [outCount 1,inputFund (k 0),continuation]
deposit a=allChecks [nonzero a,outCount 1,inputFund a,continuation]
destination i=konst (scriptHash (recipient i))
actorDestination :: Assert t => t Input Word256
actorDestination=account (destination 0) (destination 1)
withdraw a dest=allChecks [nonzero a,outCount 2,inputFund (k 0),continuation,same (outVal 1) a,same (outScript 1) dest]
sigAt i=checkSigWith (pk i) (unit>>>sigMsg) signature
actorSig :: (Simplicity t,Primitive t) => GT t
actorSig=select (is actor (k 0)) (sigAt 0) (select (is actor (k 1)) (sigAt 1) (same actor (k 2)&&&sigAt 2>>>unit))
twoActor :: Assert t => GT t
twoActor=lt actor (k 2)
nonce i=(i,add (o i) (k 1))
-- Project the192 operand bits before full128-bit arithmetic. This prevents
-- unrelated ledger/signature types from being carried through raw division.
type RatioInput=((Word64,Word64),Word64)
ratioRef :: Assert t => t RatioInput (Word64,Word64)
ratioRef=(nonzero ih&&&fullQR)>>>drop checked
 where
  fullQR=((take (A.multiply word64))&&&(k 0&&&ih))>>>A.div_mod word128
  checked=(same ooh (k 0)&&&same ioh (k 0))&&&(oih&&&iih)>>>ih
ratioWrapped :: J.WrappedSimplicity RatioInput (Word64,Word64)
ratioWrapped=J.jetSubst ratioRef
{-# NOINLINE ratioWrapped #-}
mulDiv up a b d=((a&&&b)&&&d)>>>J.unwrap ratioWrapped>>>rounded
 where
  rounded=select (is ih (k 0)) oh (if up then add oh (k 1) else oh)
floorRatio a b d=mulDiv False a b d
ceilRatio a b d=mulDiv True a b d

-- ERC4626 rounding with one virtual asset and one virtual share. Nontransferable
-- shares are permitted by the standard; exactly two owner accounts are defined.
vaultT :: (Simplicity t,Primitive t) => GT t
vaultT=allChecks [base,valid,twoActor,actorSig,choose [(0,dep),(1,mint),(2,wd),(3,redeem),(4,donate)]]
 where
  assets=o 0;supply=o 1;balance=account (o 2) (o 3)
  valid=allChecks [same supply (add (o 2) (o 3)),allChecks [same (o i) (k 0)|i<-[5..15]]]
  sharesForAssets rounding a=rounding a (add supply (k 1)) (add assets (k 1))
  assetsForShares rounding s=rounding s (add assets (k 1)) (add supply (k 1))
  userBalance b=[(2,account b (o 2)),(3,account (o 3) b)]
  increase a s=allChecks [nonzero s,changes ([(0,add assets a),(1,add supply s),nonce 4]++userBalance (add balance s)),deposit a]
  decrease a s=allChecks [nonzero s,changes ([(0,sub assets a),(1,sub supply s),nonce 4]++userBalance (sub balance s)),withdraw a actorDestination]
  dep=increase amount (sharesForAssets floorRatio amount)
  mint=increase (assetsForShares ceilRatio amount) amount
  wd=decrease amount (sharesForAssets ceilRatio amount)
  redeem=decrease (assetsForShares floorRatio amount) amount
  donate=allChecks [changes [(0,add assets amount),nonce 4],deposit amount]

-- ERC7540 lifecycle: active/economic supply includes claimable deposit shares.
-- Pending requests are escrowed; only an explicit vault authority fulfills them.
asyncT :: (Simplicity t,Primitive t) => GT t
asyncT=allChecks [base,backing,valid,choose [(0,reqD),(1,reqR),(2,fulfillD),(3,fulfillR),(4,claimD False),(5,claimR False),(6,setOp True),(7,setOp False),(8,claimD True),(9,claimR True)]]
 where
  -- field0 is physical assets;1 is active assets;2 economic supply;3/4 user
  -- shares;5/6 pending deposits;7/8 claimable shares;9/10 pending redemptions;
  -- 11/12 claimable native assets;13 operator mask;14 batch;15 state nonce.
  a=o 1;s=o 2
  backing=same (o 0) (add a (add (add (o 5) (o 6)) (add (o 11) (o 12))))
  valid=allChecks [same s (add (add (o 3) (o 4)) (add (add (o 7) (o 8)) (add (o 9) (o 10)))),le (o 13) (k 3)]
  bal x y=account (o x) (o y)
  setAccount x y v=[(x,account v (o x)),(y,account (o y) v)]
  personal=allChecks [twoActor,actorSig]
  reqD=allChecks [personal,changes ([(0,add (o 0) amount),nonce 15]++setAccount 5 6 (add (bal 5 6) amount)),deposit amount]
  reqR=allChecks [personal,nonzero amount,changes ([nonce 15]++setAccount 3 4 (sub (bal 3 4) amount)++setAccount 9 10 (add (bal 9 10) amount)),noCash]
  depositShares x=floorRatio x (add s (k 1)) (add a (k 1))
  redeemAssets x=floorRatio x (add a (k 1)) (add s (k 1))
  d0=depositShares (o 5);d1=depositShares (o 6);r0=redeemAssets (o 9);r1=redeemAssets (o 10)
  fulfillD=allChecks [sigAt 3,nonzero (add (o 5) (o 6)),same (o 7) (k 0),same (o 8) (k 0),changes [(1,add a (add (o 5) (o 6))),(2,add s (add d0 d1)),(5,k 0),(6,k 0),(7,d0),(8,d1),nonce 14,nonce 15],noCash]
  fulfillR=allChecks [sigAt 3,nonzero (add (o 9) (o 10)),changes [(1,sub a (add r0 r1)),(2,sub s (add (o 9) (o 10))),(9,k 0),(10,k 0),(11,add (o 11) r0),(12,add (o 12) r1),nonce 14,nonce 15],noCash]
  bit=account (k 1) (k 2)
  enabled=((o 13&&&bit)>>>W.bitwise_and word64)&&&bit>>>eq>>>verify
  authorization isOp=allChecks [twoActor,if isOp then enabled&&&sigAt 2>>>unit else actorSig]
  claimD isOp=allChecks [authorization isOp,nonzero amount,changes ([nonce 15]++setAccount 7 8 (sub (bal 7 8) amount)++setAccount 3 4 (add (bal 3 4) amount)),noCash]
  claimR isOp=allChecks [authorization isOp,changes ([(0,sub (o 0) amount),nonce 15]++setAccount 11 12 (sub (bal 11 12) amount)),withdraw amount actorDestination]
  setOp enabledFlag=allChecks [personal,changes [(13,if enabledFlag then (o 13&&&bit)>>>W.bitwise_or word64 else (o 13&&&(bit>>>W.complement word64))>>>W.bitwise_and word64),nonce 15],noCash]

-- Ascending auction: bid funds are real inputs, displaced bids become credits,
-- and an authenticated close phase replaces an unavailable upper-time primitive.
auctionT :: (Simplicity t,Primitive t) => GT t
auctionT=allChecks [base,valid,choose [(0,bid),(1,refund),(2,close)]]
 where
  valid=allChecks [le (o 1) (k 1),select (is (o 2) (k 0)) (same (o 3) (k 2)) (lt (o 3) (k 2)),same (o 0) (add (select (is (o 1) (k 0)) (o 2) (k 0)) (add (o 4) (o 5))),allChecks [same (o i) (k 0)|i<-[7..15]]]
  oldCredit0=add (o 4) (select (is (o 3) (k 0)) (o 2) (k 0))
  oldCredit1=add (o 5) (select (is (o 3) (k 1)) (o 2) (k 0))
  bid=allChecks [same (o 1) (k 0),twoActor,actorSig,lt (o 2) amount,changes [(0,add (o 0) amount),(2,amount),(3,actor),(4,oldCredit0),(5,oldCredit1),nonce 6],deposit amount]
  credit=account (o 4) (o 5)
  refund=allChecks [twoActor,actorSig,changes [(0,sub (o 0) credit),(4,account (k 0) (o 4)),(5,account (o 5) (k 0)),nonce 6],withdraw credit actorDestination]
  close=allChecks [sigAt 3,same (o 1) (k 0),changes [(0,sub (o 0) (o 2)),(1,k 1),nonce 6],select (is (o 2) (k 0)) noCash (withdraw (o 2) (destination 3))]

-- Exact packed commitment bytes: uint256 value || bool fake || bytes32 secret.
-- The finite auction has one commitment per each of its two bidder accounts.
wordBytes :: (Core t,TyC a) => t a Word256 -> [t a Word8]
wordBytes w=[w>>>at32 i|i<-[0::Int ..31]]
 where at32 i=pick (testBit i 4) (pick (testBit i 3) (pick (testBit i 2) (pick (testBit i 1) (pick (testBit i 0) iden))))
as256 a=konst (toWord128 0)&&&(k 0&&&a)
wordFromFields source offset=((source>>>field offset)&&&(source>>>field (offset+1)))&&&((source>>>field (offset+2))&&&(source>>>field (offset+3)))
type BlindCommitInput=(Word64,(Word256,Word8))
blindCommitRef :: Assert t => t BlindCommitInput Word256
blindCommitRef=keccakFixed (wordBytes (as256 oh)++[iih]++wordBytes ioh)
blindCommitWrapped :: J.WrappedSimplicity BlindCommitInput Word256
blindCommitWrapped=J.jetSubst blindCommitRef
{-# NOINLINE blindCommitWrapped #-}
commitment :: Simplicity t => t Input Word256
commitment=(amount&&&((payload>>>oh)&&&fakeByte))>>>J.unwrap blindCommitWrapped
-- The fake byte is extracted from its canonical0/1 scalar representation.
fakeByte :: Core t => t Input Word8
fakeByte=payload>>>ih>>>drop (drop (drop (drop (drop iden))))
blindT :: (Simplicity t,Primitive t) => GT t
blindT=allChecks [base,valid,choose [(0,commit),(1,openReveal),(2,reveal),(3,close),(4,refund)]]
 where
  valid=allChecks [le (o 1) (k 2),select (is (o 2) (k 0)) (same (o 3) (k 2)) (lt (o 3) (k 2)),le (o 6) (k 15),same (o 0) (add (o 4) (o 5)),select (is (o 1) (k 0)) (same (o 2) (k 0)&&&le (o 6) (k 3)>>>unit) unit]
  committedBit=account (k 1) (k 2);revealedBit=account (k 4) (k 8)
  has b=(((o 6&&&b)>>>W.bitwise_and word64)&&&b)>>>eq
  no b=has b>>>not iden>>>verify
  depositFor=account (o 4) (o 5)
  replaceCommit value=[(i,account (value>>>fieldWord (i-8)) (o i))|i<-[8..11]]++[(i,account (o i) (value>>>fieldWord (i-12)))|i<-[12..15]]
  fieldWord i=case i of 0->ooh;1->oih;2->ioh;_->iih
  commit=allChecks [same (o 1) (k 0),twoActor,actorSig,no committedBit,changes ([(0,add (o 0) amount),(4,account amount (o 4)),(5,account (o 5) amount),(6,(o 6&&&committedBit)>>>W.bitwise_or word64),nonce 7]++replaceCommit (payload>>>oh)),deposit amount]
  openReveal=allChecks [sigAt 3,same (o 1) (k 0),changes [(1,k 1),nonce 7],noCash]
  offered=account (wordFromFields old 8) (wordFromFields old 12)
  eligible=and (is (payload>>>ih) (konst (w256 0))) ((amount&&&depositFor)>>>A.le word64)
  beats=and eligible ((o 2&&&amount)>>>A.lt word64)
  reveal=allChecks [same (o 1) (k 1),twoActor,actorSig,has committedBit>>>verify,no revealedBit,((payload>>>ih)&&&konst (w256 1))>>>A.le word256>>>verify,same offered commitment,changes ([(2,select beats amount (o 2)),(3,select beats actor (o 3)),(6,(o 6&&&revealedBit)>>>W.bitwise_or word64),nonce 7]++replaceCommit (konst (w256 0))),noCash]
  close=allChecks [sigAt 3,same (o 1) (k 1),changes [(0,sub (o 0) (o 2)),(1,k 2),(4,select (is (o 3) (k 0)) (sub (o 4) (o 2)) (o 4)),(5,select (is (o 3) (k 1)) (sub (o 5) (o 2)) (o 5)),nonce 7],select (is (o 2) (k 0)) noCash (withdraw (o 2) (destination 3))]
  refund=allChecks [same (o 1) (k 2),twoActor,actorSig,has revealedBit>>>verify,changes [(0,sub (o 0) depositFor),(4,account (k 0) (o 4)),(5,account (o 5) (k 0)),nonce 7],withdraw depositFor actorDestination]

gEnv actualOld actualNew funding payout sequence cmr=mkEnv transaction 0 (\_->stateTap cmr (stateRef actualOld)) cmr
 where
  currentScript=stateScript cmr (stateRef actualOld)
  ins=[mkInput (dummyOutpoint 0) (fromInteger (H.head actualOld+carrier)) (BL.fromStrict currentScript) sequence,mkInput (dummyOutpoint 1) (fromInteger (funding+1000)) (BL.fromStrict (recipient 9)) 0xfffffffe]
  outs=mkOutput (fromInteger (H.head actualNew+carrier)) (stateScript cmr (stateRef actualNew)):[mkOutput (fromInteger a) (recipient d)|(d,a)<-maybe [] (:[]) payout]
  transaction=mkTx 2 ins outs 0

vector :: String -> Kernel -> Integer -> [Integer] -> [Integer] -> Integer -> Integer -> Int -> Integer -> Maybe (Int,Integer) -> DW.Word32 -> Expect -> Vector GW
vector name term=vectorBound (cmrOf term) name term
vectorBound :: Hash256 -> String -> Kernel -> Integer -> [Integer] -> [Integer] -> Integer -> Integer -> Int -> Integer -> Maybe (Int,Integer) -> DW.Word32 -> Expect -> Vector GW
vectorBound cmr name term m oldState newState who a signer funding payout sequence expected=vectorPayloadBound cmr name term m oldState newState who a signer zeroSig funding payout sequence expected
vectorPayload :: String -> Kernel -> Integer -> [Integer] -> [Integer] -> Integer -> Integer -> Int -> SigW -> Integer -> Maybe (Int,Integer) -> DW.Word32 -> Expect -> Vector GW
vectorPayload name term=vectorPayloadBound (cmrOf term) name term
cmrOf :: Kernel -> Hash256
cmrOf term=progCmr (Prog (program term empty))
 where empty=(0,(pad [],pad []),(0,0),(zeroSig,zeroSig))
vectorPayloadBound :: Hash256 -> String -> Kernel -> Integer -> [Integer] -> [Integer] -> Integer -> Integer -> Int -> SigW -> Integer -> Maybe (Int,Integer) -> DW.Word32 -> Expect -> Vector GW
vectorPayloadBound cmr name term m oldState newState who a signer extra funding payout sequence expected=Vector name env signed expected
 where
  env=gEnv (pad oldState) (pad newState) funding payout sequence
  signed=(m,(pad oldState,pad newState),(who,a),(signatureW,extra))
  signatureW=case env cmr>>=(\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of
   Just msg->sigW (signMsg (keys H.!! signer) (w256ToBytes msg));_->error "growth vector sig-all"

entry :: String -> String -> String -> [String] -> Kernel -> [Vector GW] -> Entry
entry ident title spec assumptions term vectors=Entry ident title spec BitcoinApp
 (Derived "independent Integer state arithmetic/rounding and actual native funding/output commitments; every negative transaction re-signed to isolate covenant checks")
 (assumptions++["two serialized accounts, fixed public keys; one native collateral state UTXO and separate1000-sat fee input", "one aggregate witness, authenticated old state and complete successor;10000-sat state carrier is excluded from user assets"])
 (boundProgram term . encode) vectors

entries :: [Entry]
entries=[vaultEntry,asyncEntry,auctionEntry,blindEntry,squadsEntry]

vaultEntry=entry "app-tokenized-native-vault" "Native BTC ERC4626-style nontransferable share vault" "ERC4626 deposit/mint/withdraw/redeem rounding; pinned contract-growth source"
 ["complete four-action two-owner share ledger plus donation; one virtual asset/share; no foreign ERC20 balances or external yield assumed"] vaultT vectors
 where
  oldState=[100003,70000,40000,30000,4]
  update a s u v=[a,s,u,v,5]
  v=vectorBound (cmrOf vaultT)
  vectors=[v "deposit rounds shares down" vaultT 0 oldState (update 101003 70699 40699 30000) 0 1000 0 1000 Nothing 0xfffffffe Accept,
   v "mint rounds assets up" vaultT 1 oldState (update 100718 70500 40000 30500) 1 500 1 715 Nothing 0xfffffffe Accept,
   v "withdraw rounds shares up" vaultT 2 oldState (update 99003 69300 39300 30000) 0 1000 0 0 (Just (0,1000)) 0xfffffffe Accept,
   v "redeem rounds assets down" vaultT 3 oldState (update 99289 69500 40000 29500) 1 500 1 0 (Just (1,714)) 0xfffffffe Accept,
   v "donation creates no shares" vaultT 4 oldState (update 101003 70000 40000 30000) 0 1000 0 1000 Nothing 0xfffffffe Accept,
   v "deposit inflation by one share" vaultT 0 oldState (update 101003 70700 40700 30000) 0 1000 0 1000 Nothing 0xfffffffe Reject,
   v "mint underfunded by one sat" vaultT 1 oldState (update 100717 70500 40000 30500) 1 500 1 714 Nothing 0xfffffffe Reject,
   v "wrong share owner signs" vaultT 3 oldState (update 99289 69500 40000 29500) 1 500 0 0 (Just (1,714)) 0xfffffffe Reject,
   v "initial empty vault deposit" vaultT 0 [0,0,0,0,0] [1000,1000,1000,0,1] 0 1000 0 1000 Nothing 0xfffffffe Accept,
   Vector "state input cannot impersonate fee input1" reindexedEnv reindexedWitness Reject]
  -- Without CurrentIndex=0, InputValue(1) could refer to this very state input.
  -- The deposit stays backed but can evade the stated separate1000-sat fee.
  reindexedAmount=109003
  reindexedShares=reindexedAmount*70001 `div`100004
  reindexedNew=update (100003+reindexedAmount) (70000+reindexedShares) (40000+reindexedShares) 30000
  reindexedEnv cmr=mkEnv transaction 1 (\_->stateTap cmr (stateRef oldState)) cmr
   where
    stateInput=mkInput (dummyOutpoint 1) 110003 (BL.fromStrict (stateScript cmr (stateRef oldState))) 0xfffffffe
    actualFunding=mkInput (dummyOutpoint 0) (fromInteger reindexedAmount) (BL.fromStrict (recipient 9)) 0xfffffffe
    transaction=mkTx 2 [actualFunding,stateInput] [mkOutput (fromInteger (H.head reindexedNew+carrier)) (stateScript cmr (stateRef reindexedNew))] 0
  reindexedSig=case reindexedEnv (cmrOf vaultT)>>=(\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of
   Just msg->sigW (signMsg (keys H.!!0) (w256ToBytes msg));_->error "reindexed deposit signature"
  reindexedWitness=(0,(pad oldState,pad reindexedNew),(0,reindexedAmount),(reindexedSig,zeroSig))

asyncEntry=entry "app-asynchronous-vault-claims" "Native asynchronous vault request, fulfillment and partial claim" "ERC7540 request/controller/operator lifecycle; economic share accounting native adaptation"
 ["pending deposits and redeem-assets are segregated from active assets; economic supply includes user, claimable and pending-redeem shares", "one signed vault authority fulfills each batch; delegated claims require a committed operator bit; no external yield or current-clock assertion"] asyncT vectors
 where
  baseState=[100000,100000,100000,60000,40000,0,0,0,0,0,0,0,0,0,0,5]
  requested=[101000,100000,100000,60000,40000,1000,0,0,0,0,0,0,0,0,0,6]
  fulfilled=[101000,101000,101000,60000,40000,0,0,1000,0,0,0,0,0,0,1,7]
  claimed=[101000,101000,101000,60400,40000,0,0,600,0,0,0,0,0,0,1,8]
  reqR=[100000,100000,100000,59000,40000,0,0,0,0,1000,0,0,0,0,0,6]
  fullR=[100000,99000,99000,59000,40000,0,0,0,0,0,0,1000,0,0,1,7]
  partialR=[99400,99000,99000,59000,40000,0,0,0,0,0,0,400,0,0,1,8]
  grant=[101000,101000,101000,60000,40000,0,0,1000,0,0,0,0,0,1,1,8]
  delegated=[101000,101000,101000,60400,40000,0,0,600,0,0,0,0,0,1,1,9]
  v=vectorBound (cmrOf asyncT)
  vectors=[v "fund pending deposit" asyncT 0 baseState requested 0 1000 0 1000 Nothing 0xfffffffe Accept,
   v "authority fulfills into claimable shares" asyncT 2 requested fulfilled 0 0 3 0 Nothing 0xfffffffe Accept,
   v "controller partially pulls shares" asyncT 4 fulfilled claimed 0 400 0 0 Nothing 0xfffffffe Accept,
   v "request redemption escrows shares" asyncT 1 baseState reqR 0 1000 0 0 Nothing 0xfffffffe Accept,
   v "authority fixes redeem assets" asyncT 3 reqR fullR 0 0 3 0 Nothing 0xfffffffe Accept,
   v "controller partially pulls redeem assets" asyncT 5 fullR partialR 0 600 0 0 (Just (0,600)) 0xfffffffe Accept,
   v "controller grants operator" asyncT 6 fulfilled grant 0 0 0 0 Nothing 0xfffffffe Accept,
   v "operator pulls to controller account" asyncT 8 grant delegated 0 400 2 0 Nothing 0xfffffffe Accept,
   v "unapproved operator" asyncT 8 fulfilled claimed 0 400 2 0 Nothing 0xfffffffe Reject,
   v "claim cannot skip fulfillment" asyncT 4 requested claimed 0 400 0 0 Nothing 0xfffffffe Reject,
   v "non-authority cannot fulfill" asyncT 2 requested fulfilled 0 0 0 0 Nothing 0xfffffffe Reject,
   v "redeem claim overdraw" asyncT 5 fullR partialR 0 1001 0 0 (Just (0,600)) 0xfffffffe Reject]

auctionEntry=entry "app-ascending-auction-escrow" "Funded ascending auction with displaced-bid refunds and close phase" "Solidity SimpleAuction native explicit-phase adaptation"
 ["two bidder accounts; auction authority signs the monotone close phase; exact Ethereum upper wall-clock bidding cutoff is not claimed", "all bid/refund credits stay collateralized; winner's actual highest bid pays the beneficiary once"] auctionT vectors
 where
  first=[1000,0,1000,0,0,0,1]
  second=[2500,0,1500,1,1000,0,2]
  refund=[1500,0,1500,1,0,0,3]
  closed=[1000,1,1500,1,1000,0,3]
  v=vectorBound (cmrOf auctionT)
  vectors=[v "first funded bid" auctionT 0 [0,0,0,2,0,0,0] first 0 1000 0 1000 Nothing 0xfffffffe Accept,
   v "higher bid credits displaced bidder" auctionT 0 first second 1 1500 1 1500 Nothing 0xfffffffe Accept,
   v "displaced bidder withdraws" auctionT 1 second refund 0 0 0 0 (Just (0,1000)) 0xfffffffe Accept,
   v "beneficiary receives winning bid at close" auctionT 2 second closed 0 0 3 0 (Just (3,1500)) 0xfffffffe Accept,
   v "equal bid rejected" auctionT 0 first second 1 1000 1 1500 Nothing 0xfffffffe Reject,
   v "fake displaced refund credit" auctionT 0 first [2500,0,1500,1,1001,0,2] 1 1500 1 1500 Nothing 0xfffffffe Reject,
   v "bid after close" auctionT 0 closed second 1 1500 1 1500 Nothing 0xfffffffe Reject,
   v "wrong close authority" auctionT 2 second closed 0 0 1 0 (Just (3,1500)) 0xfffffffe Reject,
   v "empty auction closes safely" auctionT 2 [0,0,0,2,0,0,0] [0,1,0,2,0,0,1] 0 0 3 0 Nothing 0xfffffffe Accept,
   v "malformed empty winner state" auctionT 2 [0,0,0,0,0,0,0] [0,1,0,0,0,0,1] 0 0 3 0 Nothing 0xfffffffe Reject]

blindHash bid fake secret=w256FromBytes (K.keccak256 (R.bytesFromInt bid<>BS.singleton (if fake then 1 else 0)<>R.bytesFromInt secret))
hashWords h=map (R.intFromBytes . (\i->BS.take 8 (BS.drop i (w256ToBytes h)))) [0,8,16,24]
blindEntry=entry "app-sealed-bid-auction-escrow" "Two-bidder commit/reveal auction with covered bids and one-time refunds" "Solidity BlindAuction exact value/fake/secret packed Keccak commitments; native explicit-phase adaptation"
 ["one commitment each; authority advances commit/reveal/closed phases; no upper-time claim", "deposit credits are retained until close, then revealed bidders pull refunds; unrevealed deposits remain locked, as an explicit bounded-auction policy", "highest valid nonfake covered bid pays beneficiary; ties preserve earlier high bidder"] blindT vectors
 where
  c0=hashWords (blindHash 1200 False 333);c1=hashWords (blindHash 1600 False 444)
  initial=pad [0,0,0,2,0,0,0,0]
  committed0=[2000,0,0,2,2000,0,1,1]++c0++replicate 4 0
  committed1=[4000,0,0,2,2000,2000,3,2]++c0++c1
  opened=[4000,1,0,2,2000,2000,3,3]++c0++c1
  revealed0=[4000,1,1200,0,2000,2000,7,4]++replicate 4 0++c1
  revealed1=[4000,1,1600,1,2000,2000,15,5]++replicate 8 0
  closed=pad [2400,2,1600,1,2000,400,15,6]
  refunded=pad [2000,2,1600,1,2000,0,15,7]
  v=vectorPayloadBound (cmrOf blindT)
  vectors=[v "bidder0 commits funded hidden bid" blindT 0 initial committed0 0 2000 0 (blindHash 1200 False 333,w256 0) 2000 Nothing 0xfffffffe Accept,
   v "bidder1 commits" blindT 0 committed0 committed1 1 2000 1 (blindHash 1600 False 444,w256 0) 2000 Nothing 0xfffffffe Accept,
   v "authority starts reveal" blindT 1 committed1 opened 0 0 3 zeroSig 0 Nothing 0xfffffffe Accept,
   v "valid first reveal" blindT 2 opened revealed0 0 1200 0 (w256 333,w256 0) 0 Nothing 0xfffffffe Accept,
   v "higher covered reveal" blindT 2 revealed0 revealed1 1 1600 1 (w256 444,w256 0) 0 Nothing 0xfffffffe Accept,
   v "close pays winner bid" blindT 3 revealed1 closed 0 0 3 zeroSig 0 (Just (3,1600)) 0xfffffffe Accept,
   v "winner pulls excess deposit" blindT 4 closed refunded 1 0 1 zeroSig 0 (Just (1,400)) 0xfffffffe Accept,
   v "wrong secret" blindT 2 opened revealed0 0 1200 0 (w256 334,w256 0) 0 Nothing 0xfffffffe Reject,
   v "second reveal rejected" blindT 2 revealed0 revealed0 0 1200 0 (w256 333,w256 0) 0 Nothing 0xfffffffe Reject,
   v "commit overwrite rejected" blindT 0 committed0 committed0 0 2000 0 (blindHash 1200 False 333,w256 0) 2000 Nothing 0xfffffffe Reject,
   v "no eligible winner closes without payment" blindT 3 [0,1,0,2,0,0,0,3] [0,2,0,2,0,0,0,4] 0 0 3 zeroSig 0 Nothing 0xfffffffe Accept,
   v "malformed collateral state" blindT 1 [4001,0,0,2,2000,2000,3,2] opened 0 0 3 zeroSig 0 Nothing 0xfffffffe Reject]

-- Squads-style fixed roles: every member may Vote (hence also create), but
-- only member2 may Execute. Approvals/rejections replace an opposite vote;
-- duplicate votes fail. Stale approved proposals remain executable per source.
squadsT :: (Simplicity t,Primitive t) => GT t
squadsT=allChecks [base,valid,choose [(0,create),(1,vote True),(2,vote False),(3,cancel),(4,execute),(5,invalidate)]]
 where
  valid=allChecks [le (o 2) (k 5),le (o 3) (k 1),le (o 5) (k 7),le (o 6) (k 7),le (o 7) (k 7),same ((o 5&&&o 6)>>>W.bitwise_and word64) (k 0),statusValid,allChecks [same (o i) (k 0)|i<-[9..14]]]
  bit=select (is actor (k 0)) (k 1) (select (is actor (k 1)) (k 2) (k 4))
  mark bm=(bm&&&bit)>>>W.bitwise_or word64
  erase bm=(bm&&&(bit>>>W.complement word64))>>>W.bitwise_and word64
  absent bm=same ((bm&&&bit)>>>W.bitwise_and word64) (k 0)
  pop bm=L.foldl' add (k 0) [select (is ((bm&&&k b)>>>W.bitwise_and word64) (k 0)) (k 0) (k 1)|b<-[1,2,4]]
  status bm yes no=select ((k 2&&&pop bm)>>>A.le word64) (k yes) (k no)
  approved=le (k 2) (pop (o 5))
  statusValid=select (is (o 2) (k 0)) (allChecks [same (o 4) (k 0),same (o 5) (k 0),same (o 6) (k 0),same (o 7) (k 0)])
   (select (is (o 2) (k 1)) (allChecks [lt (pop (o 5)) (k 2),lt (pop (o 6)) (k 2)])
    (select (is (o 2) (k 2)) (approved&&&lt (pop (o 7)) (k 2)>>>unit)
     (select (is (o 2) (k 3)) (le (k 2) (pop (o 6)))
      (select (is (o 2) (k 4)) (approved&&&le (k 2) (pop (o 7))>>>unit) approved))))
  staleActive=and (is (o 2) (k 1)) ((o 1&&&o 8)>>>A.le word64)
  inactive=or staleActive (or (is (o 2) (k 0)) (or (is (o 2) (k 3)) (or (is (o 2) (k 4)) (is (o 2) (k 5)))))>>>verify
  create=allChecks [actorSig,inactive,nonzero amount,le amount (o 0),le (n 3) (k 1),lt (o 8) (add (o 1) (k 1)),changes [(1,add (o 1) (k 1)),(2,k 1),(3,n 3),(4,amount),(5,k 0),(6,k 0),(7,k 0),nonce 15],noCash]
  vote approve=allChecks [actorSig,same (o 2) (k 1),lt (o 8) (o 1),absent (o (if approve then 5 else 6)),changes (if approve then [(2,status (mark (o 5)) 2 1),(5,mark (o 5)),(6,erase (o 6)),nonce 15] else [(2,status (mark (o 6)) 3 1),(5,erase (o 5)),(6,mark (o 6)),nonce 15]),noCash]
  cancel=allChecks [actorSig,same (o 2) (k 2),absent (o 7),changes [(2,status (mark (o 7)) 4 2),(7,mark (o 7)),nonce 15],noCash]
  execute=allChecks [same actor (k 2),sigAt 2,same (o 2) (k 2),unit>>>konst (w16 10)>>>TL.checkLockDistance,changes [(0,sub (o 0) (o 4)),(2,k 5),nonce 15],withdraw (o 4) (select (is (o 3) (k 0)) (destination 0) (destination 1))]
  invalidate=allChecks [sigAt 3,changes [(8,o 1),nonce 15],noCash]

squadsEntry=entry "app-squads-proposal-execution" "Role-separated proposal, vote, cancellation and delayed one-time payout" "SquadsV4 proposal_create/vote/vault_transaction_execute and proposal/multisig state helpers, pinned contract-growth sources"
 ["native fixed3-member/threshold2 lifecycle; three Vote/propose roles, only member2 Execute; fixed config authority may invalidate prior active proposals", "CSV10 is a conservative native delay since the last proposal state output, replacing foreign approved-timestamp clock; approved proposals may execute after becoming stale", "fixed single native payout instruction, no arbitrary Solana account/CPI execution claimed"] squadsT vectors
 where
  s balance index status dest amt approvals rejects cancels stale nonceValue=pad [balance,index,status,dest,amt,approvals,rejects,cancels,stale,0,0,0,0,0,0,nonceValue]
  idle=s 100000 10 0 0 0 0 0 0 10 5
  active=s 100000 11 1 1 25000 0 0 0 10 6
  one=s 100000 11 1 1 25000 1 0 0 10 7
  approved=s 100000 11 2 1 25000 3 0 0 10 8
  paid=s 75000 11 5 1 25000 3 0 0 10 9
  stale=s 100000 11 2 1 25000 3 0 0 11 9
  stalePaid=s 75000 11 5 1 25000 3 0 0 11 10
  cancelling=s 100000 11 2 1 25000 3 0 1 10 9
  cancelled=s 100000 11 4 1 25000 3 0 3 10 10
  rejected1=s 100000 11 1 1 25000 0 1 0 10 7
  rejected2=s 100000 11 3 1 25000 0 3 0 10 8
  activeStale=s 100000 11 1 1 25000 0 0 0 11 7
  replacement=s 100000 12 1 0 10000 0 0 0 11 8
  malformedApproved=s 100000 11 2 1 25000 0 0 0 10 8
  malformedPaid=s 75000 11 5 1 25000 0 0 0 10 9
  cmr=cmrOf squadsT
  v name m a b who value signer payout seq expected=vectorBound cmr name squadsT m a b who value signer 0 payout seq expected
  vectors=[v "create indexed payout proposal" 0 idle active 0 25000 0 Nothing 0xfffffffe Accept,
   v "first member approval" 1 active one 0 0 0 Nothing 0xfffffffe Accept,
   v "second approval reaches threshold" 1 one approved 1 0 1 Nothing 0xfffffffe Accept,
   v "designated executor after delay" 4 approved paid 2 0 2 (Just (1,25000)) 10 Accept,
   v "executor too early" 4 approved paid 2 0 2 (Just (1,25000)) 9 Reject,
   v "vote role lacks execute permission" 4 approved paid 1 0 1 (Just (1,25000)) 10 Reject,
   v "duplicate approval" 1 one one 0 0 0 Nothing 0xfffffffe Reject,
   v "configuration makes approved proposal stale" 5 approved stale 0 0 3 Nothing 0xfffffffe Accept,
   v "previously approved stale proposal still executes" 4 stale stalePaid 2 0 2 (Just (1,25000)) 10 Accept,
   v "one cancellation" 3 approved cancelling 0 0 0 Nothing 0xfffffffe Accept,
   v "cancellation threshold closes proposal" 3 cancelling cancelled 1 0 1 Nothing 0xfffffffe Accept,
   v "one rejection" 2 active rejected1 0 0 0 Nothing 0xfffffffe Accept,
   v "rejection cutoff makes approval impossible" 2 rejected1 rejected2 1 0 1 Nothing 0xfffffffe Accept,
   v "executed proposal cannot pay twice" 4 paid paid 2 0 2 (Just (1,25000)) 10 Reject,
   v "config invalidates an active proposal" 5 active activeStale 0 0 3 Nothing 0xfffffffe Accept,
   v "fresh proposal replaces stale active proposal" 0 activeStale replacement 0 10000 0 Nothing 0xfffffffe Accept,
   v "stale active proposal cannot collect votes" 1 activeStale one 0 0 0 Nothing 0xfffffffe Reject,
   v "approved status without approvals is malformed" 4 malformedApproved malformedPaid 2 0 2 (Just (1,25000)) 10 Reject]
