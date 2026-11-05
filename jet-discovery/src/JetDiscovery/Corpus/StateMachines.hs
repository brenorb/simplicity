{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Complete covenant state machines over native BTC. State is authenticated
-- by the current internal key and preserved under the same executable leaf.
module JetDiscovery.Corpus.StateMachines (entries) where
import Prelude hiding (drop,take,not,and,or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Word as DW
import Data.Serialize (runPut,putWord64be)
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
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
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as R

type SigW=(Word256,Word256)
skA=1010;skB=2020
pk sk=w256 (R.pubkeyOf sk)
recipient i=unhex "0014"<>BS.replicate 20 (fromIntegral (0x90+i))
other=unhex "0014"<>BS.replicate 20 0x99
scriptHash=w256FromBytes . hashToBytes . sha256
zeroSig=(w256 0,w256 0)
sigW (Sig r s)=(w256 (toInteger r),w256 (toInteger s))
same a b=(a&&&b)>>>eq>>>verify
add64 a b=(a&&&b)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
sub64 a b=(a&&&b)>>>A.subtract word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
outVal i=konst (w32 i)>>>primitive P.OutputValue>>>verify
outScript i=konst (w32 i)>>>primitive P.OutputScriptHash>>>verify
count n=same (unit>>>Tx.numOutputs) (konst (w32 n))
pay i dest value=(same (outScript i) (konst (scriptHash dest))&&&same (outVal i) value)>>>unit
continue new value=(same (outScript 0) (stateScriptHash new)&&&same (outVal 0) value)>>>unit
state4 a b c d=((w64 a,w64 b),(w64 c,w64 d))

stateEnv old value seq outs cmr=mkEnv transaction 0 (\_->stateTap cmr (w256ToBytes old)) cmr
 where
  script=stateScript cmr (w256ToBytes old)
  transaction=mkTx 2 [mkInput (dummyOutpoint 0) (fromInteger value) (BL.fromStrict script) seq,mkInput (dummyOutpoint 1) 1000 (BL.fromStrict other) 0xfffffffe]
   [mkOutput (fromInteger v) s|(v,s)<-outs cmr] 0
stateOut dat value cmr=(value,stateScript cmr (w256ToBytes dat))
signAll sk prog makeEnv=case makeEnv (progCmr prog)>>=(\e->J.fastEval (unwrap (J.jetSubst SH.sigAllHash)) e ()) of
 Just m->sigW (signMsg sk (w256ToBytes m));_->error "state-machine signature"

-- Both parties sign the new state independently of any previous outpoint.
-- A later state can therefore override an older confirmed state during CSV.
channelId=BS.replicate 32 0x5a
channelMessage :: (Assert t,Primitive t,TyC a) => t a Word256 -> t a Word256
channelMessage new=((((unit>>>ctx8InitTag "Simplicity/Channel/State")&&&konst (w256FromBytes channelId)>>>ctx8Add32)&&&(unit>>>primitive P.ScriptCMR)>>>ctx8Add32)&&&new)>>>ctx8Add32>>>ctx8Finalize
channel :: (Simplicity t,Primitive t) => (Bool,(Word256,Word256),(SigW,SigW)) -> t () ()
channel (updateMode,(oldState,newState),(sigA,sigB))=witness (bitW updateMode,((oldState,newState),(sigA,sigB)))>>>channelT
channelT :: (Simplicity t,Primitive t) => t (Bit,((Word256,Word256),(SigW,SigW))) ()
channelT=(loadState old&&&validOld&&&(oh&&&iden>>>cond update settle))>>>unit
 where
  old=drop (take oh);new=drop (take ih)
  validOld=(same (old>>>iih) (konst (w64 0))&&&same (add64 (old>>>oih) (old>>>ioh)) (unit>>>Tx.currentValue))>>>unit
  update=(signed&&&higher&&&validNew&&&count 1&&&continue new (unit>>>Tx.currentValue))>>>unit
  signed=(checkSigWith (pk skA) (channelMessage new) (drop (drop oh))&&&checkSigWith (pk skB) (channelMessage new) (drop (drop ih)))>>>unit
  higher=((old>>>ooh)&&&(new>>>ooh))>>>A.lt word64>>>verify
  validNew=(same (new>>>iih) (konst (w64 0))&&&same (add64 (new>>>oih) (new>>>ioh)) (unit>>>Tx.currentValue))>>>unit
  settle=(konst (w16 144)>>>TL.checkLockDistance)&&&count 2&&&pay 0 (recipient 0) (old>>>oih)&&&pay 1 (recipient 1) (old>>>ioh)>>>unit
bitW b=if b then Right () else Left ()

-- A budget can be spent in many chunks. Refill waits144 blocks since the
-- previous state UTXO; this is explicitly an idle-period bucket, not wall time.
budget :: (Simplicity t,Primitive t) => (Integer,Word256,Word64,SigW) -> t () ()
budget (mode,oldState,amount,signature)=witness (w8 mode,(oldState,(amount,signature)))>>>budgetT
budgetT :: (Simplicity t,Primitive t) => t (Word8,(Word256,(Word64,SigW))) ()
budgetT=loadState old&&&valid&&&choose>>>unit
 where
  old=ioh;a=iioh
  left=old>>>ooh;nonce=old>>>oih
  nextNonce=add64 nonce (konst (w64 1))
  state remaining=(remaining&&&nextNonce)&&&konst (toWord128 0)
  valid=(((left&&&konst (w64 10000))>>>A.le word64>>>verify)&&&same (old>>>ih) (konst (toWord128 0)))>>>unit
  spend=(checkSigWith (pk skB) (unit>>>sigMsg) iiih&&&((konst (w64 0)&&&a)>>>A.lt word64>>>verify)&&&count 2
       &&&continue (state (sub64 left a)) (sub64 (unit>>>Tx.currentValue) a)&&&pay 1 (recipient 1) a)>>>unit
  refill=(konst (w16 144)>>>TL.checkLockDistance)&&&count 1&&&continue (state (konst (w64 10000))) (unit>>>Tx.currentValue)>>>unit
  close=checkSigWith (pk skA) (unit>>>sigMsg) iiih&&&count 1&&&pay 0 (recipient 0) (unit>>>Tx.currentValue)>>>unit
  choose=L.foldr (\(i,t) rest->(oh&&&konst (w8 i)>>>eq)&&&iden>>>cond t rest) failure [(0,spend),(1,refill),(2,close)]

ownerStore :: (Simplicity t,Primitive t) => ((Word256,Word256),SigW) -> t () ()
ownerStore w=witness w>>>ownerStoreT
ownerStoreT :: (Simplicity t,Primitive t) => t ((Word256,Word256),SigW) ()
ownerStoreT=loadState (take oh)&&&checkSigWith (pk skA) (unit>>>sigMsg) ih&&&count 1&&&continue (take ih) (unit>>>Tx.currentValue)>>>unit

-- Merkle-sum liability proof: every node hash commits both child hashes and
-- sums; checked addition prevents wraparound from reducing liabilities.
type SumNode=(Word256,Word64)
type SumProof=((Word256,Word64),((Bit,SumNode),(Bit,SumNode)))
sumLeaf :: Assert t => t (Word256,Word64) SumNode
sumLeaf=((((unit>>>ctx8InitTag "Simplicity/Reserve/Leaf")&&&oh>>>ctx8Add32)&&&ih)>>>ctx8Add8>>>ctx8Finalize)&&&ih
sumNode :: Assert t => t (Bit,(SumNode,SumNode)) SumNode
sumNode=cond (ih&&&oh) iden>>>parent
 where
  parent=((((((unit>>>ctx8InitTag "Simplicity/Reserve/Node")&&&ooh>>>ctx8Add32)&&&oih>>>ctx8Add8)&&&ioh>>>ctx8Add32)&&&iih)>>>ctx8Add8>>>ctx8Finalize)&&&add64 oih iih
sumRoot :: Assert t => t SumProof SumNode
sumRoot=iden&&&take sumLeaf>>>first>>>second
 where
  first=oh&&&(((take (drop (take oh)))&&&(ih&&&(take (drop (take ih)))))>>>sumNode)
  second=((take (drop (drop oh)))&&&(ih&&&(take (drop (drop ih)))))>>>sumNode
sumState :: Assert t => t SumNode Word256
sumState=(((unit>>>ctx8InitTag "Simplicity/Reserve/State")&&&oh>>>ctx8Add32)&&&ih)>>>ctx8Add8>>>ctx8Finalize
reserve :: (Simplicity t,Primitive t) => (SumProof,SigW) -> t () ()
reserve w=witness w>>>reserveT
reserveT :: (Simplicity t,Primitive t) => t (SumProof,SigW) ()
reserveT=(loadState state&&&custody&&&inputSolvent&&&count 1&&&same (outScript 0) (unit>>>Tx.currentScriptHash)&&&outputSolvent)>>>unit
 where
  root=take sumRoot;state=root>>>sumState
  custody=checkSigWith (pk skA) (unit>>>sigMsg) ih
  inputSolvent=((root>>>ih)&&&(unit>>>Tx.currentValue))>>>A.le word64>>>verify
  outputSolvent=((root>>>ih)&&&outVal 0)>>>A.le word64>>>verify

be64 n=runPut (putWord64be (fromInteger n))
sumLeafRef (account,b)=(R.taggedHash "Simplicity/Reserve/Leaf" (R.bytesFromInt account<>be64 b),b)
sumNodeRef (h,a) (j,b)=(R.taggedHash "Simplicity/Reserve/Node" (h<>be64 a<>j<>be64 b),a+b)
sumStateRef (h,n)=R.taggedHash "Simplicity/Reserve/State" (h<>be64 n)
sumProofRef leaves i=(leaves!!i,[(odd i,ns!!(if even i then i+1 else i-1)),(i>=2,parents!!(if i<2 then 1 else 0))])
 where ns=map sumLeafRef leaves;parents=[sumNodeRef (ns!!0) (ns!!1),sumNodeRef (ns!!2) (ns!!3)]
sumProofW ((a,v),[(d,(h,n)),(e,(j,m))])=((w256 a,w64 v),((bitW d,(w256FromBytes h,w64 n)),(bitW e,(w256FromBytes j,w64 m))))
sumProofW _=error "sum proof depth2"

entries :: [Entry]
entries=[channelEntry,budgetEntry,storageEntry,reserveEntry]
 where
  old=state4 5 40000 60000 0
  newer=state4 6 45000 55000 0
  channelP w=Prog (channel w)
  channelCmr=progCmr (channelP (True,(old,newer),(zeroSig,zeroSig)))
  channelSigs state=let msg=R.taggedHash "Simplicity/Channel/State" (channelId<>hashToBytes channelCmr<>w256ToBytes state)
                   in (sigW (signMsg skA msg),sigW (signMsg skB msg))
  updateEnv previous next=stateEnv previous 100000 0xfffffffe (\cmr->[stateOut next 100000 cmr])
  settleEnv seq a b=stateEnv old 100000 seq (\_->[(a,recipient 0),(b,recipient 1)])
  channelEntry=Entry "app-symmetric-channel-state" "Versioned symmetric payment-channel update and CSV settlement" "BIP448/LN-Symmetry update/settlement design, native state-key covenant adaptation (not BIP448 byte encoding)"
   BitcoinApp (Derived "parties sign newstate+channelID+ScriptCMR independently of outpoint; Integer balance conservation and actual continuation outputs")
   ["new signed state must increase version and preserve total collateral; signatures rebind after an older state confirms", "anyone can settle agreed balances after CSV144; an update restarts the contest delay; one state UTXO serializes the channel", "fixed unique channel ID and two parties; fees are funded by an external input; single executable leaf"]
   (\w->channelP w)
   [Vector "higher state updates channel" (updateEnv old newer) (True,(old,newer),channelSigs newer) Accept,
    Vector "same pre-signed state overrides an older confirmed version" (updateEnv (state4 3 30000 70000 0) newer) (True,(state4 3 30000 70000 0,newer),channelSigs newer) Accept,
    Vector "version does not increase" (updateEnv old old) (True,(old,old),channelSigs old) Reject,
    Vector "signed balance inflation" (updateEnv old (state4 6 45000 55001 0)) (True,(old,state4 6 45000 55001 0),channelSigs (state4 6 45000 55001 0)) Reject,
    Vector "settlement after contest delay" (settleEnv 144 40000 60000) (False,(old,newer),(zeroSig,zeroSig)) Accept,
    Vector "settlement early" (settleEnv 143 40000 60000) (False,(old,newer),(zeroSig,zeroSig)) Reject,
    Vector "settlement allocation altered" (settleEnv 144 40001 59999) (False,(old,newer),(zeroSig,zeroSig)) Reject]
  -- Refillable budget with both administrator recovery and delegate spending.
  budgetOld=state4 2000 7 0 0
  budgetP w=Prog (budget w)
  spent amount=state4 (2000-amount) 8 0 0
  spendEnv amount rootValue next=stateEnv budgetOld 100000 0xfffffffe (\cmr->[stateOut next rootValue cmr,(amount,recipient 1)])
  goodSpend=spendEnv 500 99500 (spent 500)
  budgetSig sk mode amount env=signAll sk (budgetP (mode,budgetOld,w64 amount,zeroSig)) env
  refillEnv seq next=stateEnv budgetOld 100000 seq (\cmr->[stateOut next 100000 cmr])
  refilled=state4 10000 8 0 0
  closeEnv=stateEnv budgetOld 100000 0xfffffffe (\_->[(100000,recipient 0)])
  budgetEntry=Entry "app-refillable-withdrawal-budget" "Stateful withdrawal-budget wallet with idle-period refill" "Safe AllowanceModule spending-budget pattern adapted to a Bitcoin CSV-refill state machine https://github.com/safe-global/safe-modules"
   BitcoinApp (Derived "checked remaining-budget/nonce arithmetic; actual collateral debit, delegate signatures, CSV/refill and owner recovery negatives")
   ["multiple partial withdrawals consume a10000-sat bucket; refill waits144 blocks since the last state output; this is an idle-period model, not a current-time oracle", "delegate spends only to its committed recipient; owner can close to recovery; old budget and nonce are authenticated in state"]
   (\w->budgetP w)
   [Vector "partial500 withdrawal" goodSpend (0,budgetOld,w64 500,budgetSig skB 0 500 goodSpend) Accept,
    Vector "budget overdraw" (spendEnv 2001 97999 (spent 2001)) (0,budgetOld,w64 2001,budgetSig skB 0 2001 (spendEnv 2001 97999 (spent 2001))) Reject,
    Vector "remaining collateral wrong" (spendEnv 500 99499 (spent 500)) (0,budgetOld,w64 500,budgetSig skB 0 500 (spendEnv 500 99499 (spent 500))) Reject,
    Vector "refill after idle delay" (refillEnv 144 refilled) (1,budgetOld,w64 0,zeroSig) Accept,
    Vector "refill early" (refillEnv 143 refilled) (1,budgetOld,w64 0,zeroSig) Reject,
    Vector "refill nonce not advanced" (refillEnv 144 (state4 10000 7 0 0)) (1,budgetOld,w64 0,zeroSig) Reject,
    Vector "owner closes to recovery" closeEnv (2,budgetOld,w64 0,budgetSig skA 2 0 closeEnv) Accept]
  oldValue=w256 0x11223344
  newValue=w256 0xaabbccdd
  storageP w=Prog (ownerStore w)
  storeEnv old new=stateEnv old 100000 0xfffffffe (\cmr->[stateOut new 100000 cmr])
  storeSig sk e=signAll sk (storageP ((oldValue,newValue),zeroSig)) e
  goodStore=storeEnv oldValue newValue
  storageEntry=Entry "app-owner-authenticated-storage" "Owner-authorized persistent bytes32 store" "Pinned simplicity-contracts simple_storage/bytes32_tr_storage owner+state-commitment patterns; Bitcoin native-data adaptation"
   BitcoinApp (Derived "independent internal-key state commitments and transaction-bound owner signatures")
   ["complete arbitrary-write storage transition with ownership, old-value authentication, new-value commitment and exact collateral preservation", "this stores data in Taproot commitments; it does not emulate Elements asset issuance or burn"]
   (\w->storageP w)
   [Vector "owner writes new value" goodStore ((oldValue,newValue),storeSig skA goodStore) Accept,
    Vector "wrong writer" goodStore ((oldValue,newValue),storeSig skB goodStore) Reject,
    Vector "old value misreported" goodStore ((w256 0,newValue),storeSig skA goodStore) Reject,
    Vector "stored output not updated" (storeEnv oldValue oldValue) ((oldValue,newValue),storeSig skA (storeEnv oldValue oldValue)) Reject]
  -- Liabilities are committed by a real authenticated Merkle-sum root.
  leaves=[(1,10000),(2,20000),(3,30000),(4,35000)]
  ns=map sumLeafRef leaves
  root=sumNodeRef (sumNodeRef (ns!!0) (ns!!1)) (sumNodeRef (ns!!2) (ns!!3))
  reserveState=w256FromBytes (sumStateRef root)
  proof=sumProofW (sumProofRef leaves 2)
  reserveP w=Prog (reserve w)
  reserveEnv input output=stateEnv reserveState input 0xfffffffe (\cmr->[stateOut reserveState output cmr])
  resSig e=signAll skA (reserveP (proof,zeroSig)) e
  reserveEntry=Entry "app-merkle-sum-reserve-keeper" "Merkle-sum liability proof with solvent reserve rollover" "Merkle-sum proof-of-solvency construction https://github.com/summa-dev/summa-solvency; native BTC custody covenant"
   BitcoinApp (Derived "four independent account/balance leaves; tagged child hashes include both sums; current and continuing collateral checked against total95000")
   ["authenticates a liability tree committed in the current state, then preserves that root and at least its total value", "checked64-bit node sums prevent wraparound; custodian must sign the transaction; fees may reduce excess reserves only", "liability-list completeness, account identity and audit freshness are external assumptions; no zero-knowledge privacy claim"]
   (\w->reserveP w)
   [Vector "reserves remain above liabilities" (reserveEnv 100000 99000) (proof,resSig (reserveEnv 100000 99000)) Accept,
    Vector "exact liability coverage" (reserveEnv 100000 95000) (proof,resSig (reserveEnv 100000 95000)) Accept,
    Vector "input already insolvent" (reserveEnv 94999 94999) (proof,resSig (reserveEnv 94999 94999)) Reject,
    Vector "continuation becomes insolvent" (reserveEnv 100000 94999) (proof,resSig (reserveEnv 100000 94999)) Reject]
