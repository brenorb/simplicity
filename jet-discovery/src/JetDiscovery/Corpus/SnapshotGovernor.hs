{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | Three-account delegated governance with one derived past snapshot.
module JetDiscovery.Corpus.SnapshotGovernor (entry, governorKernel, quorum) where

import Prelude hiding (and, drop, not, or, take)
import qualified Prelude as H
import Data.Bits (testBit)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Word as DW
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Bitcoin.Term (Simplicity, Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Corpus.Baseline (signMsg)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import qualified JetDiscovery.Lib.TaprootTx1 as T
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.SnapshotGovernor as Ref
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

type Ledger = Vector16 Word16
type StateW = (Ledger, Word16)
type Args = (Word8, (Word16, (Word16, Word16)))
type Proof = (StateW, (Args, G.SigW))
type Transition = (StateW, Args)
type Plan = Either StateW (Either () (Word16, Word16))

accountKeys :: [Integer]
accountKeys = [7101, 7202, 7303]

feeKey :: Integer
feeKey = 7707

keyScript :: Integer -> BS.ByteString
keyScript key = unhex "5120" <> R.bytesFromInt (R.pubkeyOf key)

payeeScript :: Ref.Payee -> BS.ByteString
payeeScript Ref.Treasury = keyScript 7606
payeeScript (Ref.Target target) = keyScript ([7404,7505] H.!! target)

stateW :: Ref.State -> StateW
stateW state = case map w16 (Ref.fields state) of
  [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p,amount] ->
    ((((a,b),(c,d)),((e,f),(g,h))),(((i,j),(k,l)),((m,n),(o,p)))) `withAmount` amount
  _ -> error "governor state has exactly 17 words"
 where withAmount = (,)

field :: Core t => Int -> t StateW Word16
field 16 = ih
field index = oh >>> G.pick (testBit index 3) (G.pick (testBit index 2)
  (G.pick (testBit index 1) (G.pick (testBit index 0) iden)))

old :: Core t => Int -> t Transition Word16
old index = oh >>> field index

mode :: Core t => t Transition Word8
mode = ioh

actor, selection, quantity :: Core t => t Transition Word16
actor = ih >>> ioh
selection = ih >>> iioh
quantity = ih >>> iih >>> ih

k16 :: (Core t, TyC a) => Integer -> t a Word16
k16 = konst . w16

add16, subtract16 :: (Assert t, TyC a) => t a Word16 -> t a Word16 -> t a Word16
add16 a b = (a &&& b) >>> A.add word16 >>> ((oh >>> not iden >>> verify) &&& ih) >>> ih
subtract16 a b = (a &&& b) >>> A.subtract word16 >>> ((oh >>> not iden >>> verify) &&& ih) >>> ih

less, atMost :: (Assert t, TyC a) => t a Word16 -> t a Word16 -> t a Bit
less a b = (a &&& b) >>> A.lt word16
atMost a b = (a &&& b) >>> A.le word16

sum16 :: (Assert t, TyC a) => [t a Word16] -> t a Word16
sum16 = L.foldl' add16 (k16 0)

pickAccount :: (Assert t, TyC a, TyC b) => t a Word16 -> t a b -> t a b -> t a b -> t a b
pickAccount which first second third = G.select (G.is which (k16 0)) first
  (G.select (G.is which (k16 1)) second third)

stateHash :: Assert t => t StateW Word256
stateHash = (iden &&& (unit >>> ctx8InitTag Ref.stateTag))
  >>> L.foldl' (>>>) iden [T.append (field index) ctx8Add2 | index <- [0..16]]
  >>> ih >>> ctx8Finalize

quorum :: Core t => t Word16 Word16
quorum = (iden &&& konst (w16 Ref.quorumNumerator)) >>> A.multiply word16
  >>> (iden &&& konst (w32 Ref.quorumDenominator)) >>> A.divide word32 >>> ih

successful :: Assert t => t StateW Bit
successful = and
  (atMost (sum16 (map field [1..3]) >>> quorum) (add16 (field 14) (field 15)))
  (less (field 13) (field 14))

active, live, expired, pending :: Assert t => t StateW Bit
pending = G.is (field 7) (k16 0)
active = or (G.is (field 7) (k16 1)) (G.is (field 7) (k16 2))
live = and active (and (less (field 8) (field 0)) (atMost (field 0) (add16 (field 8) (k16 Ref.period))))
expired = and active (G.is (field 0) (add16 (field 8) (k16 (Ref.period + 1))))

validPayment :: (Assert t, TyC a) => t a Word16 -> t a ()
validPayment amount = G.allChecks
  [ atMost (k16 Ref.minimumPayment) amount >>> verify
  , atMost amount (k16 Ref.maximumPayment) >>> verify
  ]

bitSet :: (Assert t, TyC a) => t a Word16 -> t a Word16 -> t a Bit
bitSet bits mask = G.is ((bits &&& mask) >>> W.bitwise_and word16) (k16 0) >>> not iden

validState :: Assert t => t StateW ()
validState = G.allChecks
  [ less (k16 0) (field 0) >>> verify
  , G.same (sum16 (map field [1..3])) (k16 Ref.supply)
  , G.allChecks [atMost (field index) (k16 3) >>> verify | index <- [4..6]]
  , atMost (field 7) (k16 4) >>> verify
  , G.select pending unproposed proposed
  ]
 where
  unproposed = G.allChecks ((atMost (field 0) (k16 Ref.maxPending) >>> verify) :
    [G.same (field index) (k16 0) | index <- [8..16]])
  recordedWeight = sum16 [G.select (bitSet (field 12) (k16 (2^index))) (field (9+index)) (k16 0)
    | index <- [0..2]]
  proposed = G.allChecks
    [ less (k16 0) (field 8) >>> verify
    , atMost (field 8) (k16 Ref.maxPending) >>> verify
    , less (field 8) (field 0) >>> verify
    , validPayment (field 16)
    , atMost (sum16 (map field [9..11])) (k16 Ref.supply) >>> verify
    , atMost (field 12) (k16 7) >>> verify
    , G.same (sum16 (map field [13..15])) recordedWeight
    , G.select active (atMost (field 0) (add16 (field 8) (k16 (Ref.period+1))) >>> verify)
        (G.allChecks [G.same (field 0) (add16 (field 8) (k16 (Ref.period+2))), successful >>> verify])
    ]

at :: (Assert t, Primitive t, TyC a, TyC b) => Integer -> P.Prim Word32 (Either () b) -> t a b
at index primitiveType = konst (w32 index) >>> primitive primitiveType >>> verify

fundingChecks :: (Simplicity t, Primitive t) => t StateW Word256 -> t StateW ()
fundingChecks scriptFor = G.allChecks
  [ validState
  , G.same (unit >>> primitive P.CurrentIndex) (konst (w32 0))
  , G.same (unit >>> Tx.numInputs) (konst (w32 2))
  , (at 0 P.InputPrevOutpoint &&& at 1 P.InputPrevOutpoint) >>> eq >>> not iden >>> verify
  , loadState stateHash
  , G.same (at 0 P.InputScriptHash) scriptFor
  , G.same (at 0 P.InputValue) (G.k Ref.treasury)
  , G.same (at 1 P.InputValue) (G.k Ref.fee)
  ]

authenticate :: (Simplicity t, Primitive t) => t Proof ()
authenticate = G.select signed checks unit
 where
  signed = ((ioh >>> oh) &&& konst (w8 4)) >>> A.lt word8
  who = ioh >>> ioh
  keys = map (konst . w256 . R.pubkeyOf) accountKeys
  key = case keys of
    [first,second,third] -> pickAccount who first second third
    _ -> error "three governance roles"
  checks = G.allChecks [less who (k16 3) >>> verify,
    ((key &&& (ioh >>> actionMessage)) &&& iih) >>> Secp.bip_0340_verify]

actionMessage :: (Simplicity t, Primitive t) => t Args Word256
actionMessage = (iden &&& (unit >>> ctx8InitTag Ref.actionTag))
  >>> T.append (unit >>> sigMsg) ctx8Add32
  >>> T.append oh ctx8Add1 >>> T.append ioh ctx8Add2 >>> T.append iioh ctx8Add2
  >>> T.append (iih >>> ih) ctx8Add2 >>> ih >>> ctx8Finalize

updated :: Assert t => [(Int, t Transition Word16)] -> t Transition Plan
updated replacements = injl (ledger &&& value 16)
 where
  value index = maybe (old index) id (lookup index replacements)
  ledger = case add16 (old 0) (k16 1) : map value [1..15] of
    [a,b,c,d,e,f,g,h,i,j,k,l,m,n,o,p] ->
      (((a &&& b) &&& (c &&& d)) &&& ((e &&& f) &&& (g &&& h)))
      &&& (((i &&& j) &&& (k &&& l)) &&& ((m &&& n) &&& (o &&& p)))
    _ -> error "governor ledger arity"

mutable :: Assert t => t Transition Bit
mutable = or (and (oh >>> pending) (less (old 0) (k16 Ref.maxPending))) (oh >>> live)

transfer :: Assert t => t Transition Plan
transfer = (checks &&& updated [(index+1, balance index) | index <- [0..2]]) >>> ih
 where
  checks = G.allChecks [mutable >>> verify, less selection (k16 3) >>> verify,
    G.is actor selection >>> not iden >>> verify, less (k16 0) quantity >>> verify]
  balance index = G.select (G.is actor (k16 (toInteger index))) (subtract16 (old (index+1)) quantity)
    (G.select (G.is selection (k16 (toInteger index))) (add16 (old (index+1)) quantity) (old (index+1)))

delegate :: Assert t => t Transition Plan
delegate = (checks &&& updated [(index+4, delegated index) | index <- [0..2]]) >>> ih
 where
  current = pickAccount actor (old 4) (old 5) (old 6)
  checks = G.allChecks [mutable >>> verify, atMost selection (k16 3) >>> verify, G.is current selection >>> not iden >>> verify]
  delegated index = G.select (G.is actor (k16 (toInteger index))) selection (old (index+4))

propose :: Assert t => t Transition Plan
propose = (checks &&& updated ([(7, add16 selection (k16 1)), (8, old 0), (16, quantity)]
  ++ [(9 + index, power index) | index <- [0..2]])) >>> ih
 where
  checks = G.allChecks [oh >>> pending >>> verify, less selection (k16 2) >>> verify, validPayment quantity]
  power recipient = sum16 [G.select (G.is (old (4+index)) (k16 (toInteger recipient))) (old (1+index)) (k16 0)
    | index <- [0..2]]

vote :: Assert t => t Transition Plan
vote = (checks &&& updated ((12, add16 (old 12) mask) : [(13+index, total index) | index <- [0..2]])) >>> ih
 where
  mask = pickAccount actor (k16 1) (k16 2) (k16 4)
  weight = pickAccount actor (old 9) (old 10) (old 11)
  checks = G.allChecks [oh >>> live >>> verify, less selection (k16 3) >>> verify, bitSet (old 12) mask >>> not iden >>> verify]
  total index = G.select (G.is selection (k16 (toInteger index))) (add16 (old (13+index)) weight) (old (13+index))

tick, queue, execute, recover :: (Simplicity t, Primitive t) => t Transition Plan
tick = (G.allChecks [oh >>> live >>> verify, konst (w16 1) >>> TL.checkLockDistance] &&& updated []) >>> ih
queue = (G.allChecks [oh >>> expired >>> verify, oh >>> successful >>> verify] &&& updated [(7, add16 (old 7) (k16 2))]) >>> ih
execute = (G.allChecks [less (k16 2) (old 7) >>> verify, konst (w16 2) >>> TL.checkLockDistance]
  &&& injr (injr (subtract16 (old 7) (k16 3) &&& old 16))) >>> ih
recover = (G.allChecks [oh >>> expired >>> verify, oh >>> successful >>> not iden >>> verify] &&& injr (injl unit)) >>> ih

applyPlan :: forall t. (Simplicity t, Primitive t) => t StateW Word256 -> t Plan ()
applyPlan scriptFor = copair continuation (copair refund settlement)
 where
  count :: TyC a => Integer -> t a ()
  count n = G.same (unit >>> Tx.numOutputs) (konst (w32 n))
  pay :: TyC a => Integer -> t a Word256 -> t a Word64 -> t a ()
  pay index script amount = G.allChecks [G.same (G.outScript index) script, G.same (G.outVal index) amount]
  destination :: TyC a => Ref.Payee -> t a Word256
  destination = konst . G.scriptHash . payeeScript
  continuation = G.allChecks [count 1, pay 0 scriptFor (G.k Ref.treasury)]
  refund = G.allChecks [count 1, pay 0 (destination Ref.Treasury) (G.k Ref.treasury)]
  settlement = G.allChecks [count 2, pay 0 target amount, pay 1 (destination Ref.Treasury) (G.sub (G.k Ref.treasury) amount)]
  target = G.select (G.is oh (k16 0)) (destination (Ref.Target 0)) (destination (Ref.Target 1))
  amount = konst (w32 0) &&& (konst (w16 0) &&& ih)

governorKernel :: forall t. (Simplicity t, Primitive t) => t Proof ()
governorKernel = (G.allChecks [oh >>> fundingChecks scriptFor, authenticate] &&& (oh &&& ioh))
  >>> ih >>> actions >>> applyPlan scriptFor
 where
  scriptFor :: t StateW Word256
  scriptFor = stateScriptHash stateHash
  actions :: t Transition Plan
  actions = L.foldr choose failure (zip [0..] [transfer,delegate,propose,vote,tick,queue,execute,recover])
  choose (action, branch) rest = G.select (G.is mode (konst (w8 action))) branch rest

data Coin = Coin Ref.State (Hash256 -> D.Outpoint)

coinState :: Coin -> Ref.State
coinState (Coin state _) = state

data Fixture = Fixture
  { coin :: Coin
  , action :: Ref.Action
  , outputs :: [Ref.Output]
  , serial :: DW.Word32
  , edit :: D.SigTx -> D.SigTx
  , currentIndex :: DW.Word32
  , opening :: Ref.State
  , signer :: Maybe Integer
  , signedAction :: Maybe Ref.Action
  }

origin :: D.Outpoint
origin = dummyOutpoint 500

fixture :: DW.Word32 -> Coin -> Ref.Action -> [Ref.Output] -> Fixture
fixture index input requested destinations = Fixture input requested destinations index id 0 (coinState input) key Nothing
 where
  who = case requested of
    Ref.Transfer source _ _ -> Just source
    Ref.Delegate source _ -> Just source
    Ref.Propose source _ _ -> Just source
    Ref.Vote source _ -> Just source
    _ -> Nothing
  key = (\index' -> if index' `elem` [0..2] then accountKeys H.!! index' else feeKey) <$> who

honest :: DW.Word32 -> Coin -> Ref.Action -> Fixture
honest index input requested = case Ref.step (coinState input) requested age of
  Just destinations -> fixture index input requested destinations
  Nothing -> error ("invalid governance fixture " ++ show requested)
 where
  age = case requested of
    Ref.Tick -> 1
    Ref.Execute -> 2
    _ -> 0

fixtureTx :: Fixture -> Hash256 -> D.SigTx
fixtureTx f cmr = edit f (mkTx 2 [stateInput, feeInput] (map output (outputs f)) 0)
 where
  Coin state previous = coin f
  sequenceValue = case action f of
    Ref.Tick -> 1
    Ref.Execute -> 2
    _ -> 0xfffffffe
  stateInput = mkInput (previous cmr) (fromInteger Ref.treasury)
    (BL.fromStrict (stateScript cmr (Ref.stateDigest state))) sequenceValue
  feeInput = mkInput (dummyOutpoint (1000 + serial f)) (fromInteger Ref.fee)
    (BL.fromStrict (keyScript feeKey)) 0xfffffffe
  output (Ref.Continue next) = mkOutput (fromInteger Ref.treasury) (stateScript cmr (Ref.stateDigest next))
  output (Ref.Pay who amount) = mkOutput (fromInteger amount) (payeeScript who)

fixtureEnv f cmr = mkEnv (fixtureTx f cmr) (currentIndex f)
  (\_ -> stateTap cmr (Ref.stateDigest (coinState (coin f)))) cmr

successor :: Fixture -> Coin
successor f = case outputs f of
  [Ref.Continue state] -> Coin state (\cmr -> D.Outpoint (D.txid (fixtureTx f cmr)) 0)
  _ -> error "terminal governor fixture has no continuation"

arguments :: Ref.Action -> Args
arguments requested = (w8 op, (w16 who, (w16 selected, w16 amount)))
 where (op, who, selected, amount) = Ref.actionFields requested

fixtureProof :: Fixture -> Hash256 -> Proof
fixtureProof f cmr = (stateW (opening f), (arguments (action f), signature))
 where
  signature = case signer f of
    Nothing -> G.zeroSig
    Just key -> case fixtureEnv f cmr >>= (\env -> J.fastEval sigMsg env ()) of
      Just message -> G.sigW (signMsg key (Ref.actionDigest (w256ToBytes message) (maybe (action f) id (signedAction f))))
      Nothing -> error "governor fixture signature message"

inputEdit :: Int -> (D.SigTxInput -> D.SigTxInput) -> D.SigTx -> D.SigTx
inputEdit index modify tx = tx { D.sigTxIn = V.imap (\i input -> if i == index then modify input else input) (D.sigTxIn tx) }

outputEdit :: Int -> (D.TxOutput -> D.TxOutput) -> D.SigTx -> D.SigTx
outputEdit index modify tx = tx { D.sigTxOut = V.imap (\i output -> if i == index then modify output else output) (D.sigTxOut tx) }

spentValue :: Integer -> D.SigTxInput -> D.SigTxInput
spentValue amount input = input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoValue = fromInteger amount } }

alterSuccessor :: (Ref.State -> Ref.State) -> Fixture -> Fixture
alterSuccessor modify f = case outputs f of
  [Ref.Continue state] -> f { outputs = [Ref.Continue (modify state)] }
  _ -> error "expected a governor continuation"

entry :: Entry
entry = Entry "app-oz-delegated-snapshot-governance"
  "OpenZeppelin-style delegated snapshot vote with native treasury execution"
  "OpenZeppelin Governor, Votes, CountingSimple, QuorumFraction and Checkpoints at efaa6f78ab1dde05416246e801c0baaf4f900d49"
  BitcoinApp
  (Derived "Independent Integer event and checkpoint model; linked funding, delegated snapshots, quorum, queue, CSV and terminal payouts with actual C/Haskell wire checks")
  [ "One initialized native 100000-sat treasury, three fixed signed accounts, fixed 301-unit voting supply and a single proposal"
  , "Signed transfer and delegation change current power. BIP340 authorization binds the actual sig_all_hash and explicit action fields. Creation derives the exact old checkpoint and commits immutable weights and payment terms"
  , "Against, for and abstain use the stored past weight and one-use bitmap. Quorum floors 40% of fixed supply, includes for plus abstain, and approval requires strictly more for than against"
  , "The native clock counts serialized state events. The six voting slots admit ballots and signed power changes. A permissionless CSV1 tick also advances one slot"
  , "A successful expired vote queues once, and CSV2 gates the exact committed payout to one of two configured scripts plus treasury remainder. A failed vote refunds the entire treasury"
  , "Current input 0 binds the actual state script and value. A distinct 1000-sat fee input funds each event, and one aggregate witness opens the ledger and supplies action authorization"
  ] make vectors
 where
  make = boundProgram governorKernel
  cmr = progCmr (make (stateW Ref.initial, (arguments Ref.Tick, G.zeroSig)))
  vectors = [Vector name (fixtureEnv f) (fixtureProof f cmr) expected | (name, f, expected) <- cases]

cases :: [(String, Fixture, Expect)]
cases = [(name, f, Accept) | (name, f) <- positives] ++ [(name, f, Reject) | (name, f) <- negatives]
 where
  initial = Coin Ref.initial (const origin)
  shiftFirst = honest 1 initial (Ref.Transfer 0 2 31)
  shiftSecond = honest 2 (successor shiftFirst) (Ref.Transfer 1 2 50)
  undelegate = honest 3 (successor shiftSecond) (Ref.Delegate 2 3)
  openA = honest 4 (successor undelegate) (Ref.Propose 2 0 25001)
  shiftAfter = honest 5 (successor openA) (Ref.Transfer 0 1 20)
  delegateAfter = honest 6 (successor shiftAfter) (Ref.Delegate 1 0)
  voteFor = honest 7 (successor delegateAfter) (Ref.Vote 0 1)
  voteAbstain = honest 8 (successor voteFor) (Ref.Vote 1 2)
  advanceA = honest 9 (successor voteAbstain) Ref.Tick
  voteLast = honest 10 (successor advanceA) (Ref.Vote 2 0)
  queueA = honest 11 (successor voteLast) Ref.Queue
  executeA = honest 12 (successor queueA) Ref.Execute
  openB = honest 13 initial (Ref.Propose 1 1 42001)
  bAbstain = honest 14 (successor openB) (Ref.Vote 0 2)
  bFor = honest 15 (successor bAbstain) (Ref.Vote 1 1)
  bMajority = honest 16 (successor bFor) (Ref.Vote 2 1)
  (bTick1,bTick2,bTick3) = threeTicks 17 (successor bMajority)
  queueB = honest 20 (successor bTick3) Ref.Queue
  executeB = honest 21 (successor queueB) Ref.Execute
  tieVote = honest 22 (successor bFor) (Ref.Vote 2 0)
  (tieTick1,tieTick2,tieTick3) = threeTicks 23 (successor tieVote)
  tieExpired = successor tieTick3
  tieRefund = honest 26 tieExpired Ref.Recover
  (noQuorum1,noQuorum2,noQuorum3) = threeTicks 27 (successor voteFor)
  noQuorumExpired = successor noQuorum3
  noQuorumRefund = honest 30 noQuorumExpired Ref.Recover
  threeTicks index input = (first, second, third)
   where
    first = honest index input Ref.Tick
    second = honest (index+1) (successor first) Ref.Tick
    third = honest (index+2) (successor second) Ref.Tick
  positives =
    [ ("first signed transfer changes current voting balances", shiftFirst)
    , ("second signed transfer preserves the fixed supply", shiftSecond)
    , ("undelegating removes current power while keeping all voting units", undelegate)
    , ("proposal derives exact prior powers 70, 50 and 0", openA)
    , ("post-snapshot signed transfer preserves the snapshot", shiftAfter)
    , ("post-snapshot delegation concentrates current power at 120", delegateAfter)
    , ("for ballot still counts prior 70 rather than current 120", voteFor)
    , ("abstain counts prior 50 despite zero current power", voteAbstain)
    , ("permissionless CSV1 event advances the clock", advanceA)
    , ("first-use zero-weight against ballot is valid at the final slot", voteLast)
    , ("queue succeeds at the exact floored quorum of 120", queueA)
    , ("CSV2 pays target 0 the committed 25001 and returns 74999", executeA)
    , ("alternate proposal commits target 1 and a different amount", openB)
    , ("alternate first account casts abstain with snapshot weight 101", bAbstain)
    , ("alternate second account casts for with weight 100", bFor)
    , ("alternate third account adds its 100 for votes", bMajority)
    , ("successful alternate clock event 4", bTick1)
    , ("successful alternate clock event 5", bTick2)
    , ("successful alternate clock event 6", bTick3)
    , ("queue the successful alternate proposal", queueB)
    , ("CSV2 pays target 1 the committed 42001 and returns 57999", executeB)
    , ("alternate third account instead casts 100 against votes", tieVote)
    , ("tied proposal clock event 4", tieTick1)
    , ("tied proposal clock event 5", tieTick2)
    , ("tied proposal clock event 6", tieTick3)
    , ("strict tie fails despite quorum and refunds full treasury", tieRefund)
    , ("majority without quorum clock event 4", noQuorum1)
    , ("majority without quorum clock event 5", noQuorum2)
    , ("majority without quorum clock event 6", noQuorum3)
    , ("majority without quorum fails and refunds full treasury", noQuorumRefund)
    ]
  unauthorized = Just feeKey
  redirect index = outputEdit index (\output -> output { D.txoScript = BL.fromStrict (keyScript feeKey) })
  amountEdit index delta = outputEdit index (\output -> output { D.txoValue = fromInteger (toInteger (D.txoValue output) + delta) })
  sequenceEdit sequenceValue = inputEdit 0 (\input -> input { D.sigTxiSequence = sequenceValue })
  proposed = coinState (successor openA)
  voteState = coinState (successor voteFor)
  expiredState = coinState noQuorumExpired
  beforeDeadline = successor advanceA
  prematureQueue = makeQueue 33 beforeDeadline
  makeQueue index input = let state = coinState input in fixture index input Ref.Queue
    [Ref.Continue state { Ref.clock = Ref.clock state + 1, Ref.phase = Ref.phase state + 2 }]
  doubleVote = fixture 31 (successor voteFor) (Ref.Vote 0 1)
    [Ref.Continue voteState { Ref.clock = Ref.clock voteState + 1, Ref.voted = 2, Ref.tallies = [0,140,0] }]
  lateVote = fixture 32 noQuorumExpired (Ref.Vote 1 2)
    [Ref.Continue expiredState { Ref.clock = Ref.clock expiredState + 1, Ref.voted = 3, Ref.tallies = [0,70,50] }]
  reissued = fixture 34 (successor openA) (Ref.Propose 1 1 42001) [Ref.Continue proposed]
  overdraw = fixture 35 initial (Ref.Transfer 0 2 200) (outputs shiftFirst)
  earlyExecution = fixture 36 tieExpired Ref.Execute (outputs executeB)
  successfulRefund = fixture 37 (successor voteLast) Ref.Recover (outputs tieRefund)
  duplicate = executeA
    { coin = Coin (coinState (coin executeA)) (\cmr -> D.Outpoint (D.txid (fixtureTx executeA cmr)) 1)
    , serial = 40
    , edit = inputEdit 0 (\input -> input
        { D.sigTxiTxo = D.TxOutput 74999 (BL.fromStrict (payeeScript Ref.Treasury)) })
    }
  negatives =
    [ ("transfer signed by a different account", shiftFirst { signer = unauthorized })
    , ("delegation signed by a different account", undelegate { signer = unauthorized })
    , ("proposal signed by a different account", openA { signer = unauthorized })
    , ("ballot signed by a different account", voteFor { signer = unauthorized })
    , ("transfer spends more voting units than the account owns", overdraw)
    , ("signed transfer attempts to mint one extra voting unit", alterSuccessor
        (\state -> state { Ref.balances = 71 : H.tail (Ref.balances state) }) shiftFirst)
    , ("proposal snapshot counts an undelegated balance", alterSuccessor (\state -> state { Ref.weights = [70,50,181] }) openA)
    , ("second proposal tries to overwrite the active snapshot", reissued)
    , ("post-snapshot delegation tries to rewrite the snapshot", alterSuccessor
        (\state -> state { Ref.weights = Ref.power state }) delegateAfter)
    , ("for ballot tries to count current 120 instead of snapshot 70", alterSuccessor (\state -> state { Ref.tallies = [0,120,0] }) voteFor)
    , ("old state opening substitutes the current weights", voteFor { opening = (coinState (successor delegateAfter)) { Ref.weights = [120,0,0] } })
    , ("same voter tries to cast a second ballot", doubleVote)
    , ("relabel a signed zero-weight ballot while preserving the exact transaction", voteLast
        { action = Ref.Vote 2 1, signedAction = Just (Ref.Vote 2 0) })
    , ("unused voter tries to cast after the final slot", lateVote)
    , ("permissionless tick lacks CSV1", advanceA { edit = sequenceEdit 0 })
    , ("queue before voting ends despite sufficient votes", prematureQueue)
    , ("strict tie cannot queue despite sufficient quorum", makeQueue 38 tieExpired)
    , ("positive majority cannot queue without quorum", makeQueue 39 noQuorumExpired)
    , ("defeated proposal cannot execute", earlyExecution)
    , ("successful proposal cannot take failure refund", successfulRefund)
    , ("queue tries to change the committed target", alterSuccessor (\state -> state { Ref.phase = 4 }) queueA)
    , ("queue tries to change the committed payment", alterSuccessor (\state -> state { Ref.proposalAmount = 25002 }) queueA)
    , ("queued execution before CSV2", executeA { edit = sequenceEdit 1 })
    , ("redirect the actual approved payout", executeA { edit = redirect 0 })
    , ("increase the payout and reduce the remainder by one satoshi", executeA { edit = amountEdit 0 1 . amountEdit 1 (-1) })
    , ("redirect the actual treasury remainder", executeA { edit = redirect 1 })
    , ("append an unauthorized terminal output", executeA { edit = \tx -> tx { D.sigTxOut = V.snoc (D.sigTxOut tx) (mkOutput 0 (unhex "6a")) } })
    , ("redirect the exact failure refund", tieRefund { edit = redirect 0 })
    , ("executed treasury remainder cannot replay the queued state", duplicate)
    , ("actual current state script differs from the Taproot opening", shiftFirst
        { edit = inputEdit 0 (\input -> input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoScript = BL.fromStrict (keyScript feeKey) } }) })
    , ("actual state treasury is underfunded", shiftFirst { edit = inputEdit 0 (spentValue (Ref.treasury - 1)) })
    , ("incorrect separate fee input value", shiftFirst { edit = inputEdit 1 (spentValue (Ref.fee + 1)) })
    , ("state input moved to index 1", shiftFirst { currentIndex = 1, edit = \tx -> tx { D.sigTxIn = V.reverse (D.sigTxIn tx) } })
    ]
