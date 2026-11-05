{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | A fully funded native cliff stream with a transferable recipient right.
module JetDiscovery.Corpus.SablierStream (entry, streamKernel, streamedAt, Proof) where

import Prelude hiding (drop, take, not)
import qualified Prelude as H
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import qualified Data.Word as DW
import Simplicity.Digest (Hash256)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
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
import qualified JetDiscovery.Ref.SablierStream as Ref
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

type StateW = ((Word8, Word8), (Word32, (Word64, Word64)))
type SigW = G.SigW
type WithdrawW = (Word64, SigW)
type CancelW = (Word32, (SigW, SigW))
type ActionW = Either SigW (Either WithdrawW (Either SigW CancelW))
type Proof = (StateW, ActionW)
type Payout = (Word64, Word256)
type Plan = (Either StateW Payout, Either () Payout)

senderSecret, oracleSecret, feeSecret :: Integer
senderSecret = 5110
oracleSecret = 5440
feeSecret = 5550

recipientSecrets :: [Integer]
recipientSecrets = [5220, 5330]

pubkey :: Integer -> Word256
pubkey = w256 . R.pubkeyOf

keyScript :: Integer -> BS.ByteString
keyScript secret = unhex "5120" <> R.bytesFromInt (R.pubkeyOf secret)

payeeScript :: Ref.Payee -> BS.ByteString
payeeScript Ref.Sender = keyScript senderSecret
payeeScript (Ref.Recipient owner) = keyScript (recipientSecrets H.!! fromInteger owner)

phaseW, ownerW :: Core t => t StateW Word8
phaseW = ooh
ownerW = oih

heightW :: Core t => t StateW Word32
heightW = ioh

withdrawnW, refundedW :: Core t => t StateW Word64
withdrawnW = iioh
refundedW = iih >>> ih

stateW :: Ref.State -> StateW
stateW state = ((w8 (toInteger (fromEnum (Ref.phase state))), w8 (Ref.owner state)),
  (w32 (Ref.lastHeight state), (w64 (Ref.withdrawn state), w64 (Ref.refunded state))))

phaseIs :: (Assert t, TyC a) => t a StateW -> Integer -> t a Bit
phaseIs state phase = G.is (state >>> phaseW) (konst (w8 phase))

remaining :: Assert t => t StateW Word64
remaining = G.select (phaseIs iden 0) (G.k 0)
  (G.sub (G.sub (G.k Ref.deposit) withdrawnW) refundedW)

validHeight :: (Assert t, TyC a) => t a Word32 -> t a ()
validHeight height = (height &&& konst (w32 Ref.heightLimit)) >>> A.lt word32 >>> verify

monotone :: (Assert t, TyC a) => t a Word32 -> t a Word32 -> t a ()
monotone previous current = (previous &&& current) >>> A.le word32 >>> verify

validState :: Assert t => t StateW ()
validState = G.select (phaseIs iden 0) (G.same iden (konst (stateW Ref.pending)))
  (G.allChecks
    [ (ownerW &&& konst (w8 1)) >>> A.le word8 >>> verify
    , validHeight heightW
    , G.nonzero remaining
    , G.select (phaseIs iden 1) (G.same refundedW (G.k 0))
        (G.allChecks [phaseIs iden 2 >>> verify, G.nonzero refundedW])
    ])

stateHash :: Assert t => t StateW Word256
stateHash = (iden &&& (unit >>> ctx8InitTag Ref.stateTag))
  >>> T.append phaseW ctx8Add1 >>> T.append ownerW ctx8Add1 >>> T.append heightW ctx8Add4
  >>> T.append withdrawnW ctx8Add8 >>> T.append refundedW ctx8Add8 >>> ih >>> ctx8Finalize

-- The bounded schedule keeps steps * (streamable * granularity) in Word64.
-- Reassociating the product does not change the source's single final floor.
streamedAt :: Assert t => t Word32 Word64
streamedAt = G.select (before Ref.startHeight) (G.k 0)
  (G.select (before Ref.cliffHeight) (G.k Ref.startUnlock)
    (G.select (before Ref.endHeight) linear (G.k Ref.deposit)))
 where
  before height = (iden &&& konst (w32 height)) >>> A.lt word32
  elapsed = (iden &&& konst (w32 Ref.cliffHeight)) >>> A.subtract word32 >>> ih
  steps = (elapsed &&& konst (w32 Ref.granularity)) >>> A.divide word32
  unlocked = Ref.startUnlock + Ref.cliffUnlock
  rateNumerator = (Ref.deposit - unlocked) * Ref.granularity
  scaled = (steps &&& konst (w32 rateNumerator)) >>> A.multiply word32
  portion = (scaled &&& G.k (Ref.endHeight - Ref.cliffHeight)) >>> A.divide word64
  linear = G.add (G.k unlocked) portion

inputAt i primitiveType = konst (w32 i) >>> primitive primitiveType >>> verify

fundingChecks :: (Simplicity t, Primitive t) => t StateW Word256 -> t StateW ()
fundingChecks scriptFor = G.allChecks
  [ validState
  , G.same (unit >>> primitive P.CurrentIndex) (konst (w32 0))
  , G.same (unit >>> Tx.numInputs) (konst (w32 2))
  , (inputAt 0 P.InputPrevOutpoint &&& inputAt 1 P.InputPrevOutpoint) >>> eq >>> not iden >>> verify
  , loadState stateHash
  , G.same (inputAt 0 P.InputScriptHash) scriptFor
  , G.same (inputAt 0 P.InputValue) (G.add remaining (G.k Ref.carrier))
  ]

feeCheck :: (Simplicity t, Primitive t, TyC a) => Integer -> t a ()
feeCheck extra = G.same (inputAt 1 P.InputValue) (G.k (Ref.fee + extra))

requireSignature :: (Simplicity t, Primitive t, TyC a) => t a Word256 -> t a SigW -> t a ()
requireSignature key signature = ((key &&& (unit >>> sigMsg)) &&& signature) >>> Secp.bip_0340_verify

ownerKey, ownerDestination :: Assert t => t StateW Word256
ownerKey = chooseOwner (pubkey (recipientSecrets H.!! 0)) (pubkey (recipientSecrets H.!! 1))
ownerDestination = chooseOwner (G.scriptHash (payeeScript (Ref.Recipient 0)))
  (G.scriptHash (payeeScript (Ref.Recipient 1)))

chooseOwner :: (Assert t, TyC a) => a -> a -> t StateW a
chooseOwner first second = G.select (G.is ownerW (konst (w8 0))) (konst first) (konst second)

senderDestination :: (Core t, TyC a) => t a Word256
senderDestination = konst (G.scriptHash (payeeScript Ref.Sender))

continueOnly :: (Core t, TyC a) => t a StateW -> t a Plan
continueOnly next = injl next &&& injl unit

continueAndPay :: (Core t, TyC a) => t a StateW -> t a Payout -> t a Plan
continueAndPay next payout = injl next &&& injr payout

payOnly :: (Core t, TyC a) => t a Payout -> t a Plan
payOnly payout = injr payout &&& injl unit

payTwice :: (Core t, TyC a) => t a Payout -> t a Payout -> t a Plan
payTwice first second = injr first &&& injr second

applyPlan :: (Simplicity t, Primitive t) => t StateW Word256 -> t Plan ()
applyPlan scriptFor = G.allChecks
  [ oh >>> copair ((G.add remaining (G.k Ref.carrier) &&& scriptFor) >>> pay 0) (pay 0)
  , ih >>> copair (count 1) (G.allChecks [pay 1, count 2])
  ]
 where
  pay index = G.allChecks [G.same oh (G.outVal index), G.same ih (G.outScript index)]
  count n = G.same (unit >>> Tx.numOutputs) (konst (w32 n))

fundAction :: (Simplicity t, Primitive t) => t (SigW, StateW) Plan
fundAction = (checks &&& continueOnly (konst (stateW Ref.funded))) >>> ih
 where
  checks = G.allChecks
    [ phaseIs ih 0 >>> verify
    , requireSignature (konst (pubkey senderSecret)) oh
    , feeCheck Ref.deposit
    , G.same (inputAt 1 P.InputScriptHash) senderDestination
    ]

transferAction :: (Simplicity t, Primitive t) => t (SigW, StateW) Plan
transferAction = (checks &&& continueOnly next) >>> ih
 where
  checks = G.allChecks
    [ phaseIs ih 0 >>> not iden >>> verify
    , requireSignature (ih >>> ownerKey) oh
    , feeCheck 0
    ]
  next = ((ih >>> phaseW) &&& (ih >>> chooseOwner (w8 1) (w8 0))) &&& (ih >>> ih)

withdrawAction :: forall t. (Simplicity t, Primitive t) => t Word32 Word64 -> t (WithdrawW, StateW) Plan
withdrawAction vest = (checks &&& G.select terminal (payTwice payout carrierPayout) (continueAndPay next payout)) >>> ih
 where
  height :: t (WithdrawW, StateW) Word32
  height = unit >>> primitive P.LockTime
  amount = ooh
  live = phaseIs ih 1
  available = G.select live (G.sub (height >>> vest) (ih >>> withdrawnW)) (ih >>> remaining)
  nextHeight = G.select live height (ih >>> heightW)
  checks = G.allChecks
    [ phaseIs ih 0 >>> not iden >>> verify
    , requireSignature (ih >>> ownerKey) oih
    , feeCheck 0
    , validHeight height
    , G.select live (G.allChecks [monotone (ih >>> heightW) height, height >>> TL.checkLockHeight]) unit
    , G.nonzero amount
    , G.le amount available
    ]
  payout = amount &&& (ih >>> ownerDestination)
  carrierPayout = G.k Ref.carrier &&& senderDestination
  terminal = G.is amount (ih >>> remaining)
  next = (ih >>> oh) &&& (nextHeight &&& (G.add (ih >>> withdrawnW) amount &&& (ih >>> refundedW)))

valuationMessage :: (Simplicity t, Primitive t) => t Word32 Word256
valuationMessage = (((unit >>> ctx8InitTag Ref.valuationTag) &&& (unit >>> sigMsg)) >>> ctx8Add32)
  &&& iden >>> ctx8Add4 >>> ctx8Finalize

cancelAction :: forall t. (Simplicity t, Primitive t) => t Word32 Word64 -> t (CancelW, StateW) Plan
cancelAction vest = (checks &&& (iden &&& (height >>> vest))) >>> ih >>> decide
 where
  height :: t (CancelW, StateW) Word32
  height = ooh
  checks = G.allChecks
    [ phaseIs ih 1 >>> verify
    , requireSignature (konst (pubkey senderSecret)) (oh >>> ioh)
    , (((konst (pubkey oracleSecret)) &&& (height >>> valuationMessage)) &&& (oh >>> iih)) >>> Secp.bip_0340_verify
    , feeCheck 0
    , validHeight height
    , (konst (w32 0) &&& height) >>> A.lt word32 >>> verify
    , G.same height (unit >>> primitive P.LockTime)
    , height >>> TL.checkLockHeight
    , monotone (ih >>> heightW) height
    ]
  decide :: t ((CancelW, StateW), Word64) Plan
  decide = (G.allChecks [G.lt ih (G.k Ref.deposit), G.le oldWithdrawn ih] &&&
      G.select (G.is oldWithdrawn ih) (payOnly terminalRefund) (continueAndPay next refundPayout)) >>> ih
   where
    oldWithdrawn = (oh >>> ih) >>> withdrawnW
    refund = G.sub (G.k Ref.deposit) ih
    terminalRefund = G.add refund (G.k Ref.carrier) &&& senderDestination
    refundPayout = refund &&& senderDestination
    next = (konst (w8 2) &&& (oh >>> ih >>> ownerW))
      &&& ((oh >>> height) &&& (oldWithdrawn &&& refund))

streamKernel :: forall t. (Simplicity t, Primitive t) => t Proof ()
streamKernel = ((oh >>> fundingChecks scriptFor) &&& ((ih &&& oh) >>> actions)) >>> ih >>> applyPlan scriptFor
 where
  scriptFor :: t StateW Word256
  scriptFor = stateScriptHash stateHash
  vest :: t Word32 Word64
  vest = streamedAt
  actions :: t (ActionW, StateW) Plan
  actions = match fundAction (match (withdrawAction vest) (match transferAction (cancelAction vest)))

data Coin = Coin Ref.State (Hash256 -> D.Outpoint)

coinState :: Coin -> Ref.State
coinState (Coin state _) = state

data Fixture = Fixture
  { coin :: Coin
  , action :: Ref.Action
  , destinations :: [Ref.Destination]
  , feeOutpoint :: DW.Word32
  , changeTx :: D.SigTx -> D.SigTx
  , currentIndex :: DW.Word32
  , opening :: Ref.State
  , signer :: Integer
  , valuationOverride :: Maybe (Hash256 -> SigW)
  }

fixture :: DW.Word32 -> Coin -> Ref.Action -> [Ref.Destination] -> Fixture
fixture index old requested outputs = Fixture old requested outputs index id 0 state secret Nothing
 where
  state = coinState old
  secret = case requested of
    Ref.Fund -> senderSecret
    Ref.Cancel _ -> senderSecret
    _ -> recipientSecrets H.!! fromInteger (Ref.owner state)

honest :: DW.Word32 -> Coin -> Ref.Action -> Fixture
honest index old requested = case Ref.transition (coinState old) requested of
  Just outputs -> fixture index old requested outputs
  Nothing -> error ("invalid Sablier fixture " ++ show requested)

fixtureTx :: Fixture -> Hash256 -> D.SigTx
fixtureTx f cmr = changeTx f (mkTx 2 [stateInput, fundingInput] (map output (destinations f)) (fromInteger lock))
 where
  Coin state previous = coin f
  stateInput = mkInput (previous cmr) (fromInteger (Ref.remaining state + Ref.carrier))
    (BL.fromStrict (stateScript cmr (Ref.stateDigest state))) 0xfffffffe
  funds = case action f of
    Ref.Fund -> (Ref.deposit + Ref.fee, keyScript senderSecret)
    _ -> (Ref.fee, keyScript feeSecret)
  fundingInput = mkInput (dummyOutpoint (feeOutpoint f)) (fromInteger (fst funds)) (BL.fromStrict (snd funds)) 0xfffffffe
  lock = case action f of
    Ref.Withdraw height _ -> height
    Ref.Cancel height -> height
    _ -> 0
  output (Ref.Continuation next) = mkOutput (fromInteger (Ref.remaining next + Ref.carrier)) (stateScript cmr (Ref.stateDigest next))
  output (Ref.Payout who amount) = mkOutput (fromInteger amount) (payeeScript who)

fixtureEnv f cmr = mkEnv (fixtureTx f cmr) (currentIndex f)
  (\_ -> stateTap cmr (Ref.stateDigest (coinState (coin f)))) cmr

successor :: Fixture -> Coin
successor f = case destinations f of
  Ref.Continuation next : _ -> Coin next (\cmr -> D.Outpoint (D.txid (fixtureTx f cmr)) 0)
  _ -> error "terminal Sablier fixture has no successor"

transactionMessage :: Fixture -> Hash256 -> BS.ByteString
transactionMessage f cmr = case fixtureEnv f cmr >>= (\env -> J.fastEval sigMsg env ()) of
  Just message -> w256ToBytes message
  Nothing -> error "Sablier fixture environment or signature message"

signValuation :: Integer -> Integer -> Fixture -> Hash256 -> SigW
signValuation key height f cmr = G.sigW (signMsg key (Ref.valuationDigest (transactionMessage f cmr) height))

fixtureProof :: Fixture -> Hash256 -> Proof
fixtureProof f cmr = (stateW (opening f), proofAction)
 where
  signature = G.sigW (signMsg (signer f) (transactionMessage f cmr))
  proofAction = case action f of
    Ref.Fund -> Left signature
    Ref.Withdraw _ amount -> Right (Left (w64 amount, signature))
    Ref.Transfer -> Right (Right (Left signature))
    Ref.Cancel height -> Right (Right (Right (w32 height, (signature, valuation height))))
  valuation height = maybe (signValuation oracleSecret height f cmr) ($ cmr) (valuationOverride f)

modifyInput :: Int -> (D.SigTxInput -> D.SigTxInput) -> D.SigTx -> D.SigTx
modifyInput index modify tx = tx { D.sigTxIn = V.imap replace (D.sigTxIn tx) }
 where replace i input = if i == index then modify input else input

modifyOutput :: Int -> (D.TxOutput -> D.TxOutput) -> D.SigTx -> D.SigTx
modifyOutput index modify tx = tx { D.sigTxOut = V.imap replace (D.sigTxOut tx) }
 where replace i output = if i == index then modify output else output

setSpentValue :: Integer -> D.SigTxInput -> D.SigTxInput
setSpentValue value input = input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoValue = fromInteger value } }

setSpentScript :: BS.ByteString -> D.SigTxInput -> D.SigTxInput
setSpentScript script input = input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoScript = BL.fromStrict script } }

entry :: Entry
entry = Entry "app-sablier-cancelable-cliff-stream"
  "Sablier linear cliff stream with funded partial claims, transfer and cancellation"
  "Sablier Lockup and LockupMath at 18fce3d1cad30f1e641fe9eff3a913ee5cdd54ae"
  BitcoinApp
  (Derived "Exact pinned linear cliff formula and independent Integer lifecycle; linked native funding, claims, transfers, refunds and terminal outputs; signed valuation replay and actual transaction negatives")
  [ "One fixed cancelable and transferable BTC stream, with two possible recipient keys and an original sender key"
  , "Creation consumes a pending 10000-sat carrier UTXO and a separate sender-script input funding the entire 37111-sat deposit plus 1000 sats of fee"
  , "Current input 0 script/value authenticate the complete old state; every continuation retains the same executable leaf and exact remaining deposit plus carrier"
  , "Source start/cliff unlocks and integer granularity use block heights; live claims use enabled nLockTime as a conservative lower bound"
  , "Cancellation requires sender authorization and a distinct oracle BIP340 valuation event for the actual sig_all_hash and explicit height; height equals enabled nLockTime and is nondecreasing"
  , "The oracle is trusted to attest the valuation at signing. The transaction can confirm later, and Bitcoin enforces only its lower height bound"
  , "Cancellation refunds the unstreamed amount once and freezes the vested unclaimed credit; recipient rights remain transferable while credit remains"
  , "Every partial claim pays the current recipient, every refund pays the original sender, and the original sender recovers the separate carrier at depletion"
  , "An independent 1000-sat fee input funds later transitions. Native state serialization replaces the foreign NFT and ERC20 ledger, and uses one aggregate witness"
  ] make vectors
 where
  make = boundProgram streamKernel
  cmr = progCmr (make (stateW Ref.pending, Left G.zeroSig))
  vectors = [Vector name (fixtureEnv f) (fixtureProof f cmr) expected | (name, f, expected) <- cases]

cases :: [(String, Fixture, Expect)]
cases = map accept positives ++ map reject negatives
 where
  accept (name, f) = (name, f, Accept)
  reject (name, f) = (name, f, Reject)
  initial = Coin Ref.pending (const (dummyOutpoint 100))
  funding = honest 201 initial Ref.Fund
  fundedCoin = successor funding
  atStart = honest 202 fundedCoin (Ref.Withdraw Ref.startHeight 1500)
  beforeCliff = honest 203 (successor atStart) (Ref.Withdraw (Ref.cliffHeight - 1) 1000)
  transferLive = honest 204 (successor beforeCliff) Ref.Transfer
  atCliff = honest 205 (successor transferLive) (Ref.Withdraw Ref.cliffHeight 2000)
  firstStep = honest 206 (successor atCliff) (Ref.Withdraw (Ref.cliffHeight + Ref.granularity + 1) 3000)
  cancel = honest 207 (successor firstStep) (Ref.Cancel (Ref.cliffHeight + 15))
  canceledCoin = successor cancel
  transferCanceled = honest 208 canceledCoin Ref.Transfer
  claimFrozen = honest 209 (successor transferCanceled) (Ref.Withdraw 0 2000)
  lastFrozenCoin = successor claimFrozen
  closeFrozen = honest 210 lastFrozenCoin (Ref.Withdraw 0 (Ref.remaining (coinState lastFrozenCoin)))
  closeMatured = honest 211 fundedCoin (Ref.Withdraw Ref.endHeight Ref.deposit)
  cancelBeforeStart = honest 212 fundedCoin (Ref.Cancel (Ref.startHeight - 1))
  cancelNoCredit = honest 213 (successor beforeCliff) (Ref.Cancel (Ref.cliffHeight - 1))
  positives =
    [ ("sender funds the actual full stream deposit", funding)
    , ("withdraw part of the start unlock at the start height", atStart)
    , ("withdraw the remaining start credit before the cliff", beforeCliff)
    , ("transfer the live right to the other recipient", transferLive)
    , ("new owner withdraws part of the exact cliff unlock", atCliff)
    , ("withdraw after the first complete granularity step", firstStep)
    , ("sender cancels after partial claims with an exact refund and retained credit", cancel)
    , ("transfer the frozen recipient right after cancellation", transferCanceled)
    , ("new owner makes a partial frozen credit claim without a new valuation", claimFrozen)
    , ("terminal frozen claim returns the carrier separately to the sender", closeFrozen)
    , ("terminal live withdrawal releases the entire matured stream", closeMatured)
    , ("cancel before start returns full deposit plus carrier", cancelBeforeStart)
    , ("cancel when prior claims consumed all vested credit", cancelNoCredit)
    ]
  forgedWithdrawal index old height amount =
    let state = coinState old
        next = state { Ref.lastHeight = height, Ref.withdrawn = Ref.withdrawn state + amount }
    in fixture index old (Ref.Withdraw height amount) [Ref.Continuation next, Ref.Payout (Ref.Recipient (Ref.owner state)) amount]
  stale = (honest 214 (successor firstStep) (Ref.Cancel (Ref.cliffHeight + 15)))
    { action = Ref.Cancel (Ref.cliffHeight + Ref.granularity)
    , destinations = case Ref.transition ((coinState (successor firstStep)) { Ref.lastHeight = Ref.cliffHeight })
        (Ref.Cancel (Ref.cliffHeight + Ref.granularity)) of
          Just outputs -> outputs
          Nothing -> error "Sablier stale valuation fixture"
    }
  frozenExcess = Ref.remaining (coinState canceledCoin) + 1
  forgedClose = fixture 215 canceledCoin (Ref.Withdraw Ref.endHeight frozenExcess)
    [Ref.Payout (Ref.Recipient 1) frozenExcess, Ref.Payout Ref.Sender (Ref.carrier - 1)]
  repeatCancel = fixture 216 canceledCoin (Ref.Cancel (Ref.endHeight - 1)) (destinations cancel)
  matureCancel = fixture 217 fundedCoin (Ref.Cancel Ref.endHeight) (destinations cancelBeforeStart)
  wrongPayee = keyScript feeSecret
  negatives =
    [ ("short actual deposit input", funding { changeTx = modifyInput 1 (setSpentValue (Ref.deposit + Ref.fee - 1)) })
    , ("wrong actual funding input script", funding { changeTx = modifyInput 1 (setSpentScript wrongPayee) })
    , ("funder signature belongs to a different key", funding { signer = feeSecret })
    , ("withdraw before the start unlock", forgedWithdrawal 218 fundedCoin (Ref.startHeight - 1) 1500)
    , ("claim the first granularity increment one block early",
        forgedWithdrawal 219 (successor atCliff) (Ref.cliffHeight + Ref.granularity - 1) 3000)
    , ("disable nLockTime with final sequences", atStart { changeTx = \tx -> tx
        { D.sigTxIn = V.map (\input -> input { D.sigTxiSequence = 0xffffffff }) (D.sigTxIn tx) } })
    , ("transfer signed by the proposed owner instead of the current owner", transferLive { signer = recipientSecrets H.!! 1 })
    , ("withdrawal by the prior owner after transfer", atCliff { signer = recipientSecrets H.!! 0 })
    , ("cancel with an unauthorized valuation key", cancel { valuationOverride = Just (signValuation feeSecret (Ref.cliffHeight + 15) cancel) })
    , ("cancel with an authenticated but decreasing height at the same vesting step", stale)
    , ("signed valuation height differs from actual nLockTime", cancel { changeTx = \tx -> tx { D.sigTxLock = fromInteger (Ref.cliffHeight + 16) } })
    , ("valuation signature replays onto a different actual state outpoint", cancel
        { changeTx = modifyInput 0 (\input -> input { D.sigTxiPreviousOutpoint = dummyOutpoint 888 })
        , valuationOverride = Just (signValuation oracleSecret (Ref.cliffHeight + 15) cancel) })
    , ("sender authorization missing despite a valid oracle event", cancel { signer = feeSecret })
    , ("second cancellation from an authentic canceled state", repeatCancel)
    , ("cancel at the settled end height", matureCancel)
    , ("divert the sender refund with fresh authorization", cancel
        { changeTx = modifyOutput 1 (\output -> output { D.txoScript = BL.fromStrict wrongPayee }) })
    , ("inflate the retained recipient credit by one satoshi", cancel
        { changeTx = modifyOutput 0 (\output -> output { D.txoValue = D.txoValue output + 1 }) })
    , ("withdraw above the frozen credit after end height", forgedClose)
    , ("wrong actual current UTXO value", atStart { changeTx = modifyInput 0 (setSpentValue (Ref.deposit + Ref.carrier - 1)) })
    , ("wrong actual current UTXO script with the same Taproot metadata", atStart { changeTx = modifyInput 0 (setSpentScript wrongPayee) })
    , ("forge the opened old withdrawal counter", atStart { opening = Ref.funded { Ref.withdrawn = 1 } })
    , ("spend the funded state at current input 1", atStart { currentIndex = 1, changeTx = \tx -> tx
        { D.sigTxIn = V.reverse (D.sigTxIn tx) } })
    , ("actual continuation commits a different recipient owner", atStart { destinations = case destinations atStart of
        Ref.Continuation next : rest -> Ref.Continuation next { Ref.owner = 1 } : rest
        _ -> error "missing Sablier continuation" })
    , ("divert the partial recipient payout", atStart
        { changeTx = modifyOutput 1 (\output -> output { D.txoScript = BL.fromStrict wrongPayee }) })
    , ("divert the terminal carrier", closeMatured
        { changeTx = modifyOutput 1 (\output -> output { D.txoScript = BL.fromStrict wrongPayee }) })
    ]
