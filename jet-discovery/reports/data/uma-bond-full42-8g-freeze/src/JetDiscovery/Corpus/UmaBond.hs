{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | Native optimistic assertion, counterbond and settlement under one leaf.
module JetDiscovery.Corpus.UmaBond (entry, bondFee, bondKernel) where

import Prelude hiding (not)
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
import qualified JetDiscovery.Ref.UmaBond as Ref
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

type StateW = (Word8, (Word64, Word256))
type SigW = G.SigW
type AssertionW = (Word256, (Word64, SigW))
type VerdictW = (Bit, SigW)
type ActionW = Either AssertionW (Either SigW (Either () VerdictW))
type Proof = (StateW, ActionW)
type Plan = Either StateW (Either Word64 (Bit, Word64))

secret :: Ref.Payee -> Integer
secret Ref.Asserter = 6101
secret Ref.Challenger = 6202
secret Ref.Store = 6303
secret Ref.SetupSponsor = 6404

arbitratorSecret, feeSecret :: Integer
arbitratorSecret = 6505
feeSecret = 6606

public :: Integer -> Word256
public = w256 . R.pubkeyOf

keyScript :: Integer -> BS.ByteString
keyScript key = unhex "5120" <> R.bytesFromInt (R.pubkeyOf key)

payeeScript :: Ref.Payee -> BS.ByteString
payeeScript = keyScript . secret

stateW :: Ref.State -> StateW
stateW state = (w8 (toInteger (fromEnum (Ref.phase state))),
  (w64 (Ref.bond state), w256FromBytes (Ref.assertion state)))

phaseIs :: (Assert t, TyC a) => t a StateW -> Integer -> t a Bit
phaseIs state phase = G.is (state >>> oh) (konst (w8 phase))

bondBound :: Assert t => t Word64 ()
bondBound = G.allChecks [G.le (G.k Ref.minimumBond) iden, G.le iden (G.k Ref.maximumBond)]

validState :: Assert t => t StateW ()
validState = G.select (phaseIs iden 0) (G.same iden (konst (stateW Ref.setup)))
  (G.allChecks [(oh &&& konst (w8 2)) >>> A.le word8 >>> verify, ioh >>> bondBound])

stateValue :: Assert t => t StateW Word64
stateValue = G.add (G.k Ref.carrier) (G.select (phaseIs iden 2) (G.add ioh ioh) ioh)

stateHash :: Assert t => t StateW Word256
stateHash = (iden &&& (unit >>> ctx8InitTag Ref.stateTag))
  >>> T.append oh ctx8Add1 >>> T.append ioh ctx8Add8 >>> T.append iih ctx8Add32 >>> ih >>> ctx8Finalize

at :: (Assert t, Primitive t, TyC a, TyC b) => Integer -> P.Prim Word32 (Either () b) -> t a b
at index primitiveType = konst (w32 index) >>> primitive primitiveType >>> verify

distinct :: (Assert t, Primitive t, TyC a) => Integer -> Integer -> t a ()
distinct first second = (at first P.InputPrevOutpoint &&& at second P.InputPrevOutpoint)
  >>> eq >>> not iden >>> verify

fundingState :: (Simplicity t, Primitive t) => t StateW Word256 -> t StateW ()
fundingState scriptFor = G.allChecks
  [ validState
  , G.same (unit >>> primitive P.CurrentIndex) (konst (w32 0))
  , distinct 0 1
  , loadState stateHash
  , G.same (at 0 P.InputValue) stateValue
  , G.same (at 0 P.InputScriptHash) scriptFor
  ]

inputCount :: (Simplicity t, Primitive t, TyC a) => Integer -> t a ()
inputCount count = G.same (unit >>> Tx.numInputs) (konst (w32 count))

depositChecks :: (Simplicity t, Primitive t, TyC a) => Ref.Payee -> t a Word64 -> t a ()
depositChecks role amount = G.allChecks
  [ inputCount 3, distinct 0 2, distinct 1 2
  , G.same (at 1 P.InputValue) amount
  , G.same (at 1 P.InputScriptHash) (konst (G.scriptHash (payeeScript role)))
  , G.same (at 2 P.InputValue) (G.k Ref.fee)
  ]

settlementFee :: (Simplicity t, Primitive t, TyC a) => t a ()
settlementFee = G.allChecks [inputCount 2, G.same (at 1 P.InputValue) (G.k Ref.fee)]

authorize :: (Simplicity t, Primitive t, TyC a) => Ref.Payee -> t a SigW -> t a ()
authorize role signature = ((konst (public (secret role)) &&& (unit >>> sigMsg)) &&& signature)
  >>> Secp.bip_0340_verify

assertionHash :: (Assert t, Primitive t) => t (Word256, Word64) Word256
assertionHash = (iden &&& (unit >>> ctx8InitTag Ref.assertionTag))
  >>> T.append oh ctx8Add32 >>> T.append ih ctx8Add8
  >>> T.append (at 0 P.InputPrevOutpoint >>> oh) ctx8Add32
  >>> T.append (at 0 P.InputPrevOutpoint >>> ih) ctx8Add4 >>> ih >>> ctx8Finalize

verdictHash :: (Simplicity t, Primitive t) => t (Word256, Bit) Word256
verdictHash = (iden &&& (unit >>> ctx8InitTag Ref.verdictTag))
  >>> T.append oh ctx8Add32 >>> T.append (G.select ih (konst (w8 1)) (konst (w8 0))) ctx8Add1
  >>> T.append (unit >>> sigMsg) ctx8Add32 >>> ih >>> ctx8Finalize

assertAction :: (Simplicity t, Primitive t) => t (AssertionW, StateW) Plan
assertAction = (checks &&& injl next) >>> ih
 where
  claim = ooh
  amount = oh >>> ioh
  checks = G.allChecks [phaseIs ih 0 >>> verify, amount >>> bondBound,
    authorize Ref.Asserter (oh >>> iih), depositChecks Ref.Asserter amount]
  next = konst (w8 1) &&& (amount &&& ((claim &&& amount) >>> assertionHash))

challengeAction :: (Simplicity t, Primitive t) => t (SigW, StateW) Plan
challengeAction = (checks &&& injl (konst (w8 2) &&& (ih >>> ih))) >>> ih
 where
  checks = G.allChecks [phaseIs ih 1 >>> verify, authorize Ref.Challenger oh,
    depositChecks Ref.Challenger (ih >>> ioh)]

refundAction :: (Simplicity t, Primitive t) => t ((), StateW) Plan
refundAction = (checks &&& injr (injl (ih >>> ioh))) >>> ih
 where
  checks = G.allChecks [phaseIs ih 1 >>> verify, settlementFee,
    konst (w16 Ref.delay) >>> TL.checkLockDistance]

resolveAction :: (Simplicity t, Primitive t) => t (VerdictW, StateW) Plan
resolveAction = (checks &&& injr (injr (ooh &&& (ih >>> ioh)))) >>> ih
 where
  message = ((ih >>> iih) &&& ooh) >>> verdictHash
  authorized = ((konst (public arbitratorSecret) &&& message) &&& oih) >>> Secp.bip_0340_verify
  checks = G.allChecks [phaseIs ih 2 >>> verify, settlementFee, authorized]

bondFee :: Core t => t Word64 Word64
bondFee = (iden &&& konst (w64 2)) >>> A.divide word64

applyPlan :: forall t. (Simplicity t, Primitive t) => t StateW Word256 -> t Plan ()
applyPlan scriptFor = copair continuation (copair refund resolution)
 where
  count :: TyC a => Integer -> t a ()
  count n = G.same (unit >>> Tx.numOutputs) (konst (w32 n))
  pay :: TyC a => Integer -> t a Word256 -> t a Word64 -> t a ()
  pay i script amount = G.allChecks [G.same (G.outVal i) amount, G.same (G.outScript i) script]
  destination :: TyC a => Ref.Payee -> t a Word256
  destination = konst . G.scriptHash . payeeScript
  carrierOutput :: TyC a => Integer -> t a ()
  carrierOutput i = pay i (destination Ref.SetupSponsor) (G.k Ref.carrier)
  continuation = G.allChecks [count 1, pay 0 scriptFor stateValue]
  refund = G.allChecks [count 2, pay 0 (destination Ref.Asserter) iden, carrierOutput 1]
  resolution = G.allChecks [count 3,
    pay 0 (G.select oh (destination Ref.Asserter) (destination Ref.Challenger))
      (G.sub (G.add ih ih) (ih >>> bondFee)),
    pay 1 (destination Ref.Store) (ih >>> bondFee), carrierOutput 2]

bondKernel :: forall t. (Simplicity t, Primitive t) => t Proof ()
bondKernel = ((oh >>> fundingState scriptFor) &&& ((ih &&& oh) >>> actions)) >>> ih >>> applyPlan scriptFor
 where
  scriptFor :: t StateW Word256
  scriptFor = stateScriptHash stateHash
  actions :: t (ActionW, StateW) Plan
  actions = match assertAction (match challengeAction (match refundAction resolveAction))

data Coin = Coin Ref.State (Hash256 -> D.Outpoint)

coinState :: Coin -> Ref.State
coinState (Coin state _) = state

data Fixture = Fixture
  { coin :: Coin
  , action :: Ref.Action
  , outputs :: [Ref.Destination]
  , serial :: DW.Word32
  , edit :: D.SigTx -> D.SigTx
  , currentIndex :: DW.Word32
  , opening :: Ref.State
  , signingKey :: Integer
  , verdictOverride :: Maybe (Hash256 -> SigW)
  }

origin :: D.Outpoint
origin = D.Outpoint (hashFromInteger 0x112233445566778899aabbccddeeff00112233445566778899aabbccddeeff00) 77

originFields :: (BS.ByteString, Integer)
originFields = (hashToBytes (D.opHash origin), toInteger (D.opIndex origin))

fixture :: DW.Word32 -> Coin -> Ref.Action -> [Ref.Destination] -> Fixture
fixture index old requested destinations = Fixture old requested destinations index id 0 (coinState old) key Nothing
 where
  key = case requested of
    Ref.Assert _ _ -> secret Ref.Asserter
    Ref.Challenge -> secret Ref.Challenger
    _ -> arbitratorSecret

honest :: DW.Word32 -> Coin -> Ref.Action -> Fixture
honest index old requested = case Ref.transition originFields (coinState old) requested of
  Just destinations -> fixture index old requested destinations
  Nothing -> error ("invalid UMA fixture " ++ show requested)

fixtureTx :: Fixture -> Hash256 -> D.SigTx
fixtureTx f cmr = edit f (mkTx 2 (stateInput : bondInputs ++ [feeInput]) (map output (outputs f)) 0)
 where
  Coin state previous = coin f
  sequenceValue = case action f of
    Ref.Refund distance -> fromInteger distance
    _ -> 0xfffffffe
  stateInput = mkInput (previous cmr) (fromInteger (Ref.stateValue state))
    (BL.fromStrict (stateScript cmr (Ref.stateDigest state))) sequenceValue
  fund role amount = mkInput (dummyOutpoint (2 * serial f + 200)) (fromInteger amount)
    (BL.fromStrict (payeeScript role)) 0xfffffffe
  bondInputs = case action f of
    Ref.Assert _ amount -> [fund Ref.Asserter amount]
    Ref.Challenge -> [fund Ref.Challenger (Ref.bond state)]
    _ -> []
  feeInput = mkInput (dummyOutpoint (2 * serial f + 201)) (fromInteger Ref.fee)
    (BL.fromStrict (keyScript feeSecret)) 0xfffffffe
  output (Ref.Continue next) = mkOutput (fromInteger (Ref.stateValue next)) (stateScript cmr (Ref.stateDigest next))
  output (Ref.Pay role amount) = mkOutput (fromInteger amount) (payeeScript role)

fixtureEnv f cmr = mkEnv (fixtureTx f cmr) (currentIndex f)
  (\_ -> stateTap cmr (Ref.stateDigest (coinState (coin f)))) cmr

successor :: Fixture -> Coin
successor f = case outputs f of
  [Ref.Continue next] -> Coin next (\cmr -> D.Outpoint (D.txid (fixtureTx f cmr)) 0)
  _ -> error "UMA settlement has no successor"

txMessage :: Fixture -> Hash256 -> BS.ByteString
txMessage f cmr = case fixtureEnv f cmr >>= (\env -> J.fastEval sigMsg env ()) of
  Just message -> w256ToBytes message
  Nothing -> error "UMA fixture signature message"

signVerdict :: Integer -> BS.ByteString -> Bool -> Fixture -> Hash256 -> SigW
signVerdict key claimIdentity outcome f cmr = G.sigW
  (signMsg key (Ref.verdictDigest claimIdentity outcome (txMessage f cmr)))

fixtureProof :: Fixture -> Hash256 -> Proof
fixtureProof f cmr = (stateW (opening f), proofAction)
 where
  signature = G.sigW (signMsg (signingKey f) (txMessage f cmr))
  proofAction = case action f of
    Ref.Assert claim amount -> Left (w256FromBytes claim, (w64 amount, signature))
    Ref.Challenge -> Right (Left signature)
    Ref.Refund _ -> Right (Right (Left ()))
    Ref.Resolve outcome -> Right (Right (Right (bit outcome, verdict outcome)))
  bit outcome = if outcome then Right () else Left ()
  verdict outcome = maybe
    (signVerdict (signingKey f) (Ref.assertion (opening f)) outcome f cmr)
    ($ cmr) (verdictOverride f)

inputEdit :: Int -> (D.SigTxInput -> D.SigTxInput) -> D.SigTx -> D.SigTx
inputEdit index modify tx = tx { D.sigTxIn = V.imap (\i input -> if i == index then modify input else input) (D.sigTxIn tx) }

outputEdit :: Int -> (D.TxOutput -> D.TxOutput) -> D.SigTx -> D.SigTx
outputEdit index modify tx = tx { D.sigTxOut = V.imap (\i output -> if i == index then modify output else output) (D.sigTxOut tx) }

spentValue :: Integer -> D.SigTxInput -> D.SigTxInput
spentValue amount input = input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoValue = fromInteger amount } }

spentScript :: BS.ByteString -> D.SigTxInput -> D.SigTxInput
spentScript script input = input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoScript = BL.fromStrict script } }

entry :: Entry
entry = Entry "app-uma-optimistic-bond-lifecycle"
  "UMA optimistic assertion with native BTC counterbond and verdict settlement"
  "UMA OptimisticOracleV3.sol at c8c3f67367afd1c767712a3dbe3c8cad01b9a4d8"
  BitcoinApp
  (Derived "Pinned default 50% Store formula, independent Integer bond accounting, linked native transaction fixtures and same-CMR authorization, identity, maturity and payout negatives")
  [ "One initialized native lineage with fixed asserter, challenger, Store, setup sponsor and arbitrator keys"
  , "An assertion adds a bounded 2000 to 1000000 satoshi bond from an actual asserter-script input. One challenge adds an equal actual challenger-script counterbond"
  , "Current input 0 authenticates the full spent state script and value. Assertion and challenge each consume three distinct inputs including an independent 1000-sat fee input"
  , "The native tagged assertion ID commits the claim digest, bond and raw setup outpoint. The arbitrator signs the ID, outcome and actual sig_all_hash context under a separate domain"
  , "Undisputed settlement is permissionless with CSV10. A challenge can race the matured refund until one spend consumes that UTXO, since CSV only sets a minimum coin age"
  , "Disputed settlement pays the selected winner twice the bond minus floor(bond/2), and pays that fee to the fixed Store. Both terminal paths return the separate 10000-sat carrier to the setup sponsor"
  , "Native fixed keys and serialized UTXOs provide the lifecycle for one lineage. The fixed arbitrator supplies the disputed truth value"
  ] make vectors
 where
  make = boundProgram bondKernel
  cmr = progCmr (make (stateW Ref.setup, Right (Right (Left ()))))
  vectors = [Vector name (fixtureEnv f) (fixtureProof f cmr) expected | (name, f, expected) <- cases]

cases :: [(String, Fixture, Expect)]
cases = [(name, f, Accept) | (name, f) <- positives] ++ [(name, f, Reject) | (name, f) <- negatives]
 where
  initial = Coin Ref.setup (const origin)
  claimA = hashToBytes (sha256 (unhex "617373657274696f6e2d41"))
  claimB = hashToBytes (sha256 (unhex "617373657274696f6e2d42"))
  oddAmount = 24001
  evenAmount = 24000
  fundedOdd = honest 1 initial (Ref.Assert claimA oddAmount)
  openOdd = successor fundedOdd
  challengedOdd = honest 2 openOdd Ref.Challenge
  disputedOdd = successor challengedOdd
  refundOdd = honest 3 openOdd (Ref.Refund Ref.delay)
  trueOdd = honest 4 disputedOdd (Ref.Resolve True)
  falseOdd = honest 5 disputedOdd (Ref.Resolve False)
  fundedEven = honest 6 initial (Ref.Assert claimB evenAmount)
  openEven = successor fundedEven
  challengedEven = (honest 7 openEven Ref.Challenge)
    { edit = inputEdit 0 (\input -> input { D.sigTxiSequence = fromInteger Ref.delay }) }
  falseEven = honest 8 (successor challengedEven) (Ref.Resolve False)
  fundedMinimum = honest 9 initial (Ref.Assert claimA Ref.minimumBond)
  fundedMaximum = honest 10 initial (Ref.Assert claimA Ref.maximumBond)
  refundEven = honest 11 openEven (Ref.Refund Ref.delay)
  positives =
    [ ("assertion escrows an actual odd bond and independent fee", fundedOdd)
    , ("one authorized challenge escrows an equal actual counterbond", challengedOdd)
    , ("permissionless exact undisputed refund at CSV10", refundOdd)
    , ("true verdict pays the asserter and floors the odd Store fee", trueOdd)
    , ("false verdict pays the challenger and floors the odd Store fee", falseOdd)
    , ("alternate assertion escrows the actual even bond", fundedEven)
    , ("challenge can race a refund at the CSV10 sequence", challengedEven)
    , ("even bond adjudication pays the exact Store half", falseEven)
    , ("actual minimum supported bond funds the assertion", fundedMinimum)
    , ("actual maximum supported bond funds the assertion", fundedMaximum)
    , ("the same even assertion also admits the matured refund", refundEven)
    ]
  invalidBond index amount = fixture index initial (Ref.Assert claimA amount)
    [Ref.Continue (Ref.State Ref.Asserted amount (Ref.assertionDigest claimA amount originFields))]
  redirect index = outputEdit index (\output -> output { D.txoScript = BL.fromStrict (keyScript feeSecret) })
  reviseAmount index delta = outputEdit index (\output -> output { D.txoValue = fromInteger (toInteger (D.txoValue output) + delta) })
  sequenceEdit value = inputEdit 0 (\input -> input { D.sigTxiSequence = value })
  wrongClaimIdentity = Ref.assertion (coinState (successor challengedEven))
  correctIdentity = Ref.assertion (coinState disputedOdd)
  repeatChallenge = fixture 12 disputedOdd Ref.Challenge (outputs challengedOdd)
  disputedRefund = fixture 13 disputedOdd (Ref.Refund Ref.delay) (outputs refundOdd)
  unchallengedVerdict = fixture 14 openOdd (Ref.Resolve True) (outputs trueOdd)
  changedClaim = Ref.Continue ((coinState disputedOdd) { Ref.assertion = wrongClaimIdentity })
  negatives =
    [ ("actual asserter bond underfunded by one satoshi", fundedOdd { edit = inputEdit 1 (spentValue (oddAmount - 1)) })
    , ("actual asserter funding script differs", fundedOdd { edit = inputEdit 1 (spentScript (keyScript feeSecret)) })
    , ("bond is present but independent fee input is missing", fundedOdd { edit = \tx -> tx { D.sigTxIn = V.take 2 (D.sigTxIn tx) } })
    , ("actual independent fee amount differs", fundedOdd { edit = inputEdit 2 (spentValue (Ref.fee + 1)) })
    , ("assertion authorized by the wrong role", fundedOdd { signingKey = secret Ref.Challenger })
    , ("bond below minimum", invalidBond 15 (Ref.minimumBond - 1))
    , ("bond above maximum", invalidBond 16 (Ref.maximumBond + 1))
    , ("actual challenge counterbond underfunded", challengedOdd { edit = inputEdit 1 (spentValue (oddAmount - 1)) })
    , ("actual challenge funding script differs", challengedOdd { edit = inputEdit 1 (spentScript (keyScript feeSecret)) })
    , ("challenge signed by the asserter instead of challenger", challengedOdd { signingKey = secret Ref.Asserter })
    , ("repeat challenge from an authentic disputed state", repeatChallenge)
    , ("challenge continuation replaces the committed assertion identity", challengedOdd { outputs = [changedClaim] })
    , ("state input moved to index 1", challengedOdd { currentIndex = 1,
        edit = \tx -> let inputs = D.sigTxIn tx in tx { D.sigTxIn = V.fromList [inputs V.! 1, inputs V.! 0, inputs V.! 2] } })
    , ("undisputed refund before CSV10", refundOdd { edit = sequenceEdit 9 })
    , ("time-based relative lock cannot substitute for block CSV10", refundOdd { edit = sequenceEdit 0x0040000a })
    , ("version 1 disables relative lock semantics", refundOdd { edit = \tx -> tx { D.sigTxVersion = 1 } })
    , ("sequence disable flag defeats the refund lock", refundOdd { edit = sequenceEdit 0x8000000a })
    , ("disputed state cannot take the undisputed refund", disputedRefund)
    , ("redirect the exact undisputed bond refund", refundOdd { edit = redirect 0 })
    , ("verdict cannot resolve an unchallenged state", unchallengedVerdict)
    , ("verdict authorized by the wrong key", trueOdd { signingKey = secret Ref.Store })
    , ("signature on an unrelated assertion and the same transaction", trueOdd
        { verdictOverride = Just (signVerdict arbitratorSecret wrongClaimIdentity True trueOdd) })
    , ("valid verdict replayed onto a different actual state outpoint", trueOdd
        { edit = inputEdit 0 (\input -> input { D.sigTxiPreviousOutpoint = dummyOutpoint 999 })
        , verdictOverride = Just (signVerdict arbitratorSecret correctIdentity True trueOdd) })
    , ("signature commits the opposite verdict on the same transaction", trueOdd
        { verdictOverride = Just (signVerdict arbitratorSecret correctIdentity False trueOdd) })
    , ("redirect the winner despite a fresh valid verdict", trueOdd { edit = redirect 0 })
    , ("redirect the Store fee despite a fresh valid verdict", trueOdd { edit = redirect 1 })
    , ("round the odd Store fee up and reduce the winner by one satoshi", trueOdd { edit = reviseAmount 0 (-1) . reviseAmount 1 1 })
    , ("redirect the setup carrier despite a fresh valid verdict", trueOdd { edit = redirect 2 })
    , ("actual state UTXO script differs from the authenticated Taproot view", trueOdd
        { edit = inputEdit 0 (spentScript (keyScript feeSecret)) })
    , ("actual disputed state value is short", trueOdd { edit = inputEdit 0 (spentValue (2 * oddAmount + Ref.carrier - 1)) })
    , ("open a forged assertion identity with a matching fresh verdict", trueOdd
        { opening = (coinState disputedOdd) { Ref.assertion = wrongClaimIdentity } })
    ]
