{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | Fully funded partial liquidation under a bounded Clipper price curve.
module JetDiscovery.Corpus.Clipper (entry, clipperKernel, price, takeFill) where

import Prelude hiding (and, not, or)
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
import Simplicity.Programs.Sha256.Lib
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Bitcoin.Term (Simplicity, Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Corpus.Baseline (signMsg)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import qualified JetDiscovery.Lib.TaprootTx1 as T
import qualified JetDiscovery.Ref.Bip340 as R
import qualified JetDiscovery.Ref.Clipper as Ref
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

type StateW = (Vector8 Word32, Word256)
type Args = ((Word8, Word8), ((Word32, Word32), (Word32, Word32)))
type Proof = (StateW, (Args, (G.SigW, G.SigW)))
type Transition = (StateW, Args)
type FillInput = (Word32, (Word32, (Word32, Word32)))
type Fill = (Word32, Word32)
type Purchase = (Word8, Fill)
type Plan = Either (StateW, Either () Purchase) (Either Word32 (Purchase, Word32))

secret :: Ref.Payee -> Integer
secret (Ref.Bidder who) = [8101,8202] H.!! who
secret Ref.DebtSink = 8303
secret Ref.Urn = 8404
secret Ref.Ward = 8505
secret Ref.SetupSponsor = 8606

oracleKey, feeKey :: Integer
oracleKey = 8707
feeKey = 8808

keyScript :: Integer -> BS.ByteString
keyScript key = unhex "5120" <> R.bytesFromInt (R.pubkeyOf key)

payeeScript :: Ref.Payee -> BS.ByteString
payeeScript = keyScript . secret

stateW :: Ref.State -> StateW
stateW state = case map w32 (Ref.fields state) of
  [a,b,c,d,e,f,g,h] -> ((((a,b),(c,d)),((e,f),(g,h))), w256FromBytes (Ref.identity state))
  _ -> error "clipper state arity"

field :: Core t => Int -> t StateW Word32
field i = oh >>> G.pick (testBit i 2) (G.pick (testBit i 1) (G.pick (testBit i 0) iden))

old :: Core t => Int -> t Transition Word32
old index = oh >>> field index

mode, bidder :: Core t => t Args Word8
mode = ooh
bidder = oih

eventClock, eventPrice, requested, limit :: Core t => t Args Word32
eventClock = ioh >>> oh
eventPrice = ioh >>> ih
requested = iih >>> oh
limit = iih >>> ih

k32 :: (Core t, TyC a) => Integer -> t a Word32
k32 = konst . w32

add32, subtract32, product32 :: (Assert t, TyC a) => t a Word32 -> t a Word32 -> t a Word32
add32 a b = (a &&& b) >>> A.add word32 >>> ((oh >>> not iden >>> verify) &&& ih) >>> ih
subtract32 a b = (a &&& b) >>> A.subtract word32 >>> ((oh >>> not iden >>> verify) &&& ih) >>> ih
product32 a b = ((a &&& b) >>> A.multiply word32) >>> (G.same oh (k32 0) &&& ih) >>> ih

less, atMost :: (Assert t, TyC a) => t a Word32 -> t a Word32 -> t a Bit
less a b = (a &&& b) >>> A.lt word32
atMost a b = (a &&& b) >>> A.le word32

positive :: (Assert t, TyC a) => t a Word32 -> t a ()
positive amount = less (k32 0) amount >>> verify

ledger :: (Core t, TyC a) => [t a Word32] -> t a (Vector8 Word32)
ledger [a,b,c,d,e,f,g,h] = (((a &&& b) &&& (c &&& d)) &&& ((e &&& f) &&& (g &&& h)))
ledger _ = error "clipper ledger arity"

stateHash :: Assert t => t StateW Word256
stateHash = (iden &&& (unit >>> ctx8InitTag Ref.stateTag))
  >>> L.foldl' (>>>) iden [T.append (field index) ctx8Add4 | index <- [0..7]]
  >>> T.append ih ctx8Add32 >>> ih >>> ctx8Finalize

live :: Assert t => t StateW Bit
live = G.is (field 0) (k32 1)

validState :: Assert t => t StateW ()
validState = G.select live (G.allChecks
  [ positive (field 1), atMost (field 1) (field 7) >>> verify, atMost (field 7) (k32 Ref.lotLimit) >>> verify
  , positive (field 2), G.same (add32 (field 2) (field 3)) (field 4), atMost (field 4) (k32 Ref.debtLimit) >>> verify
  , atMost (field 5) (field 6) >>> verify, atMost (field 6) (k32 Ref.eventLimit) >>> verify
  ]) (G.same iden (konst (stateW Ref.setup)))

-- RAY is divisible by 100. At top=100*RAY and tau=100, the
-- full source calculation is exactly (100-elapsed)*RAY in range.
price :: Assert t => t Word32 Word32
price = G.select (less iden (k32 Ref.tau)) (subtract32 (k32 Ref.top) iden) (k32 0)

at :: (Assert t, Primitive t, TyC a, TyC b) => Integer -> P.Prim Word32 (Either () b) -> t a b
at index primitiveType = konst (w32 index) >>> primitive primitiveType >>> verify

distinct :: (Assert t, Primitive t, TyC a) => Integer -> Integer -> t a ()
distinct first second = (at first P.InputPrevOutpoint &&& at second P.InputPrevOutpoint) >>> eq >>> not iden >>> verify

quoteSats :: Core t => t Word32 Word64
quoteSats = konst (w32 0) &&& iden

collateralSats :: Core t => t Word32 Word64
collateralSats = (iden &&& konst (w32 Ref.collateralUnit)) >>> A.multiply word32

stateValue :: Assert t => t StateW Word64
stateValue = G.add (G.k Ref.carrier) (field 1 >>> collateralSats)

fundingChecks :: (Simplicity t, Primitive t) => t StateW Word256 -> t StateW ()
fundingChecks scriptFor = G.allChecks
  [ validState, G.same (unit >>> primitive P.CurrentIndex) (konst (w32 0)), distinct 0 1
  , loadState stateHash, G.same (at 0 P.InputScriptHash) scriptFor, G.same (at 0 P.InputValue) stateValue
  ]

inputCount :: (Simplicity t, Primitive t, TyC a) => Integer -> t a ()
inputCount n = G.same (unit >>> Tx.numInputs) (konst (w32 n))

threeInputs :: (Simplicity t, Primitive t, TyC a) => t a Word256 -> t a Word64 -> t a ()
threeInputs script amount = G.allChecks [inputCount 3, distinct 0 2, distinct 1 2,
  G.same (at 1 P.InputScriptHash) script, G.same (at 1 P.InputValue) amount, G.same (at 2 P.InputValue) (G.k Ref.fee)]

twoInputs :: (Simplicity t, Primitive t, TyC a) => t a ()
twoInputs = G.allChecks [inputCount 2, G.same (at 1 P.InputValue) (G.k Ref.fee)]

destination :: (Core t, TyC a) => Ref.Payee -> t a Word256
destination = konst . G.scriptHash . payeeScript

bidderScript :: Assert t => t Word8 Word256
bidderScript = G.select (G.is iden (konst (w8 0))) (destination (Ref.Bidder 0)) (destination (Ref.Bidder 1))

publicKey :: (Core t, TyC a) => Integer -> t a Word256
publicKey = konst . w256 . R.pubkeyOf

identityHash :: (Assert t, Primitive t) => t (Word32, Word32) Word256
identityHash = (iden &&& (unit >>> ctx8InitTag Ref.identityTag))
  >>> T.append (at 0 P.InputPrevOutpoint >>> oh) ctx8Add32 >>> T.append (at 0 P.InputPrevOutpoint >>> ih) ctx8Add4
  >>> T.append oh ctx8Add4 >>> T.append ih ctx8Add4 >>> ih >>> ctx8Finalize

actionMessage :: (Simplicity t, Primitive t) => t Args Word256
actionMessage = (iden &&& (unit >>> ctx8InitTag Ref.actionTag)) >>> T.append (unit >>> sigMsg) ctx8Add32
  >>> T.append mode ctx8Add1 >>> T.append bidder ctx8Add1 >>> T.append eventClock ctx8Add4
  >>> T.append eventPrice ctx8Add4 >>> T.append requested ctx8Add4 >>> T.append limit ctx8Add4 >>> ih >>> ctx8Finalize

eventMessage :: (Simplicity t, Primitive t) => t (Word256, Args) Word256
eventMessage = (iden &&& (unit >>> ctx8InitTag Ref.eventTag)) >>> T.append (unit >>> sigMsg) ctx8Add32
  >>> T.append oh ctx8Add32 >>> T.append (ih >>> mode) ctx8Add1
  >>> T.append (ih >>> eventClock) ctx8Add4 >>> T.append (ih >>> eventPrice) ctx8Add4 >>> ih >>> ctx8Finalize

authenticate :: (Simplicity t, Primitive t) => t Proof ()
authenticate = G.allChecks
  [ G.select taking (((ioh >>> bidder) &&& konst (w8 2)) >>> A.lt word8 >>> verify) unit
  , ((signer &&& (ioh >>> actionMessage)) &&& iioh) >>> Secp.bip_0340_verify
  , G.select (or taking restarting) oracle unit
  ]
 where
  taking = G.is (ioh >>> mode) (konst (w8 1))
  restarting = G.is (ioh >>> mode) (konst (w8 2))
  bidderKey = G.select (G.is (ioh >>> bidder) (konst (w8 0)))
    (publicKey (secret (Ref.Bidder 0))) (publicKey (secret (Ref.Bidder 1)))
  signer = G.select taking bidderKey (publicKey (secret Ref.Ward))
  oracle = ((publicKey oracleKey &&& (((oh >>> ih) &&& ioh) >>> eventMessage)) &&& (iih >>> ih)) >>> Secp.bip_0340_verify

kick :: (Simplicity t, Primitive t) => t Transition Plan
kick = (checks &&& injl (next &&& injl unit)) >>> ih
 where
  amount = ih >>> requested
  debt = ih >>> limit
  checks = G.allChecks [oh >>> live >>> not iden >>> verify, positive amount, positive debt,
    atMost amount (k32 Ref.lotLimit) >>> verify, atMost debt (k32 Ref.debtLimit) >>> verify,
    threeInputs (destination Ref.Urn) (amount >>> collateralSats)]
  next = ledger [k32 1, amount, debt, k32 0, debt, k32 0, k32 0, amount]
    &&& ((amount &&& debt) >>> identityHash)

elapsed :: Assert t => t Transition Word32
elapsed = subtract32 (ih >>> eventClock) (old 5)

done :: Assert t => t Transition Bit
done = or (less (k32 Ref.tailLimit) elapsed) (less (elapsed >>> price) (k32 Ref.cusp))

eventChecks :: Assert t => t Transition ()
eventChecks = G.allChecks [oh >>> live >>> verify, atMost (old 6) (ih >>> eventClock) >>> verify,
  atMost (ih >>> eventClock) (k32 Ref.eventLimit) >>> verify, G.same (elapsed >>> price) (ih >>> eventPrice)]

redo :: (Simplicity t, Primitive t) => t Transition Plan
redo = (G.allChecks [eventChecks, done >>> verify, twoInputs] &&& injl (next &&& injl unit)) >>> ih
 where
  next = ledger [if index == 5 || index == 6 then ih >>> eventClock else old index | index <- [0..7]] &&& (oh >>> ih)

yank :: (Simplicity t, Primitive t) => t Transition Plan
yank = (G.allChecks [oh >>> live >>> verify, twoInputs] &&& injr (injl (old 1))) >>> ih

-- Input (lot,(tab,(request,price))) and result (slice,owe), all in the
-- normalized units. Crop owe first, and floor slice without repricing owe.
takeFill :: forall t. Assert t => t FillInput Fill
takeFill = (G.allChecks [positive request, positive unitPrice] &&& (iden &&& (slice &&& preliminary))) >>> ih
  >>> adjust >>> ((G.allChecks [positive oh, positive ih] &&& iden) >>> ih)
 where
  request :: t FillInput Word32
  request = iioh
  unitPrice :: t FillInput Word32
  unitPrice = iih >>> ih
  slice :: t FillInput Word32
  slice = G.select (less oh request) oh request
  preliminary :: t FillInput Word32
  preliminary = product32 slice unitPrice
  adjust :: t (FillInput, Fill) Fill
  adjust = G.select (less debt iih) (crop debt)
    (G.select (and (less iih debt) (less ioh (oh >>> oh))) dustCase ih)
  debt = oh >>> ioh
  crop owe = (((owe &&& (oh >>> unitPrice)) >>> A.divide word32) &&& owe)
  dustCase = G.select (less (subtract32 debt iih) (k32 Ref.chost))
    ((less (k32 Ref.chost) debt >>> verify) &&& crop (subtract32 debt (k32 Ref.chost)) >>> ih) ih

takeAction :: forall t. (Simplicity t, Primitive t) => t Transition Plan
takeAction = (checks &&& (iden &&& fill)) >>> ih >>> settle
 where
  checks = G.allChecks [eventChecks, done >>> not iden >>> verify, atMost (ih >>> eventPrice) (ih >>> limit) >>> verify]
  fill = (old 1 &&& (old 2 &&& ((ih >>> requested) &&& (ih >>> eventPrice)))) >>> takeFill
  settle :: t (Transition, Fill) Plan
  settle = (threeInputs (buyer >>> bidderScript) (iih >>> quoteSats) &&&
    G.select terminal (injr (injr (purchase &&& nextLot))) (injl (next &&& injr purchase))) >>> ih
   where
    buyer = oh >>> ih >>> bidder
    purchase = buyer &&& ih
    nextLot = subtract32 (oh >>> old 1) ioh
    nextDebt = subtract32 (oh >>> old 2) iih
    terminal = or (G.is nextLot (k32 0)) (G.is nextDebt (k32 0))
    next = ledger [k32 1, nextLot, nextDebt, add32 (oh >>> old 3) iih, oh >>> old 4,
      oh >>> old 5, oh >>> ih >>> eventClock, oh >>> old 7] &&& (oh >>> oh >>> ih)

applyPlan :: forall t. (Simplicity t, Primitive t) => t StateW Word256 -> t Plan ()
applyPlan scriptFor = copair continuation (copair canceled finished)
 where
  count :: TyC a => Integer -> t a ()
  count n = G.same (unit >>> Tx.numOutputs) (konst (w32 n))
  pay :: TyC a => Integer -> t a Word256 -> t a Word64 -> t a ()
  pay index script amount = G.allChecks [G.same (G.outScript index) script, G.same (G.outVal index) amount]
  purchase :: Integer -> Integer -> t Purchase ()
  purchase toBuyer toSink = G.allChecks [pay toBuyer (oh >>> bidderScript) (ioh >>> collateralSats),
    pay toSink (destination Ref.DebtSink) (iih >>> quoteSats)]
  carrier :: TyC a => Integer -> t a ()
  carrier index = pay index (destination Ref.SetupSponsor) (G.k Ref.carrier)
  continuation = G.allChecks [oh >>> pay 0 scriptFor stateValue,
    ih >>> copair (count 1) (G.allChecks [count 3, purchase 1 2])]
  canceled = G.allChecks [count 2, pay 0 (destination Ref.Ward) collateralSats, carrier 1]
  finished = G.allChecks [oh >>> purchase 0 1,
    G.select (G.is ih (k32 0)) (G.allChecks [count 3, carrier 2])
      (G.allChecks [count 4, pay 2 (destination Ref.Urn) (ih >>> collateralSats), carrier 3])]

clipperKernel :: forall t. (Simplicity t, Primitive t) => t Proof ()
clipperKernel = (G.allChecks [oh >>> fundingChecks scriptFor, authenticate] &&& (oh &&& ioh))
  >>> ih >>> actions >>> applyPlan scriptFor
 where
  scriptFor :: t StateW Word256
  scriptFor = stateScriptHash stateHash
  actions :: t Transition Plan
  actions = L.foldr choose failure (zip [0..] [kick,takeAction,redo,yank])
  choose (action, branch) rest = G.select (G.is (ih >>> mode) (konst (w8 action))) branch rest

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
  , signer :: Integer
  , oracleOverride :: Maybe (Hash256 -> G.SigW)
  }

origin :: D.Outpoint
origin = dummyOutpoint 555

originFields :: (BS.ByteString, Integer)
originFields = (hashToBytes (D.opHash origin), toInteger (D.opIndex origin))

fixture :: DW.Word32 -> Coin -> Ref.Action -> [Ref.Output] -> Fixture
fixture index old requestedAction destinations = Fixture old requestedAction destinations index id 0 key Nothing
 where
  key = case requestedAction of
    Ref.Take who _ _ _ _ -> secret (Ref.Bidder who)
    _ -> secret Ref.Ward

honest :: DW.Word32 -> Coin -> Ref.Action -> Fixture
honest index old requestedAction = case Ref.step originFields (coinState old) requestedAction of
  Just destinations -> fixture index old requestedAction destinations
  Nothing -> error ("invalid Clipper fixture " ++ show requestedAction)

fixtureTx :: Fixture -> Hash256 -> D.SigTx
fixtureTx f cmr = edit f (mkTx 2 (stateInput : funded ++ [feeInput]) (map output (outputs f)) 0)
 where
  Coin state previous = coin f
  stateInput = mkInput (previous cmr) (fromInteger (Ref.stateValue state))
    (BL.fromStrict (stateScript cmr (Ref.stateDigest state))) 0xfffffffe
  funding role amount = mkInput (dummyOutpoint (2 * serial f + 600)) (fromInteger amount)
    (BL.fromStrict (payeeScript role)) 0xfffffffe
  funded = case action f of
    Ref.Kick amount _ -> [funding Ref.Urn (amount * Ref.collateralUnit)]
    Ref.Take who _ _ _ _ -> case [owe | Ref.Pay Ref.DebtSink owe <- outputs f] of
      [owe] -> [funding (Ref.Bidder who) owe]
      _ -> error "one exact Clipper quote payment"
    _ -> []
  feeInput = mkInput (dummyOutpoint (2 * serial f + 601)) (fromInteger Ref.fee)
    (BL.fromStrict (keyScript feeKey)) 0xfffffffe
  output (Ref.Continue next) = mkOutput (fromInteger (Ref.stateValue next)) (stateScript cmr (Ref.stateDigest next))
  output (Ref.Pay who amount) = mkOutput (fromInteger amount) (payeeScript who)

fixtureEnv f cmr = mkEnv (fixtureTx f cmr) (currentIndex f)
  (\_ -> stateTap cmr (Ref.stateDigest (coinState (coin f)))) cmr

successor :: Fixture -> Coin
successor f = case outputs f of
  Ref.Continue next : _ -> Coin next (\cmr -> D.Outpoint (D.txid (fixtureTx f cmr)) 0)
  _ -> error "terminal Clipper fixture has no successor"

txMessage :: Fixture -> Hash256 -> BS.ByteString
txMessage f cmr = case fixtureEnv f cmr >>= (\env -> J.fastEval sigMsg env ()) of
  Just message -> w256ToBytes message
  Nothing -> error "Clipper fixture signature message"

eventSignature :: Integer -> BS.ByteString -> Fixture -> Hash256 -> G.SigW
eventSignature key auction f cmr = G.sigW (signMsg key (Ref.eventDigest (txMessage f cmr) auction (action f)))

argsW :: Ref.Action -> Args
argsW action' = ((w8 op,w8 who),((w32 now,w32 quote),(w32 amount,w32 cap)))
 where (op,who,now,quote,amount,cap) = Ref.actionFields action'

fixtureProof :: Fixture -> Hash256 -> Proof
fixtureProof f cmr = (stateW state, (argsW (action f), (actorSignature, priceSignature)))
 where
  state = coinState (coin f)
  actorSignature = G.sigW (signMsg (signer f) (Ref.actionDigest (txMessage f cmr) (action f)))
  priceSignature = case action f of
    Ref.Take _ _ _ _ _ -> signedEvent
    Ref.Redo _ _ -> signedEvent
    _ -> G.zeroSig
  signedEvent = maybe (eventSignature oracleKey (Ref.identity state) f cmr) ($ cmr) (oracleOverride f)

inputEdit :: Int -> (D.SigTxInput -> D.SigTxInput) -> D.SigTx -> D.SigTx
inputEdit index modify tx = tx { D.sigTxIn = V.imap (\i input -> if i == index then modify input else input) (D.sigTxIn tx) }

outputEdit :: Int -> (D.TxOutput -> D.TxOutput) -> D.SigTx -> D.SigTx
outputEdit index modify tx = tx { D.sigTxOut = V.imap (\i output -> if i == index then modify output else output) (D.sigTxOut tx) }

spentValue :: Integer -> D.SigTxInput -> D.SigTxInput
spentValue amount input = input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoValue = fromInteger amount } }

spentScript :: BS.ByteString -> D.SigTxInput -> D.SigTxInput
spentScript script input = input { D.sigTxiTxo = (D.sigTxiTxo input) { D.txoScript = BL.fromStrict script } }

entry :: Entry
entry = Entry "app-maker-clipper-partial-liquidation"
  "Maker Clipper partial liquidation with funded BTC payment and surplus return"
  "Sky DSS clip.sol and abaci.sol at fa4f6630afb0624d04a003e920b0d71a00331d98"
  BitcoinApp
  (Derived "Full source-scale Integer reference, actual native funding and linked payment transactions, and same-CMR debt cap, dust, time, authority and payout vectors")
  [ "One native initialized auction. Kick consumes exact urn collateral, one collateral unit is 100 sats, and each quote unit is one actual bidder sat"
  , "The chosen exact normalized RAY profile is top 100, tau 100, tail 80, cusp 40 percent and chost 1000. Accepted fills have positive slice and owe"
  , "A fixed authority signs monotone logical event time, auction identity, price and actual sig_all_hash. The program checks the exact curve quote and reset status, and the event is the bounded valuation clock"
  , "Take preserves adjusted owe after the collateral slice floors. Actual bidder funds pay the fixed debt sink, actual collateral pays the bidder, and partial continuations account for lot, remaining target and collected proceeds"
  , "Debt cleared returns remaining collateral to the original urn. Lot exhaustion closes the sale. Redo requires the ward and a valid event, and yank pays the remaining lot to the ward. All terminal paths return the separate carrier"
  , "The actual current input 0 script and value, exact funding scripts, distinct inputs, independent 1000-sat fee, and exact output scripts, values and count are checked. The native profile uses no external debt credit or callback"
  ] make vectors
 where
  make = boundProgram clipperKernel
  cmr = progCmr (make (stateW Ref.setup, (argsW Ref.Yank, (G.zeroSig,G.zeroSig))))
  vectors = [Vector name (fixtureEnv f) (fixtureProof f cmr) expected | (name, f, expected) <- cases]

cases :: [(String, Fixture, Expect)]
cases = [(name, f, Accept) | (name, f) <- positives] ++ [(name, f, Reject) | (name, f) <- negatives]
 where
  initial = Coin Ref.setup (const origin)
  start = honest 1 initial (Ref.Kick 120 8301)
  opened = successor start
  ordinary = honest 2 opened (Ref.Take 0 30 90 10 90)
  afterOrdinary = successor ordinary
  dust = honest 3 afterOrdinary (Ref.Take 1 60 80 20 80)
  afterDust = successor dust
  capped = honest 4 afterDust (Ref.Take 0 20 75 25 75)
  atCusp = honest 5 afterOrdinary (Ref.Take 0 10 40 60 40)
  reset = honest 6 (successor atCusp) (Ref.Redo 61 39)
  restarted = successor reset
  afterReset = honest 7 restarted (Ref.Take 1 10 100 62 99)
  remove = honest 8 (successor afterReset) Ref.Yank
  shortLot = honest 9 initial (Ref.Kick 10 3000)
  exhaust = honest 10 (successor shortLot) (Ref.Take 0 20 100 0 100)
  smallTab = honest 11 initial (Ref.Kick 10 1000)
  wholeLot = honest 12 (successor smallTab) (Ref.Take 1 10 80 20 80)
  exactDebt = honest 13 initial (Ref.Kick 30 1600)
  exactClear = honest 14 (successor exactDebt) (Ref.Take 0 20 80 20 80)
  afterZeroPrice = honest 15 afterOrdinary (Ref.Redo 110 0)
  tinyTab = honest 16 initial (Ref.Kick 10 50)
  positives =
    [ ("authorized kick receives actual urn collateral and independent fee", start)
    , ("first partial purchase debits the actual 2700-sat bidder input", ordinary)
    , ("dust adjustment keeps owe 4601 after flooring slice to 57", dust)
    , ("debt cap keeps owe 1000 after flooring slice to 13 and returns surplus", capped)
    , ("exact cusp equality still permits a take", atCusp)
    , ("ward restarts after crossing below cusp with an authenticated event", reset)
    , ("take after restart measures elapsed time from the new epoch", afterReset)
    , ("authorized yank pays the ward the actual remaining lot", remove)
    , ("alternative lot funded with a higher debt target", shortLot)
    , ("last lot closes with residual uncollected debt", exhaust)
    , ("alternative debt target exactly at chost", smallTab)
    , ("full lot sale bypasses the dust restriction", wholeLot)
    , ("alternative assertion with exact debt-equality boundary", exactDebt)
    , ("preliminary owe equal to debt clears it and returns surplus", exactClear)
    , ("zero curve price after tail can restart the live auction", afterZeroPrice)
    , ("positive debt target below one unit price is funded", tinyTab)
    ]
  forgedPartial index old requestedAction who now slice owe = fixture index old requestedAction
    [Ref.Continue state { Ref.lot = Ref.lot state - slice, Ref.tab = Ref.tab state - owe
      , Ref.collected = Ref.collected state + owe, Ref.lastEvent = now },
     Ref.Pay (Ref.Bidder who) (slice * Ref.collateralUnit), Ref.Pay Ref.DebtSink owe]
   where state = coinState old
  forgedRedo index old now quote = let state = coinState old in fixture index old (Ref.Redo now quote)
    [Ref.Continue state { Ref.epoch = now, Ref.lastEvent = now }]
  unknownAuction = Ref.identity (coinState (successor shortLot))
  correctAuction = Ref.identity (coinState afterOrdinary)
  changeAmount index amount = outputEdit index (\output -> output { D.txoValue = fromInteger amount })
  redirect index = outputEdit index (\output -> output { D.txoScript = BL.fromStrict (keyScript feeKey) })
  badReset = reset { outputs = case outputs reset of
    [Ref.Continue next] -> [Ref.Continue next { Ref.tab = Ref.tab next + 1, Ref.initialTab = Ref.initialTab next + 1 }]
    _ -> error "expected reset continuation" }
  terminalReplay = remove
    { coin = Coin (coinState (coin remove)) (\cmr -> D.Outpoint (D.txid (fixtureTx capped cmr)) 3)
    , serial = 26
    , edit = inputEdit 0 (spentValue Ref.carrier . spentScript (payeeScript Ref.SetupSponsor))
    }
  negatives =
    [ ("kick collateral input is one satoshi short", start { edit = inputEdit 1 (spentValue 11999) })
    , ("kick collateral input belongs to a different script", start { edit = inputEdit 1 (spentScript (keyScript feeKey)) })
    , ("kick signed by an unauthorized role", start { signer = feeKey })
    , ("second kick tries to overwrite the active sale", start { coin = opened })
    , ("kick tries to create a zero debt target", start { action = Ref.Kick 120 0 })
    , ("bidder actual payment input is one satoshi short", ordinary { edit = inputEdit 1 (spentValue 2699) })
    , ("bidder funding input script differs from authorized bidder", ordinary { edit = inputEdit 1 (spentScript (payeeScript (Ref.Bidder 1))) })
    , ("bidder payment cannot replace the independent fee input", ordinary { edit = \tx -> tx { D.sigTxIn = V.take 2 (D.sigTxIn tx) } })
    , ("take signed by a different bidder", ordinary { signer = secret (Ref.Bidder 1) })
    , ("maximum bidder price below the exact curve quote", atCusp { action = Ref.Take 0 10 39 60 40 })
    , ("signed quote disagrees with the exact normalized curve", forgedPartial 17 afterOrdinary (Ref.Take 0 10 100 60 41) 0 60 10 410)
    , ("authenticated event clock decreases", forgedPartial 18 afterOrdinary (Ref.Take 0 10 100 9 91) 0 9 10 910)
    , ("valuation signed by an unauthorized oracle", atCusp { oracleOverride = Just (eventSignature feeKey correctAuction atCusp) })
    , ("oracle signature binds a different auction identity", atCusp { oracleOverride = Just (eventSignature oracleKey unknownAuction atCusp) })
    , ("oracle event replayed onto a different actual state outpoint", atCusp
        { edit = inputEdit 0 (\input -> input { D.sigTxiPreviousOutpoint = dummyOutpoint 999 })
        , oracleOverride = Just (eventSignature oracleKey correctAuction atCusp) })
    , ("take below cusp requires a restart", forgedPartial 19 afterOrdinary (Ref.Take 0 10 100 61 39) 0 61 10 390)
    , ("redo at exact cusp equality is premature", forgedRedo 20 (successor atCusp) 60 40)
    , ("valid event does not authorize a different restart signer", reset { signer = feeKey })
    , ("restart tries to change debt instead of just its epoch", badReset)
    , ("post-reset quote incorrectly uses the original epoch", forgedPartial 21 restarted (Ref.Take 1 10 100 62 38) 1 62 10 380)
    , ("at chost a dust-creating partial take is unavailable", forgedPartial 22 afterDust (Ref.Take 0 1 75 25 75) 0 25 1 75)
    , ("debt cap with a zero rounded slice is outside the positive-fill profile", fixture 23 (successor tinyTab)
        (Ref.Take 0 5 100 0 100) [Ref.Pay (Ref.Bidder 0) 0, Ref.Pay Ref.DebtSink 50, Ref.Pay Ref.Urn 1000, Ref.Pay Ref.SetupSponsor Ref.carrier])
    , ("dust payment cannot be recomputed as rounded slice times price", forgedPartial 24 afterOrdinary (Ref.Take 1 60 80 20 80) 1 20 57 4560)
    , ("capped payment cannot be recomputed as rounded slice times price", capped
        { edit = inputEdit 1 (spentValue 975) . changeAmount 1 975 })
    , ("redirect actual bidder collateral despite valid signed inputs", capped { edit = redirect 0 })
    , ("redirect actual quote to a different debt sink", capped { edit = redirect 1 })
    , ("redirect actual debt-cleared surplus from the urn", capped { edit = redirect 2 })
    , ("redirect actual setup carrier at terminal take", capped { edit = redirect 3 })
    , ("actual old UTXO script differs from Taproot opening", ordinary { edit = inputEdit 0 (spentScript (keyScript feeKey)) })
    , ("actual old UTXO cannot underfund remaining collateral", ordinary { edit = inputEdit 0 (spentValue 21999) })
    , ("state input moved to index 1", ordinary { currentIndex = 1,
        edit = \tx -> let inputs = D.sigTxIn tx in tx { D.sigTxIn = V.fromList [inputs V.! 1, inputs V.! 0, inputs V.! 2] } })
    , ("yank signed by a non-ward key", remove { signer = feeKey })
    , ("terminal carrier output cannot replay a live auction", terminalReplay)
    , ("partial purchase continuation inflates physical collateral by one satoshi", ordinary { edit = changeAmount 0 19001 })
    , ("terminal take adds an unauthorized output", capped { edit = \tx -> tx { D.sigTxOut = V.snoc (D.sigTxOut tx) (mkOutput 0 (unhex "6a")) } })
    ]
