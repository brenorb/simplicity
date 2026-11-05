{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | A fully funded Bitcoin mutual with two transferable cover policies.
module JetDiscovery.Corpus.NexusMutual
  ( entry, mutualCmr, referenceAudit ) where

import Prelude hiding (and,drop,not,or,take)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Vector as V
import qualified Data.Word as DW
import Data.Serialize (runPutLazy)
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import Simplicity.Digest (Hash256)
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (Bit,cond,false,not,or,verify)
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Term.Core
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Lib.Bytes (failure,konst,w8,w16,w32,w64,w256,w256FromBytes,w256ToBytes)
import JetDiscovery.Lib.State (loadState,stateScript,stateScriptHash,stateTap)
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Bip
import qualified JetDiscovery.Ref.NexusMutual as Ref

type PolicyW = (Word32,(Word32,Word32))
type Ledger = (Word32,(PolicyW,PolicyW))
type Request = (Word8,(Word8,(Word8,Word32)))
type Signature = (Word256,Word256)
type Proof = (Ledger,(Request,Either () Signature))
type Payment = (Word8,Word32)
type Effects = (Word8,(Payment,Payment))
type Plan = (Effects,Either () Ledger)
type Work = (Request,Ledger)
type PolicyWork = (Request,(Word32,PolicyW))
type PolicyPlan = (Effects,(Word32,PolicyW))

key :: Ref.Role -> Integer
key Ref.CapitalProvider = 5501
key Ref.Assessor = 5502
key (Ref.PolicyOwner Ref.Alice) = 5503
key (Ref.PolicyOwner Ref.Bob) = 5504

p2tr :: Integer -> BS.ByteString
p2tr secret = unhex "5120" <> Bip.bytesFromInt (Bip.pubkeyOf secret)

scriptHash :: BS.ByteString -> Word256
scriptHash = w256FromBytes . hashToBytes . sha256

c8 :: (Core t,TyC a) => Integer -> t a Word8
c8 = konst . w8
c16 :: (Core t,TyC a) => Integer -> t a Word16
c16 = konst . w16
c32 :: (Core t,TyC a) => Integer -> t a Word32
c32 = konst . w32
c64 :: (Core t,TyC a) => Integer -> t a Word64
c64 = konst . w64

is :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a Bit
is a b = (a&&&b)>>>eq

same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b = is a b>>>verify

checks :: (Core t,TyC a) => [t a ()] -> t a ()
checks = L.foldl' (\a b -> (a&&&b)>>>unit) unit

checked :: (Core t,TyC a,TyC b) => t a () -> t a b -> t a b
checked assertion result = (assertion&&&result)>>>ih

select :: (Core t,TyC a,TyC b) => t a Bit -> t a b -> t a b -> t a b
select predicate thn els = (predicate&&&iden)>>>cond thn els

byByte :: (Assert t,TyC a,TyC b) => t a Word8 -> [(Integer,t a b)] -> t a b
byByte label = L.foldr (\(code,branch) rest -> select (is label (c8 code)) branch rest) failure

add, subtract32 :: (Assert t,TyC a) => t a Word32 -> t a Word32 -> t a Word32
add a b = (a&&&b)>>>A.add word32>>>checked (not oh>>>verify) ih
subtract32 a b = (a&&&b)>>>A.subtract word32>>>checked (not oh>>>verify) ih

le :: (Assert t,TyC a) => t a Word32 -> t a Word32 -> t a ()
le a b = (a&&&b)>>>A.le word32>>>verify

positiveAmount :: (Assert t,TyC a) => t a Word32 -> t a ()
positiveAmount a = (c32 0&&&a)>>>A.lt word32>>>verify

z32 :: Core t => t Word32 Word64
z32 = c32 0&&&iden

phase :: Core t => t PolicyW Word8
phase = oh>>>ooh
owner :: Core t => t PolicyW Word8
owner = oh>>>oih
claimId :: Core t => t PolicyW Word16
claimId = oh>>>ih

phaseCode :: Ref.Phase -> Integer
phaseCode = toInteger . fromEnum

phaseIs :: Assert t => Ref.Phase -> t PolicyW Bit
phaseIs p = is phase (c8 (phaseCode p))

phaseIn :: Assert t => [Ref.Phase] -> t PolicyW Bit
phaseIn = L.foldr (\p rest -> or (phaseIs p) rest) false

exposure :: Assert t => t Ledger Word32
exposure = add (ioh>>>ioh) (iih>>>ioh)

refundable :: Assert t => t Ledger Word32
refundable = add (ioh>>>depositFor) (iih>>>depositFor)
 where
  depositFor = select (phaseIn [Ref.Pending,Ref.Accepted,Ref.Draw]) (c32 Ref.deposit) (c32 0)

value :: Assert t => t Ledger Word32
value = add (c32 Ref.anchor) (add oh refundable)

policyFields :: (Core t,TyC a) => t a Word8 -> t a Word8 -> t a Word16
             -> t a Word32 -> t a Word32 -> t a PolicyW
policyFields st who ident cover pending = ((st&&&who)&&&ident)&&&(cover&&&pending)

validPolicy :: Assert t => t PolicyW ()
validPolicy = checks
  [ (owner&&&c8 1)>>>A.le word8>>>verify
  , le ioh (c32 Ref.maxCover)
  , byByte phase
      [ (phaseCode Ref.Unused, same iden (konst (packPolicy (fst (Ref.policies Ref.setup)))))
      , (phaseCode Ref.Available, checks [positiveAmount ioh,same claimId (c16 0),clear])
      , (phaseCode Ref.Pending, openClaim)
      , (phaseCode Ref.Accepted, openClaim)
      , (phaseCode Ref.Draw, openClaim)
      , (phaseCode Ref.Denied, checks [settled,positiveAmount ioh])
      , (phaseCode Ref.Paid, settled)
      , (phaseCode Ref.DepositReturned, checks [settled,positiveAmount ioh])
      , (phaseCode Ref.Surrendered, checks [same ioh (c32 0),clear])
      ]
  ]
 where
  clear = same iih (c32 0)
  newId = (c16 0&&&claimId)>>>A.lt word16>>>verify
  openClaim = checks [newId,positiveAmount iih,le iih ioh]
  settled = checks [newId,clear]

validLedger :: Assert t => t Ledger ()
validLedger = checks
  [ ioh>>>validPolicy, iih>>>validPolicy, le exposure oh
  , le (add oh refundable) (c32 Ref.maxCapital) ]

stateWord :: Core t => t Ledger Word256
stateWord = ((tag&&&oh)&&&((ioh>>>oh)&&&(ioh>>>ioh)))&&&
            (((ioh>>>iih)&&&(iih>>>oh))&&&((iih>>>ioh)&&&(iih>>>iih)))
 where tag = c32 (Bip.intFromBytes (C.pack "NMX1"))

{-# NOINLINE scriptWrapped #-}
scriptWrapped :: J.WrappedSimplicity Word256 Word256
scriptWrapped = J.jetSubst (stateScriptHash iden)

stateScriptT :: Simplicity t => t Ledger Word256
stateScriptT = stateWord>>>J.unwrap scriptWrapped

roleOfOwner :: (Assert t,TyC a) => t a Word8 -> t a Word8
roleOfOwner who = select (is who (c8 0)) (c8 3) (c8 4)

roles :: [(Integer,Ref.Role)]
roles = [(1,Ref.CapitalProvider),(2,Ref.Assessor),(3,Ref.PolicyOwner Ref.Alice),(4,Ref.PolicyOwner Ref.Bob)]

publicKey :: Assert t => t Word8 Word256
publicKey = byByte iden [(code,konst (w256 (Bip.pubkeyOf (key role)))) | (code,role)<-roles]

roleScript :: Assert t => t Word8 Word256
roleScript = byByte iden [(code,konst (scriptHash (p2tr (key role)))) | (code,role)<-roles]

noPayment :: (Core t,TyC a) => t a Payment
noPayment = c8 0&&&c32 0

effects :: (Core t,TyC a) => t a Word8 -> t a Payment -> t a Payment -> t a Effects
effects authorize fund pay = authorize&&&(fund&&&pay)

mode, slot, argument :: Core t => t Request Word8
mode = oh
slot = ioh
argument = iioh

amount :: Core t => t Request Word32
amount = iiih

zeroArg :: (Assert t,TyC a) => t a Request -> t a ()
zeroArg request = same (request>>>argument) (c8 0)

zeroAmount :: (Assert t,TyC a) => t a Request -> t a ()
zeroAmount request = same (request>>>amount) (c32 0)

capitalPlan :: Assert t => t Work Plan
capitalPlan = checked (checks [same (oh>>>slot) (c8 0),zeroArg oh])
  (byByte (oh>>>mode) [(0,fund),(1,withdraw),(2,closePool)])
 where
  reserve = ioh
  size = oh>>>amount
  continue change = injr (change&&&iih)
  fund = checked (positiveAmount size)
    (effects (c8 1) (c8 1&&&size) noPayment&&&continue (add reserve size))
  withdraw = checked (positiveAmount size)
    (effects (c8 1) noPayment (c8 1&&&size)&&&continue (subtract32 reserve size))
  closePool = checked (checks [zeroAmount oh,same (ih>>>exposure) (c32 0),same (ih>>>refundable) (c32 0)])
    (effects (c8 1) noPayment (c8 1&&&(ih>>>value))&&&injl unit)

policyActions :: forall t. Assert t => t PolicyWork PolicyPlan
policyActions = byByte (oh>>>mode)
  [ (3,buy), (4,transfer), (5,submit), (6,assess)
  , (7,redeem), (8,returnDraw), (9,surrender) ]
 where
  old = iih
  reserve = ioh
  oldOwner = old>>>owner
  oldId = old>>>claimId
  cover = old>>>ioh
  pending = old>>>iih
  who = roleOfOwner oldOwner
  size = oh>>>amount
  checkPhase expected = old>>>phaseIs expected>>>verify
  hasCover = positiveAmount cover
  claimable = checks [hasCover,old>>>phaseIn [Ref.Available,Ref.Denied,Ref.Paid,Ref.DepositReturned]>>>verify]
  noArgOrAmount = checks [zeroArg oh,zeroAmount oh]
  keepStatus newPhase newCover newPending = policyFields (c8 (phaseCode newPhase)) oldOwner oldId newCover newPending
  after nextCapital newPolicy newEffects = newEffects&&&(nextCapital&&&newPolicy)
  noPaymentAction auth newPolicy = after reserve newPolicy (effects auth noPayment noPayment)
  buy = checked (checks [checkPhase Ref.Unused,((oh>>>argument)&&&c8 1)>>>A.le word8>>>verify,
                         positiveAmount size,le size (c32 Ref.maxCover)])
    (after (add reserve premium) newPolicy (effects buyer (buyer&&&premium) noPayment))
   where
    buyer = roleOfOwner (oh>>>argument)
    premium = (add size (c32 9)&&&c32 10)>>>A.divide word32
    newPolicy = policyFields (c8 (phaseCode Ref.Available)) (oh>>>argument) (c16 0) size (c32 0)
  transfer = checked (checks [noArgOrAmount,hasCover])
    (noPaymentAction who (policyFields (old>>>phase) nextOwner oldId cover pending))
   where nextOwner = select (is oldOwner (c8 0)) (c8 1) (c8 0)
  submit = checked (checks [zeroArg oh,claimable,positiveAmount size,le size cover])
    (after reserve newPolicy (effects who (who&&&c32 Ref.deposit) noPayment))
   where
    increment = (oldId&&&c16 1)>>>A.add word16>>>checked (not oh>>>verify) ih
    newPolicy = policyFields (c8 (phaseCode Ref.Pending)) oldOwner increment cover size
  assess = checked (checks [zeroAmount oh,checkPhase Ref.Pending])
    (byByte (oh>>>argument)
      [ (0,noPaymentAction (c8 2) (keepStatus Ref.Accepted cover pending))
      , (1,after (add reserve (c32 Ref.deposit)) (keepStatus Ref.Denied cover (c32 0)) (effects (c8 2) noPayment noPayment))
      , (2,noPaymentAction (c8 2) (keepStatus Ref.Draw cover pending))
      ])
  redeem = checked (checks [noArgOrAmount,checkPhase Ref.Accepted])
    (after (subtract32 reserve pending) (keepStatus Ref.Paid (subtract32 cover pending) (c32 0))
      (effects who noPayment (who&&&add pending (c32 Ref.deposit))))
  returnDraw = checked (checks [noArgOrAmount,checkPhase Ref.Draw])
    (after reserve (keepStatus Ref.DepositReturned cover (c32 0))
      (effects (c8 0) noPayment (who&&&c32 Ref.deposit)))
  surrender = checked (checks [noArgOrAmount,claimable])
    (noPaymentAction who (keepStatus Ref.Surrendered (c32 0) (c32 0)))

plan :: forall t. Assert t => t Work Plan
plan = select (((oh>>>mode)&&&c8 3)>>>A.lt word8) capitalPlan policyPlan
 where
  first = is (oh>>>slot) (c8 0)
  policyPlan = checked (((oh>>>slot)&&&c8 1)>>>A.le word8>>>verify)
    ((selected>>>policyActions)&&&iden>>>restore)
  selected :: t Work PolicyWork
  selected = oh&&&(ioh&&&select first (ih>>>ioh) (ih>>>iih))
  restore :: t (PolicyPlan,Work) Plan
  restore = ooh&&&injr (oioh&&&select (drop first)
    (oiih&&&(ih>>>ih>>>iih)) ((ih>>>ih>>>ioh)&&&oiih))

at :: (Assert t,Primitive t,TyC a,TyC b) => Integer -> P.Prim Word32 (Either () b) -> t a b
at index field = c32 index>>>primitive field>>>verify

authorize :: (Simplicity t,Primitive t) => t (Either () Signature,Word8) ()
authorize = match (same ih (c8 0))
  (((ih>>>publicKey)&&&(unit>>>sigMsg))&&&oh>>>Secp.bip_0340_verify)

funding :: (Assert t,Primitive t) => t Payment ()
funding = checks
  [ same (at 1 P.InputValue) (add ih (c32 Ref.fee)>>>z32)
  , select (is oh (c8 0)) (same ih (c32 0))
      (same (at 1 P.InputScriptHash) (oh>>>roleScript))
  ]

outCount :: (Assert t,Primitive t,TyC a) => Integer -> t a ()
outCount n = same (unit>>>Tx.numOutputs) (c32 n)

pay :: (Assert t,Primitive t) => Integer -> t Payment ()
pay index = checks
  [ positiveAmount ih
  , same (at index P.OutputValue) (ih>>>z32)
  , same (at index P.OutputScriptHash) (oh>>>roleScript)
  ]

layout :: forall t. (Simplicity t,Primitive t) => t (Either () Ledger,Payment) ()
layout = match (checks [outCount 1,ih>>>pay 0]) continuing
 where
  continuing :: t (Ledger,Payment) ()
  continuing = checks
    [ oh>>>validLedger
    , same (at 0 P.OutputValue) (oh>>>value>>>z32)
    , same (at 0 P.OutputScriptHash) (oh>>>stateScriptT)
    , select (is ioh (c8 0)) (checks [outCount 1,same iih (c32 0)])
        (checks [outCount 2,ih>>>pay 1])
    ]

common :: (Simplicity t,Primitive t) => t Ledger ()
common = checks
  [ same (unit>>>primitive P.CurrentIndex) (c32 0)
  , same (unit>>>Tx.numInputs) (c32 2)
  , not (is (at 0 P.InputPrevOutpoint) (at 1 P.InputPrevOutpoint))>>>verify
  , validLedger
  , same (at 0 P.InputValue) (value>>>z32)
  , loadState stateWord
  , same (at 0 P.InputScriptHash) stateScriptT
  ]

kernel :: forall t. (Simplicity t,Primitive t) => t Proof ()
kernel = checked (oh>>>common) (((ioh&&&oh)>>>plan)&&&iih)>>>settle
 where
  settle :: t (Plan,Either () Signature) ()
  settle = checks
    [ (ih&&&(ooh>>>oh))>>>authorize
    , ooh>>>ioh>>>funding
    , (oih&&&(ooh>>>iih))>>>layout
    ]

program :: Proof -> Prog
program = boundProgram kernel

packPolicy :: Ref.Policy -> PolicyW
packPolicy p = (((w8 (phaseCode (Ref.phase p)),w8 (toInteger (fromEnum (Ref.owner p)))),w16 (Ref.claimId p)),
  (w32 (Ref.cover p),w32 (Ref.requested p)))

packLedger :: Ref.State -> Ledger
packLedger (Ref.State reserve (first,second)) = (w32 reserve,(packPolicy first,packPolicy second))

mutualCmr :: Hash256
mutualCmr = progCmr (program (packLedger Ref.setup,((w8 2,(w8 0,(w8 0,w32 0))),Left ())))

referenceAudit :: Bool
referenceAudit = Ref.referenceAudit

entry :: Entry
entry = Entry "app-native-mutual-insurance" "Funded two-policy mutual cover, assessment and settlement"
  "Pinned Nexus Mutual 9e885628 Cover.sol, CoverNFT.sol, Assessments.sol, AssessmentLib.sol, Claims.sol and Pool.sol"
  CrossChain (Derived "independent Integer transition ledger, real Bitcoin input and output amounts/scripts, native BIP340 authorization")
  [ "one initialized BTC pool with a 1000-sat state anchor, two one-time policy slots, two registered owners and one capital provider"
  , "fixed premium ceil(cover/10), claim deposit 1000 sat, fee 3000 sat, cover at most 4000000 sat per policy, total funds excluding anchor at most 10000000 sat"
  , "underwriting capital alone must cover both remaining exposures, refundable claim deposits are reserved separately"
  , "one authenticated assessor decides each pending claim, accepted owner redemption pays amount plus deposit, draw refunds deposit once, denial converts it to capital"
  , "live cover can transfer between fixed owners, paid or returned claims cannot redeem again, signed owner surrender releases exposure without a pending deposit"
  , "actual input 0 is the pool, input 1 supplies exact fee and any role-bound funding, output scripts and amounts checked"
  , "explicit owner release replaces expiration, single assessor replaces voting and timing, no token staking or foreign solvency ratio"
  ] program vectors

type Coin = (Ref.State,D.Outpoint)

request :: Integer -> Integer -> Integer -> Integer -> Request
request m s a n = (w8 m,(w8 s,(w8 a,w32 n)))

packAction :: Ref.Action -> Request
packAction action = case action of
  Ref.Fund n -> request 0 0 0 n
  Ref.Withdraw n -> request 1 0 0 n
  Ref.ClosePool -> request 2 0 0 0
  Ref.Buy s who n -> request 3 (index s) (toInteger (fromEnum who)) n
  Ref.Transfer s -> request 4 (index s) 0 0
  Ref.Submit s n -> request 5 (index s) 0 n
  Ref.Assess s verdict -> request 6 (index s) (toInteger (fromEnum verdict)) 0
  Ref.Redeem s -> request 7 (index s) 0 0
  Ref.ReturnDraw s -> request 8 (index s) 0 0
  Ref.Surrender s -> request 9 (index s) 0 0
 where index = toInteger . fromEnum

stateOutput :: Ref.State -> D.TxOutput
stateOutput s = mkOutput (fromInteger (Ref.value s)) (stateScript mutualCmr (Ref.encode s))

roleOutput :: Ref.Role -> Integer -> D.TxOutput
roleOutput role n = mkOutput (fromInteger n) (p2tr (key role))

poolInput :: Coin -> D.SigTxInput
poolInput (s,prev) =
  mkInput prev (fromInteger (Ref.value s)) (BL.fromStrict (stateScript mutualCmr (Ref.encode s))) 0

feeSource :: Coin -> Maybe (Ref.Role,Integer) -> D.SigTxInput
feeSource coin charged = externalInput coin (maybe 5599 (key . fst) charged)
  (Ref.fee + maybe 0 snd charged)

externalInput :: Coin -> Integer -> Integer -> D.SigTxInput
externalInput (_,D.Outpoint h _) sk n =
  mkInput (D.Outpoint (sha256 (hashToBytes h)) 1) (fromInteger n) (BL.fromStrict (p2tr sk)) 0

construct :: Coin -> Maybe (Ref.Role,Integer) -> [D.TxOutput] -> D.SigTx
construct coin charged = flip (mkTx 2 [poolInput coin,feeSource coin charged]) 0

transaction :: Coin -> Ref.Action -> (D.SigTx,Ref.Step)
transaction coin@(old,_) action = (construct coin debit outputs,result)
 where
  result@(Ref.Step next _ debit payment) = maybe (error ("bad Nexus fixture " ++ show action)) id (Ref.transition old action)
  outputs = maybe [] (pure . stateOutput) next ++ maybe [] (pure . uncurry roleOutput) payment

initial :: Coin
initial = (Ref.setup,dummyOutpoint 5580)

advance :: Coin -> Ref.Action -> Coin
advance coin action = (next,D.Outpoint (sha256 (hashToBytes (sha256 wire))) 0)
 where
  (tx,result) = transaction coin action
  next = maybe (error "terminal Nexus fixture has no continuation") id (Ref.nextState result)
  wire = BL.toStrict (runPutLazy (D.putNoWitnessTx tx))

follow :: Coin -> [Ref.Action] -> Coin
follow = L.foldl' advance

{-# NOINLINE sigAllWrapped #-}
sigAllWrapped :: J.WrappedSimplicity () Word256
sigAllWrapped = J.jetSubst sigMsg

signature :: Ref.Role -> Ref.State -> D.SigTx -> Signature
signature role old tx = case mkEnv tx 0 (\leaf -> stateTap leaf (Ref.encode old)) mutualCmr of
  Just env -> case J.fastEval (J.unwrap sigAllWrapped) env () of
    Just digest -> case signMsg (key role) (w256ToBytes digest) of
      Sig r s -> (w256 (toInteger r),w256 (toInteger s))
    Nothing -> error "Nexus signature message"
  Nothing -> error "Nexus signature environment"

makeVector :: String -> Ref.State -> Proof -> D.SigTx -> DW.Word32 -> Expect -> Vector Proof
makeVector name actual opening tx index = Vector name
  (mkEnv tx index (\leaf -> stateTap leaf (Ref.encode actual))) opening

evidence :: Ref.State -> Request -> Maybe Ref.Role -> D.SigTx -> Proof
evidence old action role tx =
  (packLedger old,(action,maybe (Left ()) (Right . (\r -> signature r old tx)) role))

positive :: String -> Coin -> Ref.Action -> Vector Proof
positive name coin@(old,_) action =
  makeVector name old (evidence old (packAction action) (Ref.authorization result) tx) tx 0 Accept
 where (tx,result) = transaction coin action

vectors :: [Vector Proof]
vectors = positives ++ negatives
 where
  alice = Ref.PolicyOwner Ref.Alice
  bob = Ref.PolicyOwner Ref.Bob
  provider = Ref.CapitalProvider
  assessor = Ref.Assessor
  a = Ref.First
  b = Ref.Second
  funded = advance initial (Ref.Fund 80000)
  first = advance funded (Ref.Buy a Ref.Alice 50000)
  both = advance first (Ref.Buy b Ref.Bob 30000)
  pendA = advance both (Ref.Submit a 20000)
  pendBoth = advance pendA (Ref.Submit b 10000)
  acceptA = advance pendBoth (Ref.Assess a Ref.AcceptClaim)
  transferA = advance acceptA (Ref.Transfer a)
  paidA = advance transferA (Ref.Redeem a)
  denyA = advance pendBoth (Ref.Assess a Ref.DenyClaim)
  claimAgain = advance denyA (Ref.Submit a 13000)
  drawB = advance paidA (Ref.Assess b Ref.DrawClaim)
  transferredDraw = advance drawB (Ref.Transfer b)
  returnedB = advance transferredDraw (Ref.ReturnDraw b)
  surrenderA = advance returnedB (Ref.Surrender a)
  surrendered = advance surrenderA (Ref.Surrender b)
  drained = advance surrendered (Ref.Withdraw (Ref.capital (fst surrendered)))
  exhaustedA = follow paidA [Ref.Submit a 30000,Ref.Assess a Ref.AcceptClaim]
  nearMax = advance initial (Ref.Fund (Ref.maxCapital-1500))
  maxBooked = follow nearMax [Ref.Buy a Ref.Alice 5000,Ref.Submit a 2500]
  smallDraw = follow initial [Ref.Fund 950,Ref.Buy a Ref.Alice 500,Ref.Submit a 200,Ref.Assess a Ref.DrawClaim]
  duplicateTx = mkTx 2 [poolInput smallDraw,poolInput (fst smallDraw,dummyOutpoint 5598)]
    (txOutputs (txFor smallDraw (Ref.ReturnDraw a))) 0
  duplicateW = evidence (fst smallDraw) (packAction (Ref.ReturnDraw a)) Nothing duplicateTx
  positives =
    [ positive "fund real capital from provider" initial (Ref.Fund 80000)
    , positive "buy first cover and credit exact premium" funded (Ref.Buy a Ref.Alice 50000)
    , positive "buy second cover against aggregate collateral" first (Ref.Buy b Ref.Bob 30000)
    , positive "positive fractional premium rounds upward" first (Ref.Buy b Ref.Bob 10001)
    , positive "current owner transfers live cover" both (Ref.Transfer a)
    , positive "first owner funds one refundable deposit" both (Ref.Submit a 20000)
    , positive "second policy submits concurrent funded claim" pendA (Ref.Submit b 10000)
    , positive "withdraw exact unencumbered capital while both deposits remain reserved" pendBoth (Ref.Withdraw 8000)
    , positive "authorized assessor accepts first claim" pendBoth (Ref.Assess a Ref.AcceptClaim)
    , positive "transfer accepted unredeemed cover" acceptA (Ref.Transfer a)
    , positive "new owner redeems exact claim plus deposit" transferA (Ref.Redeem a)
    , positive "authorized denial forfeits deposit to capital" pendBoth (Ref.Assess a Ref.DenyClaim)
    , positive "denied policy can file again with new claim ID" denyA (Ref.Submit a 13000)
    , positive "denial still fits when total reserved funds reach the cap" maxBooked (Ref.Assess a Ref.DenyClaim)
    , positive "authorized draw preserves cover and deposit obligation" paidA (Ref.Assess b Ref.DrawClaim)
    , positive "transfer drawn claim before deposit return" drawB (Ref.Transfer b)
    , positive "permissionless draw refund pays new owner only" transferredDraw (Ref.ReturnDraw b)
    , positive "paid policy can claim remaining coverage" paidA (Ref.Submit a 30000)
    , positive "full remaining payout exhausts first policy" exhaustedA (Ref.Redeem a)
    , positive "first owner releases settled cover by signed surrender" returnedB (Ref.Surrender a)
    , positive "second owner releases settled cover separately" surrenderA (Ref.Surrender b)
    , positive "all underwriting capital is withdrawable after release" surrendered (Ref.Withdraw (Ref.capital (fst surrendered)))
    , positive "empty pool closes and releases carrier" drained Ref.ClosePool
    , makeVector "duplicate-draw control authorizes input zero" (fst smallDraw) duplicateW duplicateTx 0 Accept
    ]
  txFor coin action = fst (transaction coin action)
  txOutputs = V.toList . D.sigTxOut
  txInputs = V.toList . D.sigTxIn
  changeOutputs tx outs = mkTx 2 (txInputs tx) outs 0
  changeInput coin replacement tx = mkTx 2 [poolInput coin,replacement] (txOutputs tx) 0
  reject name coin action role tx =
    makeVector name (fst coin) (evidence (fst coin) action role tx) tx 0 Reject
  bad name coin action = reject name coin (packAction action)
  fundTx = txFor initial (Ref.Fund 80000)
  cheapBuyTx = txFor first (Ref.Buy b Ref.Bob 10001)
  claimTx = txFor both (Ref.Submit a 20000)
  assessTx = txFor pendBoth (Ref.Assess a Ref.AcceptClaim)
  acceptSecond = txFor pendBoth (Ref.Assess b Ref.AcceptClaim)
  transferTx = txFor acceptA (Ref.Transfer a)
  paidTx = txFor transferA (Ref.Redeem a)
  refundTx = txFor transferredDraw (Ref.ReturnDraw b)
  feeTx coin outs = construct coin Nothing outs
  spentState = fst transferA
  paidOutput = head (txOutputs paidTx)
  refundOutput = head (txOutputs refundTx)
  replaceA s p = s { Ref.policies = (p,snd (Ref.policies s)) }
  oversold = (fst first) { Ref.capital = 89000
    , Ref.policies = (fst (Ref.policies (fst first)),Ref.Policy Ref.Available Ref.Bob 0 40000 0) }
  overclaim n = replaceA (fst both) (Ref.Policy Ref.Pending Ref.Alice 1 50000 n)
  unauthorisedWithdrawal = (fst pendBoth) { Ref.capital = 79999 }
  paidWithoutReduction = replaceA (fst paidA) ((fst (Ref.policies (fst paidA))) { Ref.cover = 50000 })
  originalVerdict = signature assessor (fst pendBoth) assessTx
  reusedVerdict coin action = (packLedger (fst coin),(packAction action,Right originalVerdict))
  forgedOpening = replaceA spentState ((fst (Ref.policies spentState)) { Ref.requested = 19000 })
  reinput prev script n tx = mkTx 2 [mkInput prev (fromInteger n) (BL.fromStrict script) 0,last (txInputs tx)]
    (txOutputs tx) 0
  negatives =
    [ bad "capital funding rejects another role signature" initial (Ref.Fund 80000) (Just alice) fundTx
    , bad "capital funding must be an actual matching amount" initial (Ref.Fund 80000) (Just provider)
        (changeInput initial (externalInput initial (key provider) (Ref.fee+79999)) fundTx)
    , bad "capital funding must use provider script" initial (Ref.Fund 80000) (Just provider)
        (changeInput initial (externalInput initial (key alice) (Ref.fee+80000)) fundTx)
    , bad "funding above bounded capital limit" initial (Ref.Fund (Ref.maxCapital+1)) (Just provider)
        (construct initial (Just (provider,Ref.maxCapital+1)) [stateOutput (Ref.setup { Ref.capital = Ref.maxCapital+1 })])
    , bad "cannot sell cover against insufficient combined capital" first (Ref.Buy b Ref.Bob 40000) (Just bob)
        (construct first (Just (bob,4000)) [stateOutput oversold])
    , bad "rounded-down premium does not fund policy" first (Ref.Buy b Ref.Bob 10001) (Just bob)
        (changeInput first (externalInput first (key bob) (Ref.fee+1000)) cheapBuyTx)
    , bad "one-time policy slot cannot be purchased again" first (Ref.Buy a Ref.Alice 10000) (Just alice)
        (construct first (Just (alice,1000)) [stateOutput (fst first)])
    , reject "unregistered policy owner code" first (request 3 1 2 10001) (Just bob) cheapBuyTx
    , bad "withdrawal cannot consume refundable deposit or reserved cover" pendBoth (Ref.Withdraw 8001) (Just provider)
        (feeTx pendBoth [stateOutput unauthorisedWithdrawal,roleOutput provider 8001])
    , bad "pool cannot close with live cover and outstanding deposits" pendBoth Ref.ClosePool (Just provider)
        (feeTx pendBoth [roleOutput provider (Ref.value (fst pendBoth))])
    , bad "claim exceeds current cover" both (Ref.Submit a 50001) (Just alice)
        (construct both (Just (alice,Ref.deposit)) [stateOutput (overclaim 50001)])
    , bad "zero claim amount" both (Ref.Submit a 0) (Just alice)
        (construct both (Just (alice,Ref.deposit)) [stateOutput (overclaim 0)])
    , bad "existing pending claim cannot be overwritten" pendA (Ref.Submit a 10000) (Just alice)
        (construct pendA (Just (alice,Ref.deposit)) [stateOutput (fst pendA)])
    , bad "another claim cannot replace accepted unredeemed cover" acceptA (Ref.Submit a 10000) (Just alice)
        (construct acceptA (Just (alice,Ref.deposit)) [stateOutput (fst acceptA)])
    , bad "claim deposit must be funded in full" both (Ref.Submit a 20000) (Just alice)
        (changeInput both (externalInput both (key alice) (Ref.fee+Ref.deposit-1)) claimTx)
    , bad "claim deposit must use current owner funding script" both (Ref.Submit a 20000) (Just alice)
        (changeInput both (externalInput both (key bob) (Ref.fee+Ref.deposit)) claimTx)
    , bad "owner cannot self-approve claim" pendBoth (Ref.Assess a Ref.AcceptClaim) (Just alice) assessTx
    , reject "invalid assessment outcome" pendBoth (request 6 0 3 0) (Just assessor) assessTx
    , makeVector "assessor signature cannot move to another policy" (fst pendBoth)
        (reusedVerdict pendBoth (Ref.Assess b Ref.AcceptClaim)) acceptSecond 0 Reject
    , makeVector "assessor signature cannot move to the next claim ID" (fst claimAgain)
        (reusedVerdict claimAgain (Ref.Assess a Ref.AcceptClaim))
        (txFor claimAgain (Ref.Assess a Ref.AcceptClaim)) 0 Reject
    , bad "accepted claim cannot be assessed again" acceptA (Ref.Assess a Ref.DenyClaim) (Just assessor)
        (feeTx acceptA [stateOutput (fst acceptA)])
    , bad "buyer cannot transfer another owner's cover" acceptA (Ref.Transfer a) (Just bob) transferTx
    , bad "old owner cannot redeem after transfer" transferA (Ref.Redeem a) (Just alice) paidTx
    , bad "accepted payout returns the full assessment deposit" transferA (Ref.Redeem a) (Just bob)
        (changeOutputs paidTx [paidOutput,roleOutput bob 20000])
    , bad "accepted payout must reduce remaining cover" transferA (Ref.Redeem a) (Just bob)
        (changeOutputs paidTx [mkOutput 70000 (stateScript mutualCmr (Ref.encode paidWithoutReduction)),roleOutput bob 21000])
    , bad "paid claim cannot redeem twice" paidA (Ref.Redeem a) (Just bob)
        (feeTx paidA [stateOutput (fst paidA),roleOutput bob 21000])
    , bad "denied claim cannot redeem or recover deposit" denyA (Ref.ReturnDraw a) Nothing
        (feeTx denyA [stateOutput (fst denyA),roleOutput alice Ref.deposit])
    , bad "denied claim cannot receive an accepted payout" denyA (Ref.Redeem a) (Just alice)
        (feeTx denyA [stateOutput (fst denyA),roleOutput alice 21000])
    , bad "pending assessment deposit is still reserved" pendBoth (Ref.ReturnDraw a) Nothing
        (feeTx pendBoth [stateOutput (fst pendBoth),roleOutput alice Ref.deposit])
    , bad "draw refund cannot pay the old owner" transferredDraw (Ref.ReturnDraw b) Nothing
        (changeOutputs refundTx [refundOutput,roleOutput bob Ref.deposit])
    , bad "draw refund cannot include the claimed loss" transferredDraw (Ref.ReturnDraw b) Nothing
        (changeOutputs refundTx [refundOutput,roleOutput alice 11000])
    , bad "draw deposit cannot be collected twice" returnedB (Ref.ReturnDraw b) Nothing
        (feeTx returnedB [stateOutput (fst returnedB),roleOutput alice Ref.deposit])
    , bad "owner cannot surrender while claim deposit is open" pendBoth (Ref.Surrender a) (Just alice)
        (feeTx pendBoth [stateOutput (fst pendBoth)])
    , bad "unexpected extra transaction output" transferredDraw (Ref.ReturnDraw b) Nothing
        (changeOutputs refundTx (txOutputs refundTx ++ [mkOutput 1 BS.empty]))
    , bad "actual current input script must commit this ledger" transferA (Ref.Redeem a) (Just bob)
        (reinput (snd transferA) (p2tr (key provider)) (Ref.value spentState) paidTx)
    , bad "actual current input value must match the funded ledger" transferA (Ref.Redeem a) (Just bob)
        (reinput (snd transferA) (stateScript mutualCmr (Ref.encode spentState)) (Ref.value spentState-1) paidTx)
    , makeVector "different requested amount cannot open the current state" spentState
        (evidence forgedOpening (packAction (Ref.Redeem a)) (Just bob) paidTx) paidTx 0 Reject
    , reject "unsupported policy slot" both (request 4 2 0 0) (Just alice) (txFor both (Ref.Transfer a))
    , makeVector "second funded input cannot reuse one permissionless draw payout"
        (fst smallDraw) duplicateW duplicateTx 1 Reject
    ]
