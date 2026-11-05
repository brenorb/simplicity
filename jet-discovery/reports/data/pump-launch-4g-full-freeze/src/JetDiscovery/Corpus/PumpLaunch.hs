{-# LANGUAGE RankNTypes #-}
-- | Funded native vouchers with a finite virtual-reserve launch and migration.
module JetDiscovery.Corpus.PumpLaunch (entry,launchCmr,referenceAudit) where

import Prelude hiding (not,take,drop)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as List
import qualified Data.Vector as V
import qualified Data.Word as DW
import Data.Serialize (runPutLazy)
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import Simplicity.Digest (Hash256)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (not,verify)
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Term.Core
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Corpus.Baseline (signMsg)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Lib.Bytes (konst,failure,w32,w256FromBytes,w256ToBytes)
import JetDiscovery.Lib.State (loadState,stateScript,stateScriptHash,stateTap)
import JetDiscovery.Lib.TwoCryptoArithmetic (checked,checks,equal,same,select)
import qualified JetDiscovery.Ref.Bip340 as Bip
import qualified JetDiscovery.Ref.PumpLaunch as Ref
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

type Ledger = Word256
type Request = ((Word32,Word32),(Word32,Word32))
type Work = (Ledger,Request)
type Proof = (Work,G.SigW)
type Payment = (Word32,Word32)
type OptionalPay = Either () Payment
type Effects = (Word32,(OptionalPay,OptionalPay))
type Plan = (Either () Ledger,Effects)

c :: (Core t,TyC a) => Integer -> t a Word32
c = konst . w32

add,sub,mul,quotient :: (Assert t,TyC a) => t a Word32 -> t a Word32 -> t a Word32
add a b = (a&&&b)>>>A.add word32>>>checked (not oh>>>verify) ih
sub a b = (a&&&b)>>>A.subtract word32>>>checked (not oh>>>verify) ih
mul a b = (a&&&b)>>>A.multiply word32>>>checked (same oh (c 0)) ih
quotient a b = (a&&&b)>>>checked (positive ih) (A.divide word32)

le :: (Assert t,TyC a) => t a Word32 -> t a Word32 -> t a ()
le a b = (a&&&b)>>>A.le word32>>>verify

positive :: (Assert t,TyC a) => t a Word32 -> t a ()
positive a = (c 0&&&a)>>>A.lt word32>>>verify

stage,left,alice,bob,cash :: Core t => t Ledger Word32
stage = oooh
left = ooih
alice = oioh
bob = oiih
cash = iooh

pack :: (Core t,TyC a) => t a Word32 -> t a Word32 -> t a Word32 -> t a Word32 -> t a Word32 -> t a Ledger
pack p r a b q = ((p&&&r)&&&(a&&&b))&&&((q&&&c 0)&&&(c 0&&&c 0))

funding :: Integer
funding = (Ref.inventory+Ref.migrationInventory)*Ref.voucherValue

owners :: Assert t => t Ledger Word32
owners = add alice bob

valid :: Assert t => t Ledger ()
valid = checks
  [ same ioih (c 0),same iioh (c 0),same iiih (c 0),le cash (c Ref.maxQuote)
  , select (equal stage (c 0))
      (same iden (pack (c 0) (c 0) (c 0) (c 0) (c 0)))
      (select (equal stage (c 1)) (same (add left owners) (c Ref.inventory))
        (checks [same stage (c 2),same left (c 0),same cash (c 0),positive owners,le owners (c Ref.inventory)]))
  ]

value :: Assert t => t Ledger Word32
value = add (c Ref.carrier) (select (equal stage (c 0)) (c 0)
  (select (equal stage (c 1)) (add (c funding) cash) (mul owners (c Ref.voucherValue))))

mode,actor,amount,limit :: Core t => t Work Word32
mode = iooh
actor = ioih
amount = iioh
limit = iiih

ownerFields :: (Assert t,TyC a) => t a Word32 -> t a Word32 -> t a Word32 -> t a (Word32,Word32)
ownerFields who own other =
  select (equal who (c 0)) (own&&&other) (other&&&own)

balance :: (Assert t,TyC a) => t a Word32 -> t a Ledger -> t a Word32
balance who old = select (equal who (c 0)) (old>>>alice) (old>>>bob)

otherBalance :: (Assert t,TyC a) => t a Word32 -> t a Ledger -> t a Word32
otherBalance who old = select (equal who (c 0)) (old>>>bob) (old>>>alice)

open :: Assert t => t Work ()
open = checks [same (oh>>>stage) (c 1),positive (oh>>>left)]

quantity :: Assert t => t Work ()
quantity = checks [le actor (c 1),positive amount]

seller :: Assert t => t Work ()
seller = checks [quantity,le amount (balance actor oh)]

noPay :: (Core t,TyC a) => t a OptionalPay
noPay = injl unit

pay :: (Core t,TyC a) => t a Word32 -> t a Word32 -> t a OptionalPay
pay who n = injr (who&&&n)

continue :: (Core t,TyC a) => t a Ledger -> t a Word32 -> t a OptionalPay -> t a OptionalPay -> t a Plan
continue new fund first second = injr new&&&(fund&&&(first&&&second))

initialize :: Assert t => t Work Plan
initialize = checked (same (oh>>>stage) (c 0))
  (continue (pack (c 1) (c Ref.inventory) (c 0) (c 0) (c 0)) (c funding) noPay noPay)

curveQuote :: Assert t => t Work Word32
curveQuote = add (oh>>>cash) (c Ref.virtualQuoteOffset)

curveBase :: Assert t => t Work Word32
curveBase = add (oh>>>left) (c Ref.virtualBaseOffset)

tradeFee :: Assert t => t Word32 Word32
tradeFee = quotient (add iden (c 99)) (c 100)

buy :: Assert t => t Work Plan
buy = checked (checks [open,quantity,le amount (oh>>>left)]) (iden&&&cost)>>>
  (iden&&&(ih>>>tradeFee))>>>checked (le gross (ooh>>>limit))
  (continue new gross (pay (c (toInteger Ref.protocol)) ih) noPay)
 where
  cost = add (quotient (mul amount curveQuote) (sub curveBase amount)) (c 1)
  gross = add oih ih
  old = ooh>>>oh
  who = ooh>>>actor
  q = ooh>>>amount
  credits = ownerFields who (add (balance who old) q) (otherBalance who old)
  new = pack (c 1) (sub (old>>>left) q) (credits>>>oh) (credits>>>ih) (add (old>>>cash) oih)

sell :: Assert t => t Work Plan
sell = checked (checks [open,seller]) (iden&&&gross)>>>
  (iden&&&(ih>>>tradeFee))>>>checked (le paid (ooh>>>limit))
  (continue new (c 0) (pay who paid) (pay (c (toInteger Ref.protocol)) ih))
 where
  gross = quotient (mul amount curveQuote) (add curveBase amount)
  paid = sub oih ih
  old = ooh>>>oh
  who = ooh>>>actor
  q = ooh>>>amount
  credits = ownerFields who (sub (balance who old) q) (otherBalance who old)
  new = pack (c 1) (add (old>>>left) q) (credits>>>oh) (credits>>>ih) (sub (old>>>cash) oih)

transfer :: Assert t => t Work Plan
transfer = checked (checks [positive (oh>>>stage),seller]) (continue new (c 0) noPay noPay)
 where
  credits = ownerFields actor (sub (balance actor oh) amount) (add (otherBalance actor oh) amount)
  new = pack (oh>>>stage) (oh>>>left) (credits>>>oh) (credits>>>ih) (oh>>>cash)

migrate :: Assert t => t Work Plan
migrate = checked (checks [same (oh>>>stage) (c 1),same (oh>>>left) (c 0),positive (sub (oh>>>cash) (c Ref.migrationFee))])
  (continue new (c 0) (pay (c (toInteger Ref.destination)) handoff)
    (pay (c (toInteger Ref.protocol)) (c Ref.migrationFee)))
 where
  handoff = add (sub (oh>>>cash) (c Ref.migrationFee)) (c (Ref.migrationInventory*Ref.voucherValue))
  new = pack (c 2) (c 0) (oh>>>alice) (oh>>>bob) (c 0)

redeem :: Assert t => t Work Plan
redeem = checked (checks [same (oh>>>stage) (c 2),seller])
  (select (equal amount (oh>>>owners)) finish (continue new (c 0) payout noPay))
 where
  credits = ownerFields actor (sub (balance actor oh) amount) (otherBalance actor oh)
  new = pack (c 2) (c 0) (credits>>>oh) (credits>>>ih) (c 0)
  payout = pay actor (mul amount (c Ref.voucherValue))
  finish = injl unit&&&(c 0&&&(payout&&&pay (c (toInteger Ref.sponsor)) (c Ref.carrier)))

plan :: Assert t => t Work Plan
plan = List.foldr (\(i,term) rest -> select (equal mode (c i)) term rest) failure
  [(0,initialize),(1,buy),(2,sell),(3,transfer),(4,migrate),(5,redeem)]

keys :: [Integer]
keys = G.keys++[5505]

script :: Int -> BS.ByteString
script role = unhex "5120"<>Bip.bytesFromInt (Bip.pubkeyOf (keys !! role))

roleHash :: Assert t => t Word32 Word256
roleHash = List.foldr (\i rest -> select (equal iden (c (toInteger i))) (konst (G.scriptHash (script i))) rest)
  failure [0..4]

publicKey :: Assert t => t Work Word256
publicKey = select (equal mode (c 0)) (key Ref.sponsor) (select (equal actor (c 0)) (key 0) (key 1))
 where key i = konst (w256FromBytes (Bip.bytesFromInt (Bip.pubkeyOf (keys !! i))))

authorize :: (Simplicity t,Primitive t) => t Proof ()
authorize = select (equal (oh>>>mode) (c 4)) unit
  (((oh>>>publicKey)&&&(unit>>>sigMsg))&&&ih>>>Secp.bip_0340_verify)

at :: (Assert t,Primitive t,TyC a,TyC b) => Integer -> P.Prim Word32 (Either () b) -> t a b
at i field = c i>>>primitive field>>>verify

z32 :: Core t => t Word32 Word64
z32 = c 0&&&iden

common :: (Simplicity t,Primitive t) => t Ledger ()
common = checks
  [ valid,loadState iden
  , same (unit>>>primitive P.CurrentIndex) (c 0),same (unit>>>Tx.numInputs) (c 2)
  , not (equal (at 0 P.InputPrevOutpoint) (at 1 P.InputPrevOutpoint))>>>verify
  , same (at 0 P.InputValue) (value>>>z32)
  , same (at 0 P.InputScriptHash) (stateScriptHash iden)
  ]

outCount :: (Assert t,Primitive t,TyC a) => Integer -> t a ()
outCount n = same (unit>>>Tx.numOutputs) (c n)

payAt :: (Assert t,Primitive t) => Integer -> t Payment ()
payAt i = checks [positive ih,same (at i P.OutputValue) (ih>>>z32),same (at i P.OutputScriptHash) (oh>>>roleHash)]

paymentsAt :: (Assert t,Primitive t) => Integer -> t Effects ()
paymentsAt i = ih>>>match
  (ih>>>copair (outCount i) failure)
  (checks [take (payAt i),ih>>>copair (outCount (i+1)) (checks [outCount (i+2),payAt (i+1)])])

settle :: (Simplicity t,Primitive t) => t Plan ()
settle = checks
  [ same (at 1 P.InputValue) (add ioh (c Ref.fee)>>>z32)
  , match (drop (paymentsAt 0)) (checks
      [ oh>>>valid,same (at 0 P.OutputValue) (oh>>>value>>>z32)
      , same (at 0 P.OutputScriptHash) (stateScriptHash oh),drop (paymentsAt 1)])
  ]

kernel :: (Simplicity t,Primitive t) => t Proof ()
kernel = checks [ooh>>>common,authorize,oh>>>plan>>>settle]

program :: Proof -> Prog
program = boundProgram kernel

launchCmr :: Hash256
launchCmr = progCmr (program ((w256FromBytes (Ref.encode Ref.setup),((w32 0,w32 0),(w32 0,w32 0))),G.zeroSig))

referenceAudit :: Bool
referenceAudit = Ref.referenceAudit

entry :: Entry
entry = Entry "app-virtual-reserve-launch" "Funded virtual-reserve launch, sellout and one-time Bitcoin migration"
  "Pump program 639b87fb45c3adeffa6f7c4a1bf0cb85e392bf22 and official pump-rust-client 0.4.1"
  CrossChain (Derived "independent Integer source quotes and native value/state transition fixtures")
  [ "100 launch vouchers and 20 migration vouchers, sponsored at 5000 sats each, two registered holders"
  , "100000 virtual-only quote sats and 30 additional virtual-only base units, 100 bps ceiling protocol fee"
  , "source exact-base buy and sell, fixed bounds, no synthetic overflow-fill, fixed 5000 sat migration fee"
  , "real inventory exhausts, both curve trades stop, permissionless exact one-time handoff, holder backing survives"
  , "owner redemptions and terminal sponsor carrier return, actual input0, exact scripts and values"
  ] program vectors

type Coin = (Ref.State,D.Outpoint)

request :: Ref.Action -> Request
request a = case a of
  Ref.Fund -> req 0 0 0 0
  Ref.Buy who n bound -> req 1 (index who) n bound
  Ref.Sell who n bound -> req 2 (index who) n bound
  Ref.Transfer who n -> req 3 (index who) n 0
  Ref.Migrate -> req 4 0 0 0
  Ref.Redeem who n -> req 5 (index who) n 0
 where
  index = toInteger . fromEnum
  req m who n b = ((w32 m,w32 who),(w32 n,w32 b))

initial :: Coin
initial = (Ref.setup,dummyOutpoint 7151)

stateOutput :: Ref.State -> D.TxOutput
stateOutput s = mkOutput (fromInteger (Ref.value s)) (stateScript launchCmr (Ref.encode s))

payout :: (Int,Integer) -> D.TxOutput
payout (who,n) = mkOutput (fromInteger n) (script who)

construct :: Coin -> Integer -> Maybe Int -> [D.TxOutput] -> D.SigTx
construct (old,prev@(D.Outpoint hash _)) funded who outs =
  mkTx 2
   [mkInput prev (fromInteger (Ref.value old)) (BL.fromStrict (stateScript launchCmr (Ref.encode old))) 0xfffffffe,
    mkInput (D.Outpoint (sha256 (hashToBytes hash)) 1) (fromInteger (funded+Ref.fee))
      (BL.fromStrict (script (maybe 2 id who))) 0xfffffffe] outs 0

transaction :: Coin -> Ref.Action -> (D.SigTx,Ref.Result)
transaction coin@(old,_) action = (construct coin (Ref.funding r) (Ref.authorizer r) outs,r)
 where
  r = maybe (error ("invalid launch fixture "++show action)) id (Ref.transition old action)
  outs = maybe [] (pure . stateOutput) (Ref.next r) ++ map payout (Ref.payouts r)

advance :: Coin -> Ref.Action -> Coin
advance coin action = (next,D.Outpoint (sha256 (hashToBytes (sha256 wire))) 0)
 where
  (tx,r) = transaction coin action
  next = maybe (error "terminal launch fixture") id (Ref.next r)
  wire = BL.toStrict (runPutLazy (D.putNoWitnessTx tx))

{-# NOINLINE sigAllWrapped #-}
sigAllWrapped :: J.WrappedSimplicity () Word256
sigAllWrapped = J.jetSubst sigMsg

vector :: String -> Ref.State -> Ref.State -> Ref.Action -> Maybe Int -> D.SigTx -> DW.Word32 -> Expect -> Vector Proof
vector name actual opening action signer tx ix =
  Vector name env ((w256FromBytes (Ref.encode opening),request action),signature)
 where
  env = mkEnv tx ix (\leaf -> stateTap leaf (Ref.encode actual))
  signature = case signer of
    Nothing -> G.zeroSig
    Just who -> case env launchCmr >>= \e -> J.fastEval (J.unwrap sigAllWrapped) e () of
      Just digest -> G.sigW (signMsg (keys !! who) (w256ToBytes digest))
      Nothing -> error "launch fixture signature"

accept :: String -> Coin -> Ref.Action -> Vector Proof
accept label coin@(old,_) action =
  vector label old old action (Ref.authorizer r) tx 0 Accept
 where (tx,r) = transaction coin action

reject :: String -> Coin -> Ref.Action -> (D.SigTx -> D.SigTx) -> Maybe Int -> DW.Word32 -> Vector Proof
reject label coin@(old,_) action edit signer ix = vector label old old action signer (edit tx) ix Reject
 where (tx,_) = transaction coin action

withInput :: Int -> (D.SigTxInput -> D.SigTxInput) -> D.SigTx -> D.SigTx
withInput i f tx = tx {D.sigTxIn=D.sigTxIn tx V.// [(i,f (D.sigTxIn tx V.! i))]}

withOutput :: Int -> (D.TxOutput -> D.TxOutput) -> D.SigTx -> D.SigTx
withOutput i f tx = tx {D.sigTxOut=D.sigTxOut tx V.// [(i,f (D.sigTxOut tx V.! i))]}

smaller :: D.TxOutput -> D.TxOutput
smaller out = out {D.txoValue=D.txoValue out-1}

wrongScript :: D.TxOutput -> D.TxOutput
wrongScript out = out {D.txoScript=BL.fromStrict (script Ref.sponsor)}

vectors :: [Vector Proof]
vectors = positives ++ negatives
 where
  a = Ref.Alice
  b = Ref.Bob
  buyA = Ref.Buy a 55 74068
  sellA = Ref.Sell a 25 42899
  buyB = Ref.Buy b 45 200000
  transferA = Ref.Transfer a 10
  finalBuy = Ref.Buy a 25 300000
  transferB = Ref.Transfer b 5
  redeemA = Ref.Redeem a 50
  redeemB = Ref.Redeem b 50
  actions =
    [("sponsor funds all 120 vouchers exactly",Ref.Fund),
     ("Alice buys 55 at her exact all-in cap",buyA),
     ("Alice sells 25 at her exact net minimum",sellA),
     ("Bob buys 45 from remaining inventory",buyB),
     ("Alice transfers ten issued vouchers to Bob",transferA),
     ("final exact buy exhausts the real inventory",finalBuy),
     ("permissionless migration pays exact handoff and fee",Ref.Migrate),
     ("Bob transfers five funded post-migration vouchers",transferB),
     ("Alice redeems 50 vouchers to her script",redeemA),
     ("Bob redeems remaining 50 and returns sponsor anchor",redeemB)]
  coins = scanl advance initial (map snd actions)
  [_,funded,bought,sold,both,preComplete,completed,migrated,transferred,onlyBob] = List.take 10 coins
  exactDivision = Ref.Buy a 65 101002
  positives = [accept label coin action | (coin,(label,action))<-zip coins actions] ++
    [accept "exactly divisible buy still adds the source one unit" funded exactDivision]
  otherFunds = withInput 1 (\i -> i {D.sigTxiTxo=smaller (D.sigTxiTxo i)})
  oldValue = withInput 0 (\i -> i {D.sigTxiTxo=smaller (D.sigTxiTxo i)})
  fakeInputScript = withInput 0 (\i -> i {D.sigTxiTxo=wrongScript (D.sigTxiTxo i)})
  duplicate tx = withInput 1 (\i -> i {D.sigTxiPreviousOutpoint=D.sigTxiPreviousOutpoint (D.sigTxIn tx V.! 0)}) tx
  addOutput tx = tx {D.sigTxOut=D.sigTxOut tx V.++ V.singleton (mkOutput 0 (unhex "6a"))}
  reroute role out = out {D.txoScript=BL.fromStrict (script role)}
  signedEdit label coin action edit = reject label coin action edit
    (Ref.authorizer (snd (transaction coin action))) 0
  changedRequest label coin@(old,_) validAction altered who =
    vector label old old altered who (fst (transaction coin validAction)) 0 Reject
  dormant = Ref.setup
  holding = fst completed
  mid = fst preComplete
  completeMigrationOutputs old =
    [stateOutput (old {Ref.phase=Ref.Migrated,Ref.remaining=0,Ref.quote=0}),
     payout (Ref.destination,Ref.quote old-Ref.migrationFee+Ref.migrationInventory*Ref.voucherValue),
     payout (Ref.protocol,Ref.migrationFee)]
  earlyMigration = vector "reject fully formed migration before sellout" mid mid Ref.Migrate Nothing
    (construct preComplete 0 Nothing (completeMigrationOutputs mid)) 0 Reject
  lateGross = div ((Ref.quote holding+Ref.virtualQuoteOffset)*10) (Ref.virtualBaseOffset+10)
  lateFee = div (lateGross+99) 100
  lateSale = holding {Ref.remaining=10,Ref.alice=Ref.alice holding-10,Ref.quote=Ref.quote holding-lateGross}
  lateTrade = vector "reject otherwise well-funded sell once the curve has completed" holding holding
    (Ref.Sell a 10 (lateGross-lateFee)) (Just 0)
    (construct completed 0 (Just 0)
      [stateOutput lateSale,payout (0,lateGross-lateFee),payout (Ref.protocol,lateFee)]) 0 Reject
  migratedState = fst migrated
  postMigration = vector "reject a second permissionless migration" migratedState migratedState Ref.Migrate Nothing
    (construct migrated 0 Nothing [stateOutput migratedState]) 0 Reject
  nextBuy = maybe (error "buy fixture") id (Ref.next (snd (transaction funded buyA)))
  negatives =
    [signedEdit "reject sponsor underfunding by one sat" initial Ref.Fund otherFunds,
     reject "reject sponsor allocation signed by Alice" initial Ref.Fund id (Just 0) 0,
     vector "reject dormant opening with forged initial allocation" dormant (dormant {Ref.alice=1})
       Ref.Fund (Just Ref.sponsor) (fst (transaction initial Ref.Fund)) 0 Reject,
     signedEdit "reject underfunded exact buy" funded buyA otherFunds,
     signedEdit "reject wrong actual state input amount" funded buyA oldValue,
     signedEdit "reject wrong actual state input script" funded buyA fakeInputScript,
     signedEdit "reject duplicate prevout" funded buyA duplicate,
     signedEdit "reject diverted buy fee" funded buyA (withOutput 1 wrongScript),
     signedEdit "reject buy fee rounded down" funded buyA (withOutput 1 smaller),
     signedEdit "reject extra output" funded buyA addOutput,
     signedEdit "reject wrong continuing script" funded buyA (withOutput 0 wrongScript),
     signedEdit "reject issued vouchers attributed to the wrong holder" funded buyA
       (withOutput 0 (const (stateOutput (nextBuy {Ref.alice=54,Ref.bob=1})))),
     changedRequest "reject buy cap below actual integer charge" funded buyA (Ref.Buy a 55 74067) (Just 0),
     changedRequest "reject buying above remaining real inventory" preComplete finalBuy (Ref.Buy a 26 300000) (Just 0),
     changedRequest "reject zero buy" funded buyA (Ref.Buy a 0 74068) (Just 0),
     changedRequest "reject sell minimum above actual net output" bought sellA (Ref.Sell a 25 42900) (Just 0),
     changedRequest "reject selling without voucher ownership" bought sellA (Ref.Sell b 25 42899) (Just 1),
     signedEdit "reject sell payout redirected to Bob" bought sellA (withOutput 1 (reroute 1)),
     signedEdit "reject sell fee redirected" bought sellA (withOutput 2 wrongScript),
     reject "reject transfer with wrong owner signature" both transferA id (Just 1) 0,
     earlyMigration,lateTrade,
     signedEdit "reject redirected migration liquidity" completed Ref.Migrate (withOutput 1 wrongScript),
     signedEdit "reject short migration liquidity" completed Ref.Migrate (withOutput 1 smaller),
     signedEdit "reject short migration fee" completed Ref.Migrate (withOutput 2 smaller),
     signedEdit "reject migrating away existing holder backing" completed Ref.Migrate (withOutput 0 smaller),
     reject "reject actual current input one" completed Ref.Migrate id Nothing 1,
     postMigration,
     vector "reject redemption before migration" holding holding (Ref.Redeem a 1) (Just 0)
       (construct completed 0 (Just 0) [stateOutput holding]) 0 Reject,
     changedRequest "reject redeeming more than the holder owns" transferred redeemA (Ref.Redeem a 51) (Just 0),
     signedEdit "reject redirected native voucher redemption" transferred redeemA (withOutput 1 (reroute 1)),
     signedEdit "reject final carrier redirected to buyer" onlyBob redeemB (withOutput 1 (reroute 1)),
     signedEdit "reject final redemption short by one sat" onlyBob redeemB (withOutput 0 smaller),
     signedEdit "reject preserving an extra state output after terminal redemption" onlyBob redeemB addOutput,
     changedRequest "reject a second sponsorship after funding" sold buyB Ref.Fund (Just Ref.sponsor)]
