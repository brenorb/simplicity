{-# LANGUAGE RankNTypes #-}
-- | Fully BTC-backed two-coupon constant-product pool and LP lifecycle.
module JetDiscovery.Corpus.UniswapV2Pool (entries,referenceAudit) where

import Prelude hiding (drop,take,not,and,or)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import Data.Serialize (runPut,runPutLazy,putWord64be)
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import Simplicity.Bitcoin.Term (Primitive,Simplicity,primitive)
import Simplicity.Digest (Hash256)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (or,verify)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Term.Core
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (checkSigWith,sigMsg)
import JetDiscovery.Corpus.ContractGrowth (add,allChecks,k,le,lt,nonzero,same,is,select,sub,scriptHash)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Lib.Bytes (failure,konst,w8,w32,w64,w256,w256FromBytes,w256ToBytes)
import JetDiscovery.Lib.State (loadState,stateScript,stateScriptHash,stateTap)
import JetDiscovery.Lib.V2PoolMath (mul,divide,minimumT,sqrt44)
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Bip
import qualified JetDiscovery.Ref.UniswapV2Pool as R

type Ledger = G.Ledger
type SigW = (Word256,Word256)
type Input = (Word8,((Ledger,Ledger),((Word64,Word64),(Word64,SigW))))

carrier, feeSats :: Integer
carrier = 1000
feeSats = 1000

stateTag :: String
stateTag = "JetDiscovery/UniswapV2Pool/State/V1"

secrets :: [Integer]
secrets = [6101,6102,6103]

recipient :: Int -> B.ByteString
recipient i = unhex "5120" <> Bip.bytesFromInt (Bip.pubkeyOf (secrets !! i))

digestRef :: Assert t => t Ledger Word256
digestRef = (((unit >>> ctx8InitTag stateTag) &&& oh >>> ctx8Add64) &&& ih >>> ctx8Add64) >>> ctx8Finalize

{-# NOINLINE digestWrapped #-}
digestWrapped :: J.WrappedSimplicity Ledger Word256
digestWrapped = J.jetSubst digestRef

digest :: Simplicity t => t Ledger Word256
digest = J.unwrap digestWrapped

stateBytes :: R.Ledger -> B.ByteString
stateBytes = Bip.taggedHash stateTag . runPut . mapM_ (putWord64be . fromInteger)

old, new :: Core t => t Input Ledger
old = drop (take oh)
new = drop (take ih)

o,n :: Core t => Int -> t Input Word64
o i = old >>> G.field i
n i = new >>> G.field i

actor, amount, aux :: Core t => t Input Word64
actor = drop (drop (take oh))
amount = drop (drop (take ih))
aux = drop (drop (drop oh))

sigWitness :: Core t => t Input SigW
sigWitness = drop (drop (drop ih))

sumT :: (Assert t,TyC a) => [t a Word64] -> t a Word64
sumT = L.foldl' add (k 0)

byActor :: (Assert t,TyC b) => [t Input b] -> t Input b
byActor fs = L.foldr (\(i,f) rest -> select (is actor (k i)) f rest) failure (zip [0..] fs)

ownerIndex :: Int -> Int -> Int
ownerIndex side i = 3+3*side+i

sourceBalance :: Assert t => Int -> t Input Word64
sourceBalance side = byActor [o (ownerIndex side i) | i <- [0..2]]

setBalance :: Assert t => Int -> t Input Word64 -> [(Int,t Input Word64)]
setBalance side v = [(j,select (is actor (k (toInteger i))) v (o j))
                    | i <- [0..2],let j=ownerIndex side i]

supplyT :: Assert t => (Int -> t Input Word64) -> t Input Word64
supplyT f = sumT (map f [9..12])

valid :: Assert t => (Int -> t Input Word64) -> t Input ()
valid f = allChecks [same (f 0) (add capA capB),le capA (k R.cap),le capB (k R.cap),
  le (supplyT f) (k (2^24-1)),le (f 13) (k 1),le (f 14) (k (R.cap*R.cap)),
  select (is (supplyT f) (k 0))
    (allChecks [same (f 1) (k 0),same (f 2) (k 0),same (f 14) (k 0)])
    (allChecks [nonzero (f 1),nonzero (f 2),same (f 12) (k R.minimumLiquidity)])]
 where
  capA = sumT (map f [1,3,4,5]); capB = sumT (map f [2,6,7,8])

change :: Assert t => [(Int,t Input Word64)] -> t Input ()
change patches = allChecks [same (n j) (maybe (o j) id (lookup j entries)) | j <- [0..15]]
 where entries = (15,add (o 15) (k 1)):patches

actualValue :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
actualValue i = konst (w32 i) >>> primitive P.InputValue >>> verify
outVal :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
outVal i = konst (w32 i) >>> primitive P.OutputValue >>> verify
outHash :: (Assert t,Primitive t,TyC a) => Integer -> t a Word256
outHash i = konst (w32 i) >>> primitive P.OutputScriptHash >>> verify
outCount :: (Assert t,Primitive t,TyC a) => Integer -> t a ()
outCount i = same (unit >>> Tx.numOutputs) (konst (w32 i))

funding :: (Assert t,Primitive t) => t Input Word64 -> t Input ()
funding x = same (actualValue 1) (add (k feeSats) x)

signatureCheck :: (Simplicity t,Primitive t) => t Input ()
signatureCheck = byActor [checkSigWith (w256 (Bip.pubkeyOf sk)) (unit >>> sigMsg) sigWitness | sk <- secrets]

protocolFee :: Simplicity t => t Input Word64
protocolFee = select (is (o 13) (k 1)) (select (is (o 14) (k 0)) (k 0) growth) (k 0)
 where
  root = mul (o 1) (o 2) >>> sqrt44
  prior = o 14 >>> sqrt44
  growth = select ((prior &&& root) >>> A.lt word64)
                  (divide (mul (supplyT o) (sub root prior)) (add (mul (k 5) root) prior)) (k 0)

kAfter :: Assert t => t Input Word64 -> t Input Word64 -> t Input Word64
kAfter x y = select (is (o 13) (k 1)) (mul x y) (k 0)

issue :: (Simplicity t,Primitive t) => Int -> t Input ()
issue side = allChecks [nonzero amount,same aux (k 0),outCount 1,funding amount,
  change ((0,add (o 0) amount):setBalance side (add (sourceBalance side) amount))]

redeem :: (Simplicity t,Primitive t) => Int -> t Input ()
redeem side = allChecks [nonzero amount,same aux (k 0),outCount 2,funding (k 0),
  konst (w32 (if side==0 then 800000 else 900000)) >>> TL.checkLockHeight,
  same (outVal 1) amount,
  same (outHash 1) (byActor [konst (scriptHash (recipient i)) | i<-[0..2]]),
  change ((0,sub (o 0) amount):setBalance side (sub (sourceBalance side) amount))]

mint :: (Simplicity t,Primitive t) => t Input ()
mint = allChecks [nonzero amount,nonzero aux,nonzero shares,outCount 1,funding (k 0),
  change ([(1,x),(2,y),(12,k R.minimumLiquidity),(14,kAfter x y)] ++
          setBalance 0 (sub (sourceBalance 0) amount) ++ setBalance 1 (sub (sourceBalance 1) aux) ++ lp)]
 where
  x=add (o 1) amount; y=add (o 2) aux
  adjustedSupply=add (supplyT o) protocolFee
  shares=select (is (supplyT o) (k 0)) (sub (mul amount aux >>> sqrt44) (k R.minimumLiquidity))
    (minimumT (divide (mul amount adjustedSupply) (o 1)) (divide (mul aux adjustedSupply) (o 2)))
  lp=[(i+9,select (is actor (k (toInteger i))) (add existing shares) existing)
      | i<-[0..2],let existing=if i==2 then add (o 11) protocolFee else o (i+9)]

burn :: (Simplicity t,Primitive t) => t Input ()
burn = allChecks [nonzero amount,same aux (k 0),le amount (byActor (map o [9..11])),
  nonzero a,nonzero b,outCount 1,funding (k 0),
  change ([(1,x),(2,y),(14,kAfter x y)] ++
    setBalance 0 (add (sourceBalance 0) a) ++ setBalance 1 (add (sourceBalance 1) b) ++ lp)]
 where
  adjustedSupply=add (supplyT o) protocolFee
  a=divide (mul amount (o 1)) adjustedSupply; b=divide (mul amount (o 2)) adjustedSupply
  x=sub (o 1) a; y=sub (o 2) b
  lp=[(i+9,select (is actor (k (toInteger i))) (sub existing amount) existing)
      | i<-[0..2],let existing=if i==2 then add (o 11) protocolFee else o (i+9)]

swap :: (Simplicity t,Primitive t) => Int -> t Input ()
swap side = allChecks [nonzero amount,nonzero aux,nonzero (o rin),lt aux (o rout),
  le (mul (mul (o 1) (o 2)) (k 1000000))
     (mul (sub (mul x (k 1000)) (mul amount (k 3))) (mul y (k 1000))),
  outCount 1,funding (k 0),
  change ([(rin,x),(rout,y)] ++ setBalance side (sub (sourceBalance side) amount) ++
                              setBalance (1-side) (add (sourceBalance (1-side)) aux))]
 where
  rin=1+side; rout=2-side
  x=add (o rin) amount; y=sub (o rout) aux

kernel :: (Simplicity t,Primitive t) => t Input ()
kernel = allChecks [valid o,valid n,signatureCheck,
  same (unit >>> primitive P.CurrentIndex) (konst (w32 0)),
  same (unit >>> Tx.numInputs) (konst (w32 2)),
  same (unit >>> Tx.currentValue) (add (o 0) (k carrier)),
  loadState (old >>> digest),
  same (konst (w32 0) >>> primitive P.InputScriptHash >>> verify) (stateScriptHash (old >>> digest)),
  same (outVal 0) (add (n 0) (k carrier)),same (outHash 0) (stateScriptHash (new >>> digest)),
  L.foldr (\(i,x) rest -> select (is oh (konst (w8 i))) x rest) failure (zip [0..] branches)]
 where
  feeMode = allChecks [same actor (k 2),same aux (k 0),le amount (k 1),outCount 1,funding (k 0),change [(13,amount)]]
  branches = [issue 0,issue 1,redeem 0,redeem 1,feeMode,mint,burn,swap 0,swap 1]

program :: Input -> Prog
program = boundProgram kernel

cmr :: Hash256
cmr = progCmr (program (w8 0,((G.ledger [],G.ledger []),((w64 0,w64 0),(w64 0,(w256 0,w256 0))))))

type Setup = (R.Ledger,D.Outpoint)

encodeAction :: R.Action -> (Integer,Integer,Integer,Integer)
encodeAction a = case a of
  R.Issue side who qty -> (toInteger side,toInteger who,qty,0)
  R.Redeem side who qty -> (toInteger (2+side),toInteger who,qty,0)
  R.SetFee flag -> (4,2,if flag then 1 else 0,0)
  R.Mint who x y -> (5,toInteger who,x,y)
  R.Burn who shares -> (6,toInteger who,shares,0)
  R.Swap side who qty out -> (toInteger (7+side),toInteger who,qty,out)

stateOutput :: R.Ledger -> D.TxOutput
stateOutput ls = mkOutput (fromInteger (carrier+head ls)) (stateScript cmr (stateBytes ls))

buildTx :: Setup -> R.Ledger -> Integer -> Maybe (Int,Integer) -> Integer -> D.SigTx
buildTx (oldState,op@(D.Outpoint h _)) next cash payout lock = mkTx 2
  [mkInput op (D.txoValue (stateOutput oldState)) (D.txoScript (stateOutput oldState)) 0xfffffffe,
   mkInput (D.Outpoint (sha256 (hashToBytes h)) 1) (fromInteger (feeSats+cash)) (BL.fromStrict (recipient 2)) 0xfffffffe]
  (stateOutput next : [mkOutput (fromInteger amt) (recipient to) | (to,amt)<-maybe [] (:[]) payout]) (fromInteger lock)

nextSetup :: Setup -> R.Action -> Setup
nextSetup s@(oldState,_) action = (next,D.Outpoint (sha256 (hashToBytes (sha256 wire))) 0)
 where
  Just (next,cash,pay) = R.step oldState action
  wire = BL.toStrict (runPutLazy (D.putNoWitnessTx (buildTx s next cash pay 900000)))

makeVector :: String -> Expect -> Setup -> R.Ledger -> R.Ledger -> R.Action -> Integer -> D.SigTx -> Maybe Int -> Vector Input
makeVector name expected (actualOld,_) oldState next action index tx signerOverride = Vector name env witnessValue expected
 where
  env = mkEnv tx (fromInteger index) (\root -> stateTap root (stateBytes actualOld))
  (op,who,qty,other) = encodeAction action
  whoSigns = maybe (fromInteger who) id signerOverride
  signatureBytes = case env cmr >>= \e -> J.fastEval sigMsg e () of
    Just msg -> Bip.sign (secrets !! whoSigns) (w256ToBytes msg) (B.replicate 32 0)
    _ -> error "V2 fixture environment"
  sigPair = (w256FromBytes (B.take 32 signatureBytes), w256FromBytes (B.drop 32 signatureBytes))
  witnessValue = (w8 op,((G.ledger oldState,G.ledger next),((w64 who,w64 qty),(w64 other,sigPair))))

positive :: String -> Setup -> R.Action -> Vector Input
positive name s@(oldState,_) action = makeVector name Accept s oldState next action 0 (buildTx s next cash pay 900000) Nothing
 where Just (next,cash,pay) = R.step oldState action

start, d1, d2, d3, d4, feeOn, started, swapped, diluted, reversed, partial, feeBurn, disabled, reset :: Setup
start = (R.initial,dummyOutpoint 0)
d1 = nextSetup start (R.Issue 0 0 300000)
d2 = nextSetup d1 (R.Issue 1 0 300000)
d3 = nextSetup d2 (R.Issue 0 1 100000)
d4 = nextSetup d3 (R.Issue 1 1 160000)
feeOn = nextSetup d4 (R.SetFee True)
started = nextSetup feeOn (R.Mint 0 100000 100000)
swapForward, swapBack :: R.Action
swapForward = R.Swap 0 1 50000 (R.quote (fst started) 0 50000)
swapped = nextSetup started swapForward
diluted = nextSetup swapped (R.Mint 1 15000 6673)
swapBack = R.Swap 1 0 50000 (R.quote (fst diluted) 1 50000)
reversed = nextSetup diluted swapBack
partial = nextSetup reversed (R.Burn 1 3000)
feeBurn = nextSetup partial (R.Burn 2 4)
disabled = nextSetup feeBurn (R.SetFee False)
reset = nextSetup disabled (R.Burn 0 1000)

referenceAudit :: Bool
referenceAudit = andH [R.protocolMint (fst swapped)>0, fst diluted!!11==R.protocolMint(fst swapped),
  fst started!!12==1000, fst started!!9==99000, fst disabled!!14==fst feeBurn!!14,
  fst reset!!14==0, fst feeBurn!!11<fst partial!!11+R.protocolMint(fst partial),
  R.step (fst started) (R.Swap 0 1 50000 (R.quote(fst started) 0 50000+1))==Nothing]
 where andH = L.foldl' (&&) True

positives :: [Vector Input]
positives = [positive "actual A receipt funds first LP" start (R.Issue 0 0 300000),
  positive "actual B receipt funds first LP" d1 (R.Issue 1 0 300000),
  positive "second account funds A" d2 (R.Issue 0 1 100000),
  positive "second account funds B" d3 (R.Issue 1 1 160000),
  positive "fee setter enables fixed protocol recipient" d4 (R.SetFee True),
  positive "first mint locks exactly 1000 LP" feeOn (R.Mint 0 100000 100000),
  positive "A to B at fee-adjusted limit" started swapForward,
  positive "unbalanced add mints source floor and dilutes to fee recipient" swapped (R.Mint 1 15000 6673),
  positive "reverse B to A fee-adjusted swap" diluted swapBack,
  positive "partial burn returns both assets with fee-on dilution" reversed (R.Burn 1 3000),
  positive "fee recipient burns previously minted LP" partial (R.Burn 2 4),
  positive "disable fee without prematurely resetting kLast" feeBurn (R.SetFee False),
  positive "fee-off burn resets kLast" disabled (R.Burn 0 1000),
  positive "holder burns all remaining LP while minimum stays locked" reset (R.Burn 0 (fst reset!!9)),
  positive "burned-pool coupons can pay exact native A output" reset (R.Redeem 0 0 2000),
  positive "B coupon native payout at its maturity" reset (R.Redeem 1 0 3000)]

negatives :: [Vector Input]
negatives =
  [ bad "first mint cannot unlock minimum liquidity" feeOn (R.Mint 0 100000 100000)
      (R.replace (fst started) [(12,999),(9,99001)])
  , bad "one extra sat of swap output violates adjusted K" started excessive
      (R.replace (fst swapped) [(2,fst swapped!!2-1),(7,fst swapped!!7+1)])
  , bad "swap does not update kLast" started swapForward (R.replace (fst swapped) [(14,fst swapped!!1*fst swapped!!2)])
  , bad "fee-on mint cannot omit protocol dilution" swapped (R.Mint 1 15000 6673)
      (R.replace (fst diluted) [(11,0)])
  , bad "fee-on mint cannot round LP up" swapped (R.Mint 1 15000 6673)
      (R.replace (fst diluted) [(10,fst diluted!!10+1)])
  , bad "fee setter alone cannot reset kLast" feeBurn (R.SetFee False) (R.replace (fst disabled) [(14,0)])
  , bad "fee-off burn must clear stale kLast" disabled (R.Burn 0 1000)
      (R.replace (fst reset) [(14,fst disabled!!14)])
  , bad "holder cannot burn any locked LP" reset (R.Burn 0 (fst reset!!9+1)) (fst reset)
  , bad "user cannot spend another account's unowned A" started (R.Swap 0 1 100001 1) (fst swapped)
  , makeVector "issue needs exact actual input funding" Reject start R.initial (fst d1)
      (R.Issue 0 0 300000) 0 (buildTx start (fst d1) 299999 Nothing 900000) Nothing
  , makeVector "wrong actual fee-setting signer" Reject d4 (fst d4) (fst feeOn)
      (R.SetFee True) 0 (buildTx d4 (fst feeOn) 0 Nothing 900000) (Just 0)
  , makeVector "wrong actual continuation despite correct transition witness" Reject swapped (fst swapped) (fst diluted)
      (R.Mint 1 15000 6673) 0 (buildTx swapped (fst swapped) 0 Nothing 900000) Nothing
  , makeVector "actual old state cannot be swapped for claimed ledger" Reject reset (fst disabled) redeemed
      redemption 0 (buildTx reset redeemed cash payout 900000) Nothing
  , makeVector "B maturity height cannot be skipped" Reject reset (fst reset) redeemed
      redemption 0 (buildTx reset redeemed cash payout 899999) Nothing
  , makeVector "re-signed coupon withdrawal cannot redirect payee" Reject reset (fst reset) redeemed
      redemption 0 (buildTx reset redeemed cash (Just (1,3000)) 900000) Nothing
  , makeVector "same transaction cannot authorize a fee input as the state" Reject reset (fst reset) redeemed
      redemption 1 (buildTx reset redeemed cash payout 900000) Nothing
  ]
 where
  bad name s lsAction ns = makeVector name Reject s (fst s) ns lsAction 0 (buildTx s ns 0 Nothing 900000) Nothing
  excessive = R.Swap 0 1 50000 (R.quote (fst started) 0 50000 + 1)
  redemption = R.Redeem 1 0 3000
  Just (redeemed,cash,payout)=R.step (fst reset) redemption

entries :: [Entry]
entries = [Entry "app-uniswap-v2-fee-on-pool" "Native Uniswap V2 pool with exact LP fee minting and coupon payouts"
  "Uniswap v2-core 6a9e7c97860676e0992f22a49665760444c1cdf5 Pair mint/burn/swap/_mintFee and Math.sqrt"
  CrossChain (Derived "independent Integer source relations; exact native funding, signed transitions and payouts, ancestry and adversarial state controls")
  ["two BTC-backed maturity classes, two ordinary owners and fixed fee recipient/admin, each asset supply at most 2^22-1; fully collateralized native coupon and LP accounting",
   "exact 1000 locked initial LP, source floor mint/burn and protocol sqrt(k) dilution, both exact adjusted-K single-input swap directions, signed fee enable/disable and kLast reset at mint/burn",
   "actual current input 0 script/value, exactly one extra fee/funding input, preserved 1000-sat setup carrier, exact successor and actual maturity-bound redemption",
   "one initialized pool lineage; no global foreign tokens, flash callbacks, timestamp price accumulator, fee-on-transfer tokens, skim or sync"] program (positives++negatives)]
