{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | Fixed-scale TwoCrypto pool with real BTC-backed coupon and LP ownership.
module JetDiscovery.Corpus.TwoCrypto (entry,poolCmr) where

import Prelude hiding (drop,not,take)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.Vector as V
import qualified Data.Word as DW
import Data.Serialize (runPutLazy)
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import Simplicity.Digest (Hash256)
import Simplicity.Programs.Bit (not,verify)
import Simplicity.Term.Core
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Corpus.Baseline (signMsg)
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Lib.Bytes (failure,konst,w16,w32,w256ToBytes)
import qualified JetDiscovery.Lib.ClaimLedger as L
import JetDiscovery.Lib.State (stateScript,stateScriptHash,stateTap)
import JetDiscovery.Lib.TwoCryptoArithmetic
import qualified JetDiscovery.Lib.TwoCryptoPool as T
import qualified JetDiscovery.Ref.Bip340 as Bip
import qualified JetDiscovery.Ref.TwoCrypto as R
import qualified JetDiscovery.Ref.TwoCryptoLedger as Ref
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

type Kernel t = t L.Input ()
type Quoted a = (L.Input,(T.Pool,a))

holderFields :: Int -> (Int,Int)
holderFields 0 = (3,4)
holderFields 1 = (5,6)
holderFields _ = error "TwoCrypto coupon index"

forOwner :: (Assert t,TyC a,TyC b) => t a Word64 -> t a b -> t a b -> t a b
forOwner actor = select (equal actor (word 0))

changeHolder :: (Assert t,TyC a) => (Int -> t a Word64) -> t a Word64
             -> (Int,Int) -> t a Word64 -> [(Int,t a Word64)]
changeHolder old who (alice,bob) value =
  [(alice,forOwner who value (old alice)),(bob,forOwner who (old bob) value)]

holderBalance :: (Assert t,TyC a) => (Int -> t a Word64) -> t a Word64
              -> (Int,Int) -> t a Word64
holderBalance old who (alice,bob) = forOwner who (old alice) (old bob)

validLedger :: Assert t => t L.Ledger ()
validLedger = checks
  [ same (f 0) (add (f 1) (f 2))
  , le (f 0) (word Ref.maxCollateral)
  , same (f 1) (sumFields [3,4,7,9])
  , same (f 2) (sumFields [5,6,8,10])
  , same (f 11) (add (f 12) (f 13))
  , le (f 11) (word (8*R.wad))
  , le (word R.wad) (f 16),le (f 16) (word (2*R.wad))
  , le (word R.wad) (f 18),le (f 18) (f 17),le (f 17) (word (4*R.wad))
  , le (f 19) (word (8*R.wad))
  , select (equal (f 11) (word 0)) (checks [same (f i) (word 0) | i<-[7,8,15]])
      (checks (le (word (10^17)) (f 15):le (f 15) (word (8*R.wad)):
        [bound i | i<-[7,8]]))
  , checks [same (f i) (word 0) | i<-[20..31]]
  ]
 where
  f = L.field
  sumFields xs = L.sumT (map f xs)
  bound i = checks [le (word R.minReserve) (f i),le (f i) (word R.maxReserve)]

sourcePool :: Core t => t L.Input T.Pool
sourcePool = T.assemble (L.o 7&&&L.o 8) (L.o 15) (L.o 11)
  (L.o 16) (L.o 17) (L.o 18) (L.o 19)

updatedPool :: (Core t,TyC a) => [(Int,t (Quoted a) Word64)]
updatedPool =
  [(7,p>>>T.balances>>>oh),(8,p>>>T.balances>>>ih),(15,p>>>T.invariantD),
   (11,p>>>T.supply),(16,p>>>T.virtualPrice),(17,p>>>T.profit),
   (18,p>>>T.profitAnchor),(19,p>>>T.adminCredit)]
 where p = ioh

verifyQuote :: (Assert t,TyC a) => [(Int,t (Quoted a) Word64)] -> t (Quoted a) ()
verifyQuote extra = checks [same (take (L.n i)) (maybe (take (L.o i)) id (lookup i writes)) | i<-[0..31]]
 where writes = (14,add (take (L.o 14)) (word 1)):updatedPool++extra

p2tr :: Int -> BS.ByteString
p2tr i = unhex "5120" <> Bip.bytesFromInt (Bip.pubkeyOf (G.keys !! i))

destination :: (Core t,TyC a) => Int -> t a Word256
destination = konst . G.scriptHash . p2tr

actualInputScript :: (Assert t,Primitive t,TyC a) => t a Word256
actualInputScript = konst (w32 0)>>>primitive P.InputScriptHash>>>verify

distinctInputs :: (Assert t,Primitive t,TyC a) => t a ()
distinctInputs = not (equal (at 0) (at 1))>>>verify
 where at i = konst (w32 i)>>>primitive P.InputPrevOutpoint>>>verify

claimAction :: (Simplicity t,Primitive t) => Int -> Int -> Kernel t
claimAction coin mode = checks [L.actorSig,positive L.amount,action]
 where
  who = L.actor
  qty = L.amount
  old = L.o
  fields@(alice,bob) = holderFields coin
  supply = 1+coin
  balance = holderBalance old who fields
  nonce = (14,add (old 14) (word 1))
  change = changeHolder old who fields
  height = Ref.maturity (if coin==0 then Ref.X else Ref.Y)
  action = case mode of
    0 -> checks [L.changes ([(0,add (old 0) qty),(supply,add (old supply) qty),nonce]++
                             change (add balance qty)),L.deposit qty]
    1 -> checks [L.changes [nonce,
          (alice,forOwner who (sub (old alice) qty) (add (old alice) qty)),
          (bob,forOwner who (add (old bob) qty) (sub (old bob) qty))],L.noCash]
    2 -> checks [konst (w32 height)>>>TL.checkLockHeight,
          L.changes ([(0,sub (old 0) qty),(supply,sub (old supply) qty),nonce]++
                     change (sub balance qty)),L.withdraw qty (forOwner who (destination 0) (destination 1))]
    _ -> failure

joinAction :: (Simplicity t,Primitive t) => Kernel t
joinAction = checked L.actorSig (iden&&&((sourcePool&&&(L.aux 0&&&L.aux 1))>>>T.joinPool))>>>
  checks [le (take (L.aux 2)) iih,verifyQuote (couponUpdates++lpUpdate),take L.noCash]
 where
  old = take . L.o
  who = take L.actor
  couponUpdates = concat
    [let fields=holderFields i in changeHolder old who fields
       (sub (holderBalance old who fields) (take (L.aux i))) | i<-[0,1]]
  lpUpdate = changeHolder old who (12,13) (add (holderBalance old who (12,13)) iih)

swapAction :: (Simplicity t,Primitive t) => Kernel t
swapAction = checked (checks [L.actorSig,le (L.aux 0) (word 1)])
  (iden&&&((sourcePool&&&(equal (L.aux 0) (word 1)&&&L.amount))>>>T.swapPool))>>>
  checks [le (take (L.aux 1)) iih,verifyQuote couponUpdates,take L.noCash]
 where
  old = take . L.o
  who = take L.actor
  couponUpdates = concat
    [let fields=holderFields i
         balance=holderBalance old who fields
         value=select (equal (take (L.aux 0)) (word (toInteger i)))
           (sub balance (take L.amount)) (add balance iih)
     in changeHolder old who fields value | i<-[0,1]]

exitAction :: (Simplicity t,Primitive t) => Kernel t
exitAction = checked L.actorSig (iden&&&((sourcePool&&&L.amount)>>>T.exitPool))>>>
  checks [le (take (L.aux 0)) (iih>>>oh),le (take (L.aux 1)) (iih>>>ih),
          verifyQuote (couponUpdates++lpUpdate),take L.noCash]
 where
  old = take . L.o
  who = take L.actor
  couponUpdates = concat
    [let fields=holderFields i in changeHolder old who fields
       (add (holderBalance old who fields) result) | (i,result)<-[(0,iih>>>oh),(1,iih>>>ih)]]
  lpUpdate = changeHolder old who (12,13) (sub (holderBalance old who (12,13)) (take L.amount))

lpMove :: (Simplicity t,Primitive t) => Kernel t
lpMove = checks [L.actorSig,positive L.amount,L.changes
  [(14,add (L.o 14) (word 1)),
   (12,forOwner L.actor (sub (L.o 12) L.amount) (add (L.o 12) L.amount)),
   (13,forOwner L.actor (add (L.o 13) L.amount) (sub (L.o 13) L.amount))],L.noCash]

adminSweep :: (Simplicity t,Primitive t) => Kernel t
adminSweep = checked (checks [L.sigAt 3 0,konst (w16 169)>>>TL.checkLockDuration])
  (iden&&&(sourcePool>>>T.sweepPool))>>>
  checks [verifyQuote [(9,add (take (L.o 9)) (iih>>>oh)),(10,add (take (L.o 10)) (iih>>>ih))],take L.noCash]

feeRedeem :: (Simplicity t,Primitive t) => Int -> Kernel t
feeRedeem coin = checks
  [ L.sigAt 3 0,positive L.amount,konst (w32 maturity)>>>TL.checkLockHeight
  , L.changes [(14,add (L.o 14) (word 1)),(0,debit 0),(1+coin,debit (1+coin)),(9+coin,debit (9+coin))]
  , L.withdraw L.amount (destination 3)
  ]
 where
  maturity = Ref.maturity (if coin==0 then Ref.X else Ref.Y)
  debit i = sub (L.o i) L.amount

kernel :: forall t. (Simplicity t,Primitive t) => Kernel t
kernel = checks
  [ L.base,distinctInputs,same actualInputScript (stateScriptHash (L.old>>>L.stateHash))
  , L.old>>>validLedger,L.new>>>validLedger
  , L.choose ([(toInteger n,claimAction (n `mod` 2) (n `div` 2)) | n<-[0..5]]++
      [(6,joinAction),(7,swapAction),(8,exitAction),(9,lpMove),(10,adminSweep),
       (11,feeRedeem 0),(12,feeRedeem 1)])
  ]

program :: L.CW -> Prog
program = boundProgram kernel . L.encode

poolCmr :: Hash256
poolCmr = progCmr (program (L.CW 0 (Ref.ledger Ref.setup) (Ref.ledger Ref.setup) 0 0 [] []))

entry :: Entry
entry = Entry "app-cryptoswap-transition" "Fixed-scale TwoCrypto pool with native funded coupon and LP ownership"
  "Curve TwoCrypto NG 5cbe558902402e8fcb331463089db65fc56c11f9, proven Newton fallback and fixed scale profile"
  CrossChain (Derived "independent pinned Integer arithmetic, funded Bitcoin UTXO history, authenticated exact state and payouts")
  [ "two 1-sat-backed coupon assets, two fixed owners and fixed admin, carrier10000 sats and fee1000 sats"
  , "ANN4000000, gamma199e15, price scale1e18, equal precision10^12, dynamic fees30000000/50000000 and fee gamma10^16"
  , "get_y uses source Newton fallback proven at 45*D<=100*x_j<=55*D, K0_prev=0, at most12 checked iterations"
  , "initial and fee-bearing LP join, both swaps, LP transfer, partial/full proportional exit, source admin fee accrual and settlement, matured coupon redemption"
  , "fixed-scale guard makes the source rebalance condition false, exact virtual price/profit persisted, unused EMA/spot state projected out"
  , "native admin trigger uses169 BIP68 time units; current input0 and both old/new exact scripts and BTC amounts"
  ] program vectors

type Coin = (Ref.State,D.Outpoint)
type Request = (Integer,Integer,Integer,[Integer])

request :: Ref.Action -> Request
request action = case action of
  Ref.Issue who asset qty -> coupon 0 who asset qty
  Ref.Transfer who asset qty -> coupon 2 who asset qty
  Ref.Redeem who asset qty -> coupon 4 who asset qty
  Ref.Join who (a,b) -> (6,index who,0,[a,b,1])
  Ref.Swap who asset qty -> (7,index who,qty,[index asset,1])
  Ref.Exit who qty -> (8,index who,qty,[0,0])
  Ref.MoveLp who qty -> (9,index who,qty,[])
  Ref.Sweep -> (10,0,0,[])
  Ref.RedeemFee asset qty -> (11+index asset,0,qty,[])
 where
  index :: Enum a => a -> Integer
  index = toInteger . fromEnum
  coupon mode who asset qty = (mode+index asset,index who,qty,[])

stateBytes :: Ref.State -> BS.ByteString
stateBytes = L.stateRef . Ref.ledger

stateOutput :: Ref.State -> D.TxOutput
stateOutput s = mkOutput (fromInteger (head (Ref.ledger s)+Ref.carrier))
  (stateScript poolCmr (stateBytes s))

maturityFor :: Ref.Action -> DW.Word32
maturityFor (Ref.Redeem _ asset _) = fromInteger (Ref.maturity asset)
maturityFor (Ref.RedeemFee asset _) = fromInteger (Ref.maturity asset)
maturityFor _ = 0

sequenceFor :: Ref.Action -> DW.Word32
sequenceFor Ref.Sweep = 0x00400000+169
sequenceFor _ = 0xfffffffe

txFor :: Coin -> Integer -> [D.TxOutput] -> DW.Word32 -> DW.Word32 -> D.SigTx
txFor (old,prev@(D.Outpoint h _)) funded outs lock sq =
  mkTx 2
    [mkInput prev (fromInteger (head (Ref.ledger old)+Ref.carrier))
       (BL.fromStrict (stateScript poolCmr (stateBytes old))) sq,
     mkInput (D.Outpoint (sha256 (hashToBytes h)) 1) (fromInteger (funded+Ref.fee))
       (BL.fromStrict (p2tr 2)) 0xfffffffe]
    outs lock

transaction :: Coin -> Ref.Action -> (D.SigTx,Ref.State)
transaction coin@(old,_) action =
  (txFor coin (Ref.funded result) outputs (maturityFor action) (sequenceFor action),next)
 where
  result = maybe (error ("bad TwoCrypto fixture "++show action)) id (Ref.transition old action)
  next = Ref.next result
  outputs = stateOutput next:[mkOutput (fromInteger n) (p2tr who) |
     (who,n)<-maybe [] pure (Ref.payout result)]

initial :: Coin
initial = (Ref.setup,dummyOutpoint 2980)

advance :: Coin -> Ref.Action -> Coin
advance coin action = (next,D.Outpoint (sha256 (hashToBytes (sha256 wire))) 0)
 where
  (tx,next) = transaction coin action
  wire = BL.toStrict (runPutLazy (D.putNoWitnessTx tx))

{-# NOINLINE sigAllWrapped #-}
sigAllWrapped :: J.WrappedSimplicity () Word256
sigAllWrapped = J.jetSubst sigMsg

signed :: Ref.State -> [Integer] -> [Integer] -> Request -> Int -> D.SigTx -> L.CW
signed = signedAt 0

signedAt :: DW.Word32 -> Ref.State -> [Integer] -> [Integer] -> Request -> Int -> D.SigTx -> L.CW
signedAt ix actual old next (mode,who,qty,aux) signer tx = L.CW mode old next who qty aux [signature]
 where
  signature = case mkEnv tx ix (\leaf -> stateTap leaf (stateBytes actual)) poolCmr
                   >>= \env -> J.fastEval (J.unwrap sigAllWrapped) env () of
    Just digest -> G.sigW (signMsg (G.keys !! signer) (w256ToBytes digest))
    Nothing -> error "TwoCrypto signature environment"

vector :: String -> Ref.State -> L.CW -> D.SigTx -> DW.Word32 -> Expect -> Vector L.CW
vector label actual proof tx ix =
  Vector label (mkEnv tx ix (\leaf -> stateTap leaf (stateBytes actual))) proof

positiveVector :: String -> Coin -> Ref.Action -> Vector L.CW
positiveVector label coin@(old,_) action =
  vector label old (signed old (Ref.ledger old) (Ref.ledger next) (request action) (Ref.signer action) tx) tx 0 Accept
 where (tx,next) = transaction coin action

changeWords :: [(Int,Integer)] -> [Integer] -> [Integer]
changeWords changes xs = [x+maybe 0 id (lookup i changes) | (i,x)<-zip [0..] xs]

changeRequest :: (Request -> Request) -> L.CW -> L.CW
changeRequest f cw = cw {L.cwMode=mode,L.cwActor=who,L.cwAmount=qty,L.cwAux=aux}
 where
  (mode,who,qty,aux) = f (L.cwMode cw,L.cwActor cw,L.cwAmount cw,L.cwAux cw)

withInput :: Int -> (D.SigTxInput -> D.SigTxInput) -> D.SigTx -> D.SigTx
withInput ix f tx = tx {D.sigTxIn=D.sigTxIn tx V.// [(ix,f (D.sigTxIn tx V.! ix))]}

withOutput :: Int -> (D.TxOutput -> D.TxOutput) -> D.SigTx -> D.SigTx
withOutput ix f tx = tx {D.sigTxOut=D.sigTxOut tx V.// [(ix,f (D.sigTxOut tx V.! ix))]}

editPositive :: String -> Coin -> Ref.Action -> (L.CW -> L.CW) -> (D.SigTx -> D.SigTx) -> Int -> DW.Word32 -> Vector L.CW
editPositive label coin@(old,_) action edit editTx signer ix = vector label old proof tx ix Reject
 where
  (original,next) = transaction coin action
  raw = Ref.ledger next
  opened = edit (L.CW mode (Ref.ledger old) raw who qty aux [])
  (mode,who,qty,aux) = request action
  adjusted = if L.cwNew opened==raw then original else withOutput 0
    (\o -> o {D.txoScript=BL.fromStrict (stateScript poolCmr (L.stateRef (L.cwNew opened)))}) original
  tx = editTx adjusted
  proof = signedAt ix old (L.cwOld opened) (L.cwNew opened)
    (L.cwMode opened,L.cwActor opened,L.cwAmount opened,L.cwAux opened) signer tx

invalid :: String -> Coin -> Ref.Action -> Vector L.CW
invalid label coin@(old,_) action = case Ref.transition old action of
  Just _ -> error ("TwoCrypto rejection fixture is valid "++show action)
  Nothing -> vector label old proof tx 0 Reject
 where
  stale = old {Ref.nonce=Ref.nonce old+1}
  tx = txFor coin 0 [stateOutput stale] (maturityFor action) (sequenceFor action)
  proof = signed old (Ref.ledger old) (Ref.ledger stale) (request action) (Ref.signer action) tx

vectors :: [Vector L.CW]
vectors = issued ++ poolHistory ++ redemptions ++ branches ++ negatives
 where
  alice = Ref.Alice
  bob = Ref.Bob
  x = Ref.X
  y = Ref.Y
  issueSteps =
    [("Alice funds X coupons with Bitcoin",Ref.Issue alice x 1400000),
     ("Alice funds Y coupons with Bitcoin",Ref.Issue alice y 1400000),
     ("Bob funds X coupons with Bitcoin",Ref.Issue bob x 400000),
     ("Bob funds Y coupons with Bitcoin",Ref.Issue bob y 400000)]
  issuedCoins = scanl advance initial (map snd issueSteps)
  issued = [positiveVector label coin action | (coin,(label,action))<-zip issuedCoins issueSteps]
  funded = last issuedCoins
  join0 = Ref.Join alice (1000000,1000000)
  join1 = Ref.Join bob (10000,0)
  swapX = Ref.Swap alice x 10000
  swapY = Ref.Swap bob y 10000
  lpMove = Ref.MoveLp alice (div R.wad 20)
  burn = Ref.Exit alice (div R.wad 10)
  initialized = advance funded join0
  poolSteps =
    [("two-sided initial geometric-mean LP mint",join0),
     ("one-sided join charges source LP fee",join1),
     ("Alice swaps X for Y",swapX),
     ("Bob swaps Y for X",swapY),
     ("Alice transfers funded LP ownership",lpMove),
     ("Alice partially burns LP with the source one-unit rounding",burn),
     ("administrator settles source fee share after actual BIP68 delay",Ref.Sweep)]
  poolCoins = scanl advance funded (map snd poolSteps)
  poolHistory = [positiveVector label coin action | (coin,(label,action))<-zip poolCoins poolSteps]
  beforeSweep = poolCoins !! (length poolSteps-1)
  settled = last poolCoins
  (feeX,feeY) = Ref.administrator (fst settled)
  redemptionSteps =
    [("administrator redeems earned X coupons",Ref.RedeemFee x feeX),
     ("administrator redeems earned Y coupons",Ref.RedeemFee y feeY),
     ("Bob transfers X coupons to Alice",Ref.Transfer bob x 2000),
     ("Alice redeems X coupons into her exact Bitcoin script",Ref.Redeem alice x 7000),
     ("Bob redeems Y coupons into his exact Bitcoin script",Ref.Redeem bob y 5000)]
  redeemedCoins = scanl advance settled (map snd redemptionSteps)
  redemptions = [positiveVector label coin action | (coin,(label,action))<-zip redeemedCoins redemptionSteps]
  redemption = Ref.Redeem alice x 7000
  partial = Ref.Exit alice (div R.wad 10)
  branches =
    [positiveVector "balanced full LP burn empties reserves and invariant" initialized (Ref.Exit alice R.wad),
     positiveVector "balanced partial burn yields 99999 sat coupons per asset" initialized partial,
     positiveVector "exact upper fallback boundary at 55 percent" initialized (Ref.Swap alice x 100000),
     sameStateInputs "accept current input 0 with both input scripts equal" 0 Accept]
  edit label coin action cw tx = editPositive label coin action cw tx (Ref.signer action) 0
  changeNext xs cw = cw {L.cwNew=changeWords xs (L.cwNew cw)}
  changeOld xs cw = cw {L.cwOld=changeWords xs (L.cwOld cw)}
  setAux aux = changeRequest (\(m,a,n,_) -> (m,a,n,aux))
  smallerInput x0 = x0 {D.sigTxiTxo=smaller (D.sigTxiTxo x0)}
  smaller o = o {D.txoValue=D.txoValue o-1}
  wrongScript o = o {D.txoScript=BL.fromStrict (p2tr 2)}
  setSeq sq i = i {D.sigTxiSequence=sq}
  duplicate tx = withInput 1 (\i -> i {D.sigTxiPreviousOutpoint=D.sigTxiPreviousOutpoint (D.sigTxIn tx V.! 0)}) tx
  sameStateInputs label ix expectation = vector label Ref.setup proof tx ix expectation
   where
    action = Ref.Issue alice x (Ref.carrier-Ref.fee)
    (original,next) = transaction initial action
    tx = withInput 1 (\i -> i {D.sigTxiTxo=D.sigTxiTxo (D.sigTxIn original V.! 0)}) original
    proof = signedAt ix Ref.setup (Ref.ledger Ref.setup) (Ref.ledger next) (request action) 0 tx
  negatives =
    [edit "reject input funded one sat too little" initial (snd (head issueSteps)) id (withInput 1 smallerInput),
     edit "reject wrong current state input amount" initialized swapX id (withInput 0 smallerInput),
     edit "reject wrong real current script" initialized swapX id
       (withInput 0 (\i -> i {D.sigTxiTxo=wrongScript (D.sigTxiTxo i)})),
     edit "reject repeated input prevout" initialized swapX id duplicate,
     edit "reject stale old invariant opening" initialized swapX (changeOld [(15,1)]) id,
     edit "reject wrong continuation script with valid actor signature" initialized swapX id (withOutput 0 wrongScript),
     edit "reject wrong continuation backing" initialized swapX id (withOutput 0 smaller),
     edit "reject optimistic output even when coupon supply balances" initialized swapX
       (changeNext [(5,1),(8,-1)]) id,
     edit "reject stored invariant one unit off" initialized swapX (changeNext [(15,1)]) id,
     edit "reject stale virtual-price/profit accounting" initialized swapX (changeNext [(16,-1),(17,-1)]) id,
     edit "reject swap minimum exceeds actual output" initialized swapX (setAux [0,10000]) id,
     invalid "reject one unit beyond upper fallback boundary" initialized (Ref.Swap alice x 100001),
     invalid "reject zero swap" initialized (Ref.Swap alice x 0),
     invalid "reject one-sided initial join" funded (Ref.Join alice (1000000,0)),
     invalid "reject unaffordable coupon join" initialized (Ref.Join bob (400001,0)),
     edit "reject inflated join LP even when holder supply agrees" initialized join1 (changeNext [(11,1),(13,1)]) id,
     edit "reject join minimum exceeds actual mint" initialized join1 (setAux [10000,0,R.wad]) id,
     edit "reject treating partial burn as exact rather than amount-minus-one" initialized partial
       (changeNext [(3,1),(5,1),(7,-1),(8,-1)]) id,
     edit "reject partial burn minimum based on optimistic rounding" initialized partial (setAux [100000,100000]) id,
     invalid "reject Bob burning Alice's LP" initialized (Ref.Exit bob (div R.wad 10)),
     invalid "reject Bob transferring absent LP" initialized (Ref.MoveLp bob 1),
     editPositive "reject unauthorized LP transfer" initialized lpMove id id 1 0,
     editPositive "reject non-admin sweep signature" beforeSweep Ref.Sweep id id 0 0,
     edit "reject admin sweep at 168 BIP68 units" beforeSweep Ref.Sweep id (withInput 0 (setSeq (0x00400000+168))),
     edit "reject height-based sequence for time-based admin delay" beforeSweep Ref.Sweep id (withInput 0 (setSeq 169)),
     edit "reject admin coupon diversion" beforeSweep Ref.Sweep (changeNext [(3,1),(9,-1)]) id,
     invalid "reject initial unearned admin fee claim" initialized Ref.Sweep,
     invalid "reject repeated admin claim after profit anchor update" settled Ref.Sweep,
     edit "reject admin X redemption one height early" settled (Ref.RedeemFee x feeX) id
       (\tx -> tx {D.sigTxLock=D.sigTxLock tx-1}),
     edit "reject redirected admin Bitcoin payout" settled (Ref.RedeemFee x feeX) id (withOutput 1 wrongScript),
     invalid "reject admin redemption above coupon entitlement" settled (Ref.RedeemFee x (feeX+1)),
     edit "reject ordinary coupon redemption one height early" initialized redemption id
       (\tx -> tx {D.sigTxLock=D.sigTxLock tx-1}),
     edit "reject ordinary coupon payout redirected" initialized redemption id (withOutput 1 wrongScript),
     edit "reject ordinary coupon payout one sat short" initialized redemption id (withOutput 1 smaller),
     sameStateInputs "reject actual current input 1 even with both input scripts equal" 1 Reject,
     editPositive "reject Alice action signed by Bob" initialized swapX id id 1 0]
