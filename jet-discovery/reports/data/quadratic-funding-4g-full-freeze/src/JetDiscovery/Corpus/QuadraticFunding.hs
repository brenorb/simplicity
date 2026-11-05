{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}
-- | Funded three-donor/two-project native quadratic funding. Every current
-- ledger and action enters through one bound witness.
module JetDiscovery.Corpus.QuadraticFunding
  ( entries, allocationT, roundCmr, referenceAudit ) where

import Prelude hiding (drop,take)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as C
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Serialize (runPutLazy)
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import Simplicity.Digest (Hash256)
import Simplicity.LibSecp256k1.Schnorr (Sig(..))
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (Bit,cond,verify)
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.LibSecp256k1.Lib as Secp
import Simplicity.Term.Core
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Apps (sigMsg)
import JetDiscovery.Corpus.Baseline (signSigAll)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Bip
import qualified JetDiscovery.Ref.QuadraticFunding as Ref

type Votes = (Word8,(Word8,Word8))
type Open = (Word16,(Votes,Votes))
type Claims = (Word16,(Word16,Word16))
type State = Either Open Claims
type Signature = (Word256,Word256)
type Donation = (Word8,(Word8,Signature))
type Action = Either Donation (Either Signature Word8)
type Input = (State,Action)
type Pay = (Word32,Word256)
type Plan = Either Pay (State,(Word32,Either () Pay))

donors, recipients :: [Integer]
donors = [3401,3402,3403]
recipients = [3411,3412,3421]
sponsor :: Integer
sponsor = 3421

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

eqT :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
eqT a b = (a&&&b)>>>eq>>>verify

checks :: (Core t,TyC a) => [t a ()] -> t a ()
checks = L.foldl' (\a b -> (a&&&b)>>>unit) unit

checked :: (Core t,TyC a,TyC b) => t a () -> t a b -> t a b
checked assertion result = (assertion&&&result)>>>ih

select :: (Core t,TyC a,TyC b) => t a Bit -> t a b -> t a b -> t a b
select p a b = (p&&&iden)>>>cond a b

add32,sub32,mul32 :: (Assert t,TyC a) => t a Word32 -> t a Word32 -> t a Word32
add32 a b = (a&&&b)>>>A.add word32>>>ih
sub32 a b = (a&&&b)>>>A.subtract word32>>>ih
mul32 a b = (a&&&b)>>>A.multiply word32>>>ih

z8 :: Core t => t Word8 Word32
z8 = c16 0&&&(c8 0&&&iden)
z16 :: Core t => t Word16 Word32
z16 = c16 0&&&iden
z32 :: Core t => t Word32 Word64
z32 = c32 0&&&iden

square8 :: Assert t => t Word8 Word32
square8 = (iden&&&iden)>>>A.multiply word8>>>z16

voice :: Core t => Int -> t Votes Word8
voice 0 = oh
voice 1 = ioh
voice 2 = iih
voice _ = error "fixed donor slot"

project :: Core t => Int -> t Open Votes
project 0 = ioh
project 1 = iih
project _ = error "fixed project slot"

direct :: Assert t => t Votes Word32
direct = add32 (oh>>>square8) (add32 (ioh>>>square8) (iih>>>square8))

stats :: Assert t => t Votes (Word32,Word32)
stats = (direct&&&add32 (oh>>>z8) (add32 (ioh>>>z8) (iih>>>z8)))>>>
        (oh&&&sub32 (mul32 ih ih) oh)

-- At v <= 63, each D <= 23,814, sumD <= 47,628, and the largest
-- min(B,sumD)*D <= 1,134,213,192. The Word32 product is exact.
fraction :: Assert t => t (Word32,(Word32,Word32)) Word32
fraction = select ((iih&&&c32 0)>>>eq) (c32 0)
           ((mul32 oh ioh&&&iih)>>>A.div_mod word32>>>oh)

type Stats = (Word32,((Word32,Word32),(Word32,Word32)))
matchShare :: Assert t => Int -> t (Stats,Word32) Word32
matchShare p = (cap&&&(deficit&&&ih))>>>fraction
 where
  budget = take oh
  cap = select ((budget&&&ih)>>>A.le word32) budget ih
  deficit = take (if p==0 then ioh else iih)>>>ih

allocationT :: Assert t => t Open Claims
allocationT =
  ((oh>>>z16)&&&((ioh>>>stats)&&&(iih>>>stats)))>>>
  (iden&&&add32 (ioh>>>ih) (iih>>>ih))>>>
  ((matchShare 0&&&matchShare 1)&&&oh)>>>
  ((add32 (ih>>>ioh>>>oh) ooh>>>ih)&&&
    ((add32 (ih>>>iih>>>oh) oih>>>ih)&&&
     (sub32 (ih>>>oh) (add32 ooh oih)>>>ih)))

openAmount :: Assert t => t Open Word32
openAmount = add32 (oh>>>z16) (add32 (ioh>>>direct) (iih>>>direct))

closedAmount :: Assert t => t Claims Word32
closedAmount = add32 (oh>>>z16) (add32 (ioh>>>z16) (iih>>>z16))

validOpen :: Assert t => t Open ()
validOpen = checks $
  ((c16 0&&&oh)>>>A.lt word16>>>verify):
  [((project p>>>voice i)&&&c8 Ref.cap)>>>A.le word8>>>verify | p<-[0,1],i<-[0,1,2]]

validClosed :: Assert t => t Claims ()
validClosed = checks [((f&&&c16 35721)>>>A.le word16>>>verify) | f<-[oh,ioh]]

stateWord :: Core t => t State Word256
stateWord = konst domain &&& ((iden&&&unit)>>>match (take openWord) (take closedWord))
 where
  domain = toWord128 (Bip.intFromBytes (C.pack "QF-BTC-Round-v1!"))
  openWord = c64 0&&&((oh&&&((project 0>>>voice 0)&&&(project 0>>>voice 1)))&&&
    (((project 0>>>voice 2)&&&(project 1>>>voice 0))&&&
     ((project 1>>>voice 1)&&&(project 1>>>voice 2))))
  closedWord = c64 1&&&((oh&&&ioh)&&&(iih&&&c16 0))

{-# NOINLINE scriptWrapped #-}
scriptWrapped :: J.WrappedSimplicity Word256 Word256
scriptWrapped = J.jetSubst (stateScriptHash iden)

stateScriptT :: Simplicity t => t State Word256
stateScriptT = stateWord >>> J.unwrap scriptWrapped

inValue :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
inValue i = c32 i>>>primitive P.InputValue>>>verify
inScript :: (Assert t,Primitive t,TyC a) => Integer -> t a Word256
inScript i = c32 i>>>primitive P.InputScriptHash>>>verify
outValue :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
outValue i = c32 i>>>primitive P.OutputValue>>>verify
outScript :: (Assert t,Primitive t,TyC a) => Integer -> t a Word256
outScript i = c32 i>>>primitive P.OutputScriptHash>>>verify
outCount :: (Assert t,Primitive t,TyC a) => Integer -> t a ()
outCount n = eqT (unit>>>Tx.numOutputs) (c32 n)

payT :: (Assert t,Primitive t) => Integer -> t Pay ()
payT index = checks [eqT (outValue index) (oh>>>z32),eqT (outScript index) ih]

layout :: forall t. (Simplicity t,Primitive t) => t Plan ()
layout = (iden&&&unit)>>>match (take (checks [outCount 1,payT 0])) (take continuation)
 where
  continuation :: t (State,(Word32,Either () Pay)) ()
  continuation = checks [eqT (outValue 0) (ioh>>>z32),eqT (outScript 0) (oh>>>stateScriptT),
    (iih&&&unit)>>>match (outCount 1) (take (checks [outCount 2,payT 1]))]

type Pick = (Word8,(Word8,Open))
type Selected = (Word8,(Word8,(Open,(Word256,Word256))))
chooseDonation :: forall t. Assert t => t Pick Selected
chooseDonation = L.foldr (\i rest -> select ((oh&&&c8 (toInteger i))>>>eq) (choice i) rest) failure [0..5]
 where
  choice :: Int -> t Pick Selected
  choice slot = (iih>>>project p>>>voice d)&&&(ioh&&&(new&&&keys))
   where
    (p,d) = slot `divMod` 3
    sk = donors !! d
    keys = konst (w256 (Bip.pubkeyOf sk),scriptHash (p2tr sk))
    update i j | i==p && j==d = ioh
               | otherwise = iih>>>project i>>>voice j
    votes i = update i 0&&&(update i 1&&&update i 2)
    new = (iih>>>oh)&&&(votes 0&&&votes 1)

signed :: (Simplicity t,Primitive t,TyC a) => t a Word256 -> t a Signature -> t a ()
signed key signature = (((key&&&(unit>>>sigMsg))&&&signature)>>>Secp.bip_0340_verify)

contribute :: forall t. (Simplicity t,Primitive t) => t (Donation,Open) Plan
contribute = ((((ooh&&&(oioh&&&ih))>>>chooseDonation)&&&oiih)&&&(ih>>>openAmount))>>>step
 where
  step :: t ((Selected,Signature),Word32) Plan
  step = checked
    (checks [((old&&&new)>>>A.lt word8>>>verify),((new&&&c8 Ref.cap)>>>A.le word8>>>verify),
      eqT (inScript 1) (sel>>>iih>>>ih>>>ih),
      eqT (inValue 1) (add32 delta (c32 Ref.fee)>>>z32),
      signed (sel>>>iih>>>ih>>>oh) oih])
    (injr (injl (sel>>>iih>>>oh)&&&(add32 ih delta&&&injl unit)))
   where
    sel = ooh
    old = sel>>>oh
    new = sel>>>ioh
    delta = sub32 (new>>>square8) (old>>>square8)

close :: (Simplicity t,Primitive t) => t (Signature,Open) Plan
close = checked (checks [eqT (inValue 1) (c64 Ref.fee),signed (konst (w256 (Bip.pubkeyOf sponsor))) oh])
         (injr (injr (ih>>>allocationT)&&&((ih>>>openAmount)&&&injl unit)))

type ClaimPick = (Word32,(Claims,Word256))
chooseClaim :: forall t. Assert t => t (Word8,Claims) ClaimPick
chooseClaim = L.foldr (\i rest -> select ((oh&&&c8 (toInteger i))>>>eq) (pick i) rest) failure [0..2]
 where
  pick :: Int -> t (Word8,Claims) ClaimPick
  pick i = (ih>>>field i>>>z16)&&&
           ((keep 0&&&(keep 1&&&keep 2))&&&konst (scriptHash (p2tr (recipients !! i))))
   where
    field j = [oh,ioh,iih] !! j
    keep j = if j==i then c16 0 else ih>>>field j

claim :: (Simplicity t,Primitive t) => t (Word8,Claims) Plan
claim = chooseClaim>>>checked
  (checks [((c32 0&&&oh)>>>A.lt word32>>>verify),eqT (inValue 1) (c64 Ref.fee)])
  (select ((remaining&&&c32 0)>>>eq)
    (injl pay) (injr (injr ioh&&&(remaining&&&injr pay))))
 where
  remaining = ioh>>>closedAmount
  pay = oh&&&iih

kernel :: forall t. (Simplicity t,Primitive t) => t Input ()
kernel = checked
  (checks [eqT (unit>>>primitive P.CurrentIndex) (c32 0),eqT (unit>>>Tx.numInputs) (c32 2),
     loadState (oh>>>stateWord),eqT (inScript 0) (oh>>>stateScriptT)])
  (match openStep closedStep>>>layout)
 where
  openStep :: t (Open,Action) Plan
  openStep = checked
    (checks [oh>>>validOpen,eqT (unit>>>Tx.currentValue) (oh>>>openAmount>>>z32)])
    ((ih&&&oh)>>>match contribute (match close failure))
  closedStep :: t (Claims,Action) Plan
  closedStep = checked
    (checks [oh>>>validClosed,eqT (unit>>>Tx.currentValue) (oh>>>closedAmount>>>z32)])
    ((ih&&&oh)>>>match failure (match failure claim))

program :: Input -> Prog
program = boundProgram kernel

packState :: Ref.State -> State
packState (Ref.Open b x y) = Left (w16 b,(votes x,votes y))
 where votes (a,c,d) = (w8 a,(w8 c,w8 d))
packState (Ref.Closed (a,b,c)) = Right (w16 a,(w16 b,w16 c))

zeroSig :: Signature
zeroSig = (w256 0,w256 0)

roundCmr :: Hash256
roundCmr = progCmr (program (packState (Ref.initial 1),Right (Right (w8 0))))

referenceAudit :: Bool
referenceAudit = Ref.referenceAudit

entries :: [Entry]
entries = [Entry "app-budgeted-quadratic-funding" "Native funded quadratic round with exact capped matching and one-time claims"
  "Buterin–Hitzig–Weyl arXiv:1809.06421v2 §§4,5.1–5.2; exact perfect-square bounded native CQF profile"
  CrossChain (Derived "independent Integer pair-product reference; real BTC UTXO funding, full close and once-only outputs")
  ["three fixed donor keys, two projects; per-donor per-project v=0..63 with cumulative contribution v² sat",
   "sponsor-funded initial budget 1..65535 sat; authorized closure fixes floor(min(B,sumD)*D_p/sumD), zero when sumD=0",
   "every floor remainder and unused sponsor budget belongs to immutable sponsor; independent exact payout of each nonzero claim",
   "one initialized same-leaf state lineage; input 0 only, exact BTC backing, input 1 funds contribution plus fixed fee or fee alone",
   "fixed roster is not Sybil resistance; explicit sponsor closure, no off-chain production Gitcoin calculator, fiat donations or relay policy claim"]
  program vectors]

type Build = (Ref.State,D.Outpoint)

stateOutput :: Ref.State -> D.TxOutput
stateOutput s = mkOutput (fromInteger (Ref.balance s)) (stateScript roundCmr (Ref.encode s))

payOutput :: Int -> Integer -> D.TxOutput
payOutput i n = mkOutput (fromInteger n) (p2tr (recipients !! i))

stateInput :: Build -> D.SigTxInput
stateInput (s,p) = mkInput p (fromInteger (Ref.balance s))
  (BL.fromStrict (stateScript roundCmr (Ref.encode s))) 0

fundInput :: Build -> Integer -> Integer -> D.SigTxInput
fundInput (_,D.Outpoint h _) sk n =
  mkInput (D.Outpoint (sha256 (hashToBytes h)) 1) (fromInteger n) (BL.fromStrict (p2tr sk)) 0

signer :: Ref.Action -> Maybe Integer
signer (Ref.Donate i _) = Just (donors !! (i `mod` 3))
signer Ref.Close = Just sponsor
signer (Ref.Claim _) = Nothing

fundKey :: Ref.Action -> Integer
fundKey a@(Ref.Donate _ _) = maybe (error "donation role") id (signer a)
fundKey _ = 3499

transaction :: Build -> Ref.Action -> (D.SigTx,Ref.Step)
transaction b@(old,_) action = (mkTx 2 [stateInput b,fundInput b (fundKey action) (Ref.fee+debit)] outputs 0,result)
 where
  result@(Ref.Step next debit payment) = maybe (error "invalid reference fixture step") id (Ref.apply old action)
  outputs = maybe [] (pure . stateOutput) next ++ maybe [] (pure . uncurry payOutput) payment

initial :: Integer -> Build
initial b = (Ref.initial b,dummyOutpoint (fromInteger b))

advance :: Build -> Ref.Action -> Build
advance b a = (next,D.Outpoint (sha256 (hashToBytes (sha256 raw))) 0)
 where
  (tx,step) = transaction b a
  next = maybe (error "terminal step has no output") id (Ref.successor step)
  raw = BL.toStrict (runPutLazy (D.putNoWitnessTx tx))

getSignature :: Maybe Integer -> Ref.State -> D.SigTx -> Signature
getSignature Nothing _ _ = zeroSig
getSignature (Just sk) old tx = case mkEnv tx 0 (\leaf -> stateTap leaf (Ref.encode old)) roundCmr of
  Just env -> case signSigAll sk env of Sig r s -> (w256 (toInteger r),w256 (toInteger s))
  Nothing -> error "quadratic funding signature fixture environment"

input :: Ref.State -> Ref.Action -> Signature -> Input
input old action sig = (packState old, case action of
  Ref.Donate i v -> Left (w8 (toInteger i),(w8 v,sig))
  Ref.Close -> Right (Left sig)
  Ref.Claim i -> Right (Right (w8 (toInteger i))))

vector :: String -> Ref.State -> Input -> D.SigTx -> Integer -> Expect -> Vector Input
vector name actual wit tx ix = Vector name
  (mkEnv tx (fromInteger ix) (\leaf -> stateTap leaf (Ref.encode actual))) wit

positive :: String -> Build -> Ref.Action -> Vector Input
positive name b@(old,_) a =
  vector name old (input old a (getSignature (signer a) old tx)) tx 0 Accept
 where (tx,_) = transaction b a

vectors :: [Vector Input]
vectors = positives ++ negatives
 where
  b0 = initial 1001
  d1 = advance b0 (Ref.Donate 0 10)
  d2 = advance d1 (Ref.Donate 0 20)
  d3 = advance d2 (Ref.Donate 1 20)
  d4 = advance d3 (Ref.Donate 3 20)
  d5 = advance d4 (Ref.Donate 4 10)
  f0 = advance d5 Ref.Close
  f1 = advance f0 (Ref.Claim 0)
  f2 = advance f1 (Ref.Claim 1)
  sponsorFirst = advance f0 (Ref.Claim 2)
  noDeficit = L.foldl' advance b0 [Ref.Donate 0 20,Ref.Donate 5 10]
  uncapped = L.foldl' advance (initial 2000)
    [Ref.Donate 0 20,Ref.Donate 1 20,Ref.Donate 3 20,Ref.Donate 4 10]
  maximumVotes = L.foldl' advance (initial 65535) [Ref.Donate i 63 | i<-[0..5]]
  duplicate = advance (initial 1000) Ref.Close
  duplicateTx = mkTx 2 [stateInput duplicate,stateInput (fst duplicate,dummyOutpoint 999)]
                           [payOutput 2 1000] 0
  duplicateW = input (fst duplicate) (Ref.Claim 2) zeroSig
  (spend0,_) = transaction f0 (Ref.Claim 0)
  closedOld = fst f0
  close0 = input closedOld (Ref.Claim 0) zeroSig
  outList tx = V.toList (D.sigTxOut tx)
  inList tx = V.toList (D.sigTxIn tx)
  changeOut tx outs = mkTx 2 (inList tx) outs 0
  reject name b@(old,_) a sk tx =
    vector name old (input (fst b) a (getSignature sk old tx)) tx 0 Reject
  refuse name w tx = vector name closedOld w tx 0 Reject
  (donationTx,_) = transaction d1 (Ref.Donate 0 20)
  (initialDonation,_) = transaction b0 (Ref.Donate 0 10)
  (crossProject,_) = transaction b0 (Ref.Donate 3 10)
  firstSig = getSignature (signer (Ref.Donate 0 10)) (fst b0) initialDonation
  (closeTx,_) = transaction d5 Ref.Close
  closeA b = fst (transaction b Ref.Close)
  continued = head (outList spend0)
  badFund n key = mkTx 2 [stateInput d1,fundInput d1 key n] (outList donationTx) 0
  badVoice b sk v = mkTx 2 [stateInput b,fundInput b sk (Ref.fee+v*v)]
    [stateOutput (Ref.Open 1001 (v,0,0) (0,0,0))] 0
  noIncrease = mkTx 2 [stateInput d2,fundInput d2 (head donors) Ref.fee] [stateOutput (fst d2)] 0
  malformedState n script = mkInput (snd f0) (fromInteger n) (BL.fromStrict script) 0
  claimInputs a = mkTx 2 [a,fundInput f0 3499 Ref.fee] (outList spend0) 0
  positives =
    [ positive "donor zero funds first square increment" b0 (Ref.Donate 0 10)
    , positive "split contribution pays cumulative square difference" d1 (Ref.Donate 0 20)
    , positive "donor one adds matching weight to project zero" d2 (Ref.Donate 1 20)
    , positive "same donor may choose project one separately" d3 (Ref.Donate 3 20)
    , positive "second project accrues distinct matching deficit" d4 (Ref.Donate 4 10)
    , positive "donor two funds sixth slot at voice cap" d5 (Ref.Donate 5 63)
    , positive "capped close yields floors and one sat sponsor remainder" d5 Ref.Close
    , positive "uncapped close returns all unused sponsor budget" uncapped Ref.Close
    , positive "zero denominator returns sponsor budget without a match" noDeficit Ref.Close
    , positive "empty round closes into sponsor refund only" b0 Ref.Close
    , positive "maximum safe votes and sponsor budget close exactly" maximumVotes Ref.Close
    , positive "project zero exact once-only claim" f0 (Ref.Claim 0)
    , positive "project one claim after project zero" f1 (Ref.Claim 1)
    , positive "last sponsor remainder payout has no state output" f2 (Ref.Claim 2)
    , positive "sponsor may claim before both projects" f0 (Ref.Claim 2)
    , positive "project one may claim first after early sponsor claim" sponsorFirst (Ref.Claim 1)
    , vector "duplicate-input control accepts protected input zero" (fst duplicate) duplicateW duplicateTx 0 Accept
    ]
  negatives =
    [ reject "split donation cannot pay the new delta squared" d1 (Ref.Donate 0 20) (signer (Ref.Donate 0 20))
        (badFund (Ref.fee+100) (head donors))
    , reject "wrong fixed donor signature" d1 (Ref.Donate 0 20) (Just (donors !! 1)) donationTx
    , reject "actual funding input must use selected donor script" d1 (Ref.Donate 0 20) (Just (head donors))
        (badFund (Ref.fee+300) (donors !! 1))
    , vector "same signed donation cannot be replayed at updated voice" (fst d1)
        (input (fst d1) (Ref.Donate 0 20) firstSig) donationTx 0 Reject
    , vector "same signature cannot change projects" (fst b0)
        (input (fst b0) (Ref.Donate 3 10) firstSig) crossProject 0 Reject
    , reject "voice above cap with correct signature and nominal funding" b0 (Ref.Donate 0 64)
        (Just (head donors)) (badVoice b0 (head donors) 64)
    , reject "voice must strictly increase" d2 (Ref.Donate 0 20) (Just (head donors)) noIncrease
    , reject "unknown seventh donor-project slot" b0 (Ref.Donate 6 10) (Just (head donors)) initialDonation
    , reject "non-sponsor cannot close" d5 Ref.Close (Just (head donors)) closeTx
    , reject "sponsor cannot sign away one project entitlement" d5 Ref.Close (Just sponsor)
        (changeOut closeTx [stateOutput (Ref.Closed (1466,833,2))])
    , reject "no-match close cannot assign sponsor satoshis to a project" noDeficit Ref.Close (Just sponsor)
        (changeOut (closeA noDeficit) [stateOutput (Ref.Closed (401,100,1000))])
    , reject "claim is unavailable before close" d5 (Ref.Claim 0) Nothing closeTx
    , reject "second close cannot reopen matching" f0 Ref.Close (Just sponsor) spend0
    , reject "donation cannot reopen closed state" f0 (Ref.Donate 0 10) (Just (head donors)) spend0
    , refuse "wrong project payout script" close0 (changeOut spend0 [continued,payOutput 1 1467])
    , refuse "rounded-up payout" close0 (changeOut spend0 [continued,payOutput 0 1468])
    , refuse "paid slot must be zero in continuation" close0
        (changeOut spend0 [mkOutput 834 (stateScript roundCmr (Ref.encode closedOld)),payOutput 0 1467])
    , refuse "unexpected third output" close0 (changeOut spend0 [continued,payOutput 0 1467,mkOutput 1 BS.empty])
    , refuse "actual backing cannot exceed committed remaining claims" close0
        (claimInputs (malformedState 2302 (stateScript roundCmr (Ref.encode closedOld))))
    , refuse "actual current input script must open the same state" close0
        (claimInputs (malformedState 2301 (p2tr sponsor)))
    , refuse "stale witness cannot substitute a different allocation"
        (input (Ref.Closed (1468,832,1)) (Ref.Claim 0) zeroSig) spend0
    , reject "claim is unavailable after exact withdrawal" f1 (Ref.Claim 0) Nothing (fst (transaction f1 (Ref.Claim 1)))
    , reject "unknown claim index" f0 (Ref.Claim 3) Nothing spend0
    , vector "second identical state input cannot reuse the sponsor payout" (fst duplicate) duplicateW duplicateTx 1 Reject
    ]
