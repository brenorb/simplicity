{-# LANGUAGE RankNTypes #-}
-- | Repeated native receipts and cumulative payee claims. The account ledger
-- is opened once; the successor and payout are computed from that same input.
module JetDiscovery.Corpus.CumulativeSplitter (entries, referenceAudit) where

import Prelude hiding (drop,take,not)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BL
import qualified Data.List as L
import qualified Data.Vector as V
import Data.Serialize (runPutLazy)
import qualified Simplicity.Bitcoin.DataTypes as D
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.Term (Primitive,Simplicity,primitive)
import Simplicity.Digest (Hash256)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Term.Core
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.ContractGrowth (add, allChecks, k, le, nonzero, same, scriptHash, select, sub)
import JetDiscovery.Lib.Bytes (failure,konst,w8,w32,w64)
import JetDiscovery.Lib.State (loadState,stateScript,stateScriptHash,stateTap)
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Bip
import qualified JetDiscovery.Ref.CumulativeSplitter as Ref

type Ledger = ((Word64,Word64),(Word64,Word64))
type Action = Either () Word8
type Input = (Ledger,Action)
type Payout = Either () (Word64,Word256)

anchor, fee :: Integer
anchor = 1000
fee = 1200

payee :: Int -> BS.ByteString
payee i = unhex "5120" <> Bip.bytesFromInt (Bip.pubkeyOf ([1901,1902,1903] !! i))

packLedger :: Ref.Ledger -> Ledger
packLedger (Ref.Ledger r (a,b,c)) = ((w64 r,w64 a),(w64 b,w64 c))

ledgerDigest :: Assert t => t Ledger Word256
ledgerDigest = L.foldl' (\ctx field -> (ctx &&& field) >>> ctx8Add8)
  (unit >>> ctx8InitTag "JetDiscovery/CumulativeSplitter/V1") [ooh,oih,ioh,iih] >>> ctx8Finalize

stateBytes :: Ref.Ledger -> BS.ByteString
stateBytes = Bip.taggedHash "JetDiscovery/CumulativeSplitter/V1" . Ref.encode

backing :: Assert t => t Ledger Word64
backing = add (k anchor) (sub ooh (add oih (add ioh iih)))

-- Fixed shares 1:2:3 yield the exact three floors R/6, R/3, R/2.
entitlement :: Assert t => Integer -> t Ledger Word64
entitlement divisor = (ooh &&& k divisor) >>> Arith.div_mod word64 >>> oh

validLedger :: Assert t => t Ledger ()
validLedger = allChecks [le ooh (k Ref.receivedLimit),le oih (entitlement 6),
                        le ioh (entitlement 3),le iih (entitlement 2)]

funding :: (Assert t,Primitive t,TyC a) => t a Word64
funding = konst (w32 1) >>> primitive P.InputValue >>> verify

receive :: (Assert t,Primitive t) => t ((),Ledger) (Ledger,Payout)
receive = ih >>> ((nonzero delta &&& le next (k Ref.receivedLimit)) &&&
                  (((next &&& oih) &&& ih) &&& injl unit)) >>> ih
 where
  delta = sub funding (k fee)
  next = add ooh delta

release :: (Assert t,Primitive t) => t (Word8,Ledger) (Ledger,Payout)
release = select (selected 0) (ih >>> pay 0) $
          select (selected 1) (ih >>> pay 1) $
          select (selected 2) (ih >>> pay 2) failure
 where
  selected i = (oh &&& konst (w8 i)) >>> eq
  pay i = ((same funding (k fee) &&& nonzero due) &&& (next &&& injr payout)) >>> ih
   where
    accrued = entitlement ([6,3,2] !! i)
    due = sub accrued ([oih,ioh,iih] !! i)
    keep j f = if i == j then accrued else f
    next = (ooh &&& keep 0 oih) &&& (keep 1 ioh &&& keep 2 iih)
    payout = due &&& konst (scriptHash (payee i))

outVal :: (Assert t,Primitive t,TyC a) => Integer -> t a Word64
outVal i = konst (w32 i) >>> primitive P.OutputValue >>> verify

outHash :: (Assert t,Primitive t,TyC a) => Integer -> t a Word256
outHash i = konst (w32 i) >>> primitive P.OutputScriptHash >>> verify

outCount :: (Assert t,Primitive t,TyC a) => Integer -> t a ()
outCount n = same (unit >>> Tx.numOutputs) (konst (w32 n))

settle :: (Assert t,Primitive t) => t (Ledger,Payout) ()
settle = allChecks [same (outVal 0) (oh >>> backing),
                    same (outHash 0) (stateScriptHash (oh >>> ledgerDigest)),
                    (ih &&& unit) >>> match (outCount 1) disburse]
 where
  disburse = allChecks [outCount 2,same (outVal 1) ooh,same (outHash 1) oih]

kernel :: (Simplicity t,Primitive t) => t Input ()
kernel = allChecks [same (unit >>> primitive P.CurrentIndex) (konst (w32 0)),
                   same (unit >>> Tx.numInputs) (konst (w32 2)),
                   oh >>> validLedger,
                   same (unit >>> Tx.currentValue) (oh >>> backing),
                   loadState (oh >>> ledgerDigest),
                   same (konst (w32 0) >>> primitive P.InputScriptHash >>> verify)
                        (stateScriptHash (oh >>> ledgerDigest)),
                   (ih &&& oh) >>> match receive release >>> settle]

program :: Input -> Prog
program = boundProgram kernel

cmr :: Hash256
cmr = progCmr (program (packLedger Ref.initial,Left ()))

ledgerOutput :: Ref.Ledger -> D.TxOutput
ledgerOutput ledger = mkOutput (fromInteger (anchor + Ref.outstanding ledger))
                               (stateScript cmr (stateBytes ledger))

type Build = (Ref.Ledger,D.Outpoint)

transaction :: Build -> Ref.Action -> (D.SigTx,Ref.Ledger)
transaction (old,op) action = (mkTx 2 inputs outputs 0,new)
 where
  Just (new,payout) = Ref.apply old action
  donation = case action of Ref.Receive d -> d; Ref.Release _ -> 0
  inputs = [ledgerInput op old, feeInput op (fee+donation)]
  outputs = ledgerOutput new : maybe [] (\(i,n) -> [mkOutput (fromInteger n) (payee i)]) payout

feeInput :: D.Outpoint -> Integer -> D.SigTxInput
feeInput (D.Outpoint h _) n = mkInput (D.Outpoint (sha256 (hashToBytes h)) 1)
                                     (fromInteger n) (BL.fromStrict (payee 2)) 0

ledgerInput :: D.Outpoint -> Ref.Ledger -> D.SigTxInput
ledgerInput op l = mkInput op (D.txoValue (ledgerOutput l)) (D.txoScript (ledgerOutput l)) 0

successor :: Build -> Ref.Action -> Build
successor old action = (ledger,D.Outpoint (sha256 (hashToBytes (sha256 wire))) 0)
 where
  (tx,ledger) = transaction old action
  wire = BL.toStrict (runPutLazy (D.putNoWitnessTx tx))

start :: Build
start = (Ref.initial,dummyOutpoint 0)

witnessFor :: Ref.Ledger -> Ref.Action -> Input
witnessFor l a = (packLedger l,case a of Ref.Receive _ -> Left (); Ref.Release i -> Right (w8 (toInteger i)))

mkVector :: String -> Ref.Ledger -> Input -> D.SigTx -> Integer -> Expect -> Vector Input
mkVector name actual w tx ix = Vector name
  (mkEnv tx (fromInteger ix) (\leaf -> stateTap leaf (stateBytes actual))) w

positive :: String -> Build -> Ref.Action -> Vector Input
positive name old@(ledger,_) action = mkVector name ledger (witnessFor ledger action) (fst (transaction old action)) 0 Accept

entries :: [Entry]
entries = [Entry "app-cumulative-payment-splitter" "Native cumulative pull-payment splitter with historical rounding"
  "OpenZeppelin PaymentSplitter v4.9.6 dc44c9f1a4c3b10af99492eed84f83ed244203f6, native Ether release/pending-payment relation"
  CrossChain (Derived "independent Integer source formula; actual input funding, Taproot continuation and exact recipient outputs")
  ["one initialized BTC lineage, immutable 1:2:3 shares and three payee scripts, with receipts bounded to 48 bits",
   "actual input 0 and exactly one fee/funding input; fixed 1,200-sat fee and preserved 1,000-sat state anchor, excluded from payee income",
   "permissionless release pays only immutable recipient; small exact rounding vectors are consensus-level fixtures and may be relay dust",
   "no ERC20, arbitrary share reconfiguration, or EVM callbacks; funding the initial state is a setup action"] program vectors]

vectors :: [Vector Input]
vectors = positives ++ negatives
 where
  d1 = successor start (Ref.Receive 1)
  d2 = successor d1 (Ref.Receive 1)
  d3 = successor d2 (Ref.Receive 1)
  d6 = L.foldl' successor d3 (replicate 3 (Ref.Receive 1))
  afterC = successor d6 (Ref.Release 2)
  afterB = successor afterC (Ref.Release 1)
  afterA = successor afterB (Ref.Release 0)
  alternate = successor (successor d6 (Ref.Release 0)) (Ref.Release 1)
  grown = successor afterA (Ref.Receive 12003)
  maxed = successor start (Ref.Receive Ref.receivedLimit)
  (old,op) = d6
  (payTx,_) = transaction d6 (Ref.Release 0)
  (depTx,_) = transaction d6 (Ref.Receive 9000)
  valid = witnessFor old (Ref.Release 0)
  depositW = witnessFor old (Ref.Receive 9000)
  continuation = D.sigTxOut payTx V.! 0
  replaceOut outs = mkTx 2 [ledgerInput op old,feeInput op fee] outs 0
  reject name w tx i = mkVector name old w tx i Reject
  (duplicateOld,duplicateOp) = successor start (Ref.Receive (fee-anchor))
  dupW = witnessFor duplicateOld (Ref.Release 0)
  (dupBase,_) = transaction (duplicateOld,duplicateOp) (Ref.Release 0)
  dupTx = mkTx 2 [ledgerInput duplicateOp duplicateOld,ledgerInput (dummyOutpoint 99) duplicateOld]
                (V.toList (D.sigTxOut dupBase)) 0
  positives = [positive "first one-sat receipt" start (Ref.Receive 1),
    positive "second one-sat receipt" d1 (Ref.Receive 1),
    positive "third one-sat receipt" d2 (Ref.Receive 1),
    positive "one-half share first becomes payable" d2 (Ref.Release 2),
    positive "one-third share first becomes payable" d3 (Ref.Release 1),
    positive "one-sixth entitlement after six separate receipts" d6 (Ref.Release 0),
    positive "largest payee releases before others" d6 (Ref.Release 2),
    positive "middle payee still earns lifetime share after release" afterC (Ref.Release 1),
    positive "last withdrawal leaves only permanent anchor" afterB (Ref.Release 0),
    positive "alternative claim order also leaves only anchor" alternate (Ref.Release 2),
    positive "receive new funds after all earlier income released" afterA (Ref.Receive 12003),
    positive "larger payout excludes previously released credit" grown (Ref.Release 0),
    positive "maximum supported lifetime receipts" start (Ref.Receive Ref.receivedLimit),
    mkVector "index zero can authorize its own side of duplicate-input control" duplicateOld dupW dupTx 0 Accept]
  negatives = [mkVector "pending amount zero before threshold" (fst d1)
      (witnessFor (fst d1) (Ref.Release 0)) (fst (transaction d1 (Ref.Receive 1))) 0 Reject,
    mkVector "claim cannot be repeated after exhausted entitlement" (fst afterA)
      (witnessFor (fst afterA) (Ref.Release 0)) (fst (transaction afterA (Ref.Receive 1))) 0 Reject,
    reject "wrong payee" valid (replaceOut [continuation,mkOutput 1 (payee 2)]) 0,
    reject "rounded-up payout" valid (replaceOut [continuation,mkOutput 2 (payee 0)]) 0,
    reject "unexpected extra output" valid (replaceOut [continuation,mkOutput 1 (payee 0),mkOutput 0 BS.empty]) 0,
    reject "incorrect continuation ledger" valid (replaceOut [ledgerOutput old,mkOutput 1 (payee 0)]) 0,
    reject "incorrect current value" valid
      (mkTx 2 [mkInput op 1007 (D.txoScript (ledgerOutput old)) 0,feeInput op fee] [continuation,mkOutput 1 (payee 0)] 0) 0,
    reject "incorrect actual current script" valid
      (mkTx 2 [mkInput op 1006 (BL.fromStrict (payee 0)) 0,feeInput op fee] [continuation,mkOutput 1 (payee 0)] 0) 0,
    mkVector "second identical state input cannot reuse payout" duplicateOld dupW dupTx 1 Reject,
    reject "unopened ledger cannot fabricate received history"
      (witnessFor (Ref.Ledger 12 (2,4,0)) (Ref.Release 2)) payTx 0,
    reject "payee index outside initialized set" (packLedger old,Right (w8 3)) payTx 0,
    reject "claimed donation missing from actual funding input" depositW
      (mkTx 2 [ledgerInput op old,feeInput op fee] (V.toList (D.sigTxOut depTx)) 0) 0,
    reject "fee deduction cannot wrap" depositW
      (mkTx 2 [ledgerInput op old,feeInput op (fee-1)] (V.toList (D.sigTxOut depTx)) 0) 0,
    mkVector "lifetime receipt cap cannot overflow" (fst maxed) (witnessFor (fst maxed) (Ref.Receive 1))
      (mkTx 2 [ledgerInput (snd maxed) (fst maxed),feeInput (snd maxed) (fee+1)] [ledgerOutput (fst maxed)] 0) 0 Reject]

-- Independent lifetime-receipt calculation and all six claim orders.
referenceAudit :: Bool
referenceAudit = and [permutationInvariant,history,limits]
 where
  next r a = fst <$> Ref.apply r a
  Just six = foldl (\m _ -> m >>= \r -> next r (Ref.Receive 1)) (Just Ref.initial) [1..6 :: Int]
  claims order = foldl (\m i -> m >>= \r -> next r (Ref.Release i)) (Just six) order
  permutationInvariant = all (\is -> claims is == Just (Ref.Ledger 6 (1,2,3))) (L.permutations [0,1,2])
  history = case Ref.apply six (Ref.Release 2) of
    Just (after,Just (2,3)) -> Ref.outstanding after == 3 &&
      Ref.apply after (Ref.Release 0) == Just (Ref.Ledger 6 (1,0,3),Just (0,1)) &&
      Ref.apply after (Ref.Release 2) == Nothing
    _ -> False
  limits = Ref.apply Ref.initial (Ref.Receive 0)==Nothing &&
           Ref.apply Ref.initial (Ref.Receive (Ref.receivedLimit+1))==Nothing &&
           Ref.apply (Ref.Ledger 6 (2,0,0)) (Ref.Release 0)==Nothing
