{-# LANGUAGE RankNTypes #-}
-- | Native Lido withdrawal queue. Request IDs are one and two in an initialized
-- lineage. A finalization commits an immutable checkpoint and exact claim
-- amount for each request in the next FIFO prefix.
module JetDiscovery.Corpus.NativeLidoQueue (entries, queueT) where

import Prelude hiding (drop, take)
import qualified Prelude as H
import qualified Data.ByteString.Lazy as BL
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import Simplicity.Bitcoin.Term (Primitive, Simplicity)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Bit as B
import Simplicity.Term.Core
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Corpus.Baseline (signMsg)
import JetDiscovery.Corpus.ContractGrowth hiding (entries)
import JetDiscovery.Lib.Bytes (konst, w256, w256ToBytes)
import qualified JetDiscovery.Lib.LidoWithdrawalMath as Math
import qualified JetDiscovery.Lib.LogExpBounded as L
import JetDiscovery.Lib.State (stateScript, stateTap)
import JetDiscovery.Tx (dummyOutpoint, mkEnv, mkInput, mkOutput, mkTx)
import JetDiscovery.Types (Entry, Expect(..), Vector(..))
import Simplicity.Digest (Hash256)
import JetDiscovery.Tx (hashFromInteger)

-- Fixture only. The driver checks the complete canonical program independently.
queueFixtureCmr :: Hash256
queueFixtureCmr = hashFromInteger 0xea29d274c09b077049d8015a4e7546692c64a1702b911de958559beafea3c76d

-- The first four words are cash, last request, last finalized and realized
-- surplus. Each request has nominal value, owner, two checkpoint words,
-- locked payout and a claimed marker.
slot :: Int -> Int
slot request = 4 + 6 * (request - 1)

checkpoint :: (Core t, TyC a) => (Int -> t a Word64) -> Int -> t a Word128
checkpoint f request = f (slot request + 2) &&& f (slot request + 3)

validLedger :: Assert t => t Ledger ()
validLedger = allChecks
  [ le (field 2) (field 1)
  , le (field 1) (k 2)
  , checkRequest 1
  , checkRequest 2
  , same (field 0) (add (field 3) (add (liability 1) (liability 2)))
  ]
 where
  inPrefix request end = (k (toInteger request) &&& field end) >>> A.le word64
  requestField request offset = field (slot request + offset)
  checkRequest request = select (inPrefix request 1) present absent
   where
    f = requestField request
    absent = allChecks [same (f offset) (k 0) | offset <- [0..5]]
    present = allChecks
      [ Math.nominalBounds (f 0)
      , le (f 1) (k 1)
      , select (inPrefix request 2) finalized unfinalized
      ]
    finalized = allChecks
      [ Math.rateBounds (checkpoint field request)
      , nonzero (f 4)
      , le (f 4) (f 0)
      , le (f 5) (k 1)
      ]
    unfinalized = allChecks [same (f offset) (k 0) | offset <- [2..5]]
  liability request = select (inPrefix request 2)
    (select (is (requestField request 5) (k 0)) (requestField request 4) (k 0))
    (requestField request 0)

validWrapped :: J.WrappedSimplicity Ledger ()
validWrapped = J.jetSubst validLedger
{-# NOINLINE validWrapped #-}

queueT :: (Simplicity t, Primitive t) => GT t
queueT = allChecks
  [ base
  , old >>> J.unwrap validWrapped
  , new >>> J.unwrap validWrapped
  , choose [(0, append), (1, transfer), (2, finalize), (3, claim),
            (4, sweep), (5, close)]
  ]
 where
  authority = allChecks [same actor (k 3), sigAt 3]
  append = allChecks
    [ twoActor
    , actorSig
    , lt (o 1) (k 2)
    , Math.nominalBounds amount
    , changes
        [(0, add (o 0) amount), (1, add (o 1) (k 1)),
         (slot 1, select first amount (o (slot 1))),
         (slot 1 + 1, select first actor (o (slot 1 + 1))),
         (slot 2, select first (o (slot 2)) amount),
         (slot 2 + 1, select first (o (slot 2 + 1)) actor)]
    , deposit amount
    ]
   where first = is (o 1) (k 0)

  firstRequest = is amount (k 1)
  requestField offset = select firstRequest (o (slot 1 + offset)) (o (slot 2 + offset))
  ownsLiveRequest = allChecks
    [ twoActor, actorSig, nonzero amount, le amount (o 1)
    , same actor (requestField 1), same (requestField 5) (k 0)
    ]
  transfer = allChecks
    [ ownsLiveRequest
    , changes
        [(slot 1 + 1, select firstRequest (sub (k 1) actor) (o (slot 1 + 1))),
         (slot 2 + 1, select firstRequest (o (slot 2 + 1)) (sub (k 1) actor))]
    , noCash
    ]

  -- Mode 2 carries the exact E27 checkpoint in the low 128 bits of the
  -- auxiliary word. The finalization authority signs the actual outputs.
  rate = payload >>> oh >>> ih
  newlyFinalized request = B.and
    ((o 2 &&& k (toInteger request)) >>> A.lt word64)
    ((k (toInteger request) &&& amount) >>> A.le word64)
  requestQuote request = select (newlyFinalized request)
    ((o (slot request) &&& rate) >>> Math.claimAmount) (k 0)
  finalize = (allChecks
    [ authority, lt (o 2) amount, le amount (o 1)
    , same (payload >>> oh >>> oh) (L.ks 0)
    , Math.rateBounds rate
    ] &&& iden) >>> drop
      ((iden &&& (requestQuote 1 &&& requestQuote 2)) >>> finalizeChanges)
  finalizeChanges = allChecks
    (take noCash : [same (take (n i)) (maybe (take (o i)) id (lookup i updates))
                  | i <- [0..15]])
   where
    oldField i = take (o i)
    selected request = take (newlyFinalized request)
    quote 1 = ioh
    quote _ = iih
    released request = select (selected request)
      (sub (oldField (slot request)) (quote request)) (k 0)
    updates =
      [(2, take amount),
       (3, add (oldField 3) (add (released 1) (released 2)))]
      ++ concatMap record [1,2]
    record request =
      [ (slot request + offset, select (selected request) value
                                  (oldField (slot request + offset)))
      | (offset, value) <- [(2, take (rate >>> oh)), (3, take (rate >>> ih)),
                            (4, quote request)]
      ]

  claim = allChecks
    [ ownsLiveRequest, le amount (o 2)
    , changes
        [(0, sub (o 0) (requestField 4)),
         (slot 1 + 5, select firstRequest (k 1) (o (slot 1 + 5))),
         (slot 2 + 5, select firstRequest (o (slot 2 + 5)) (k 1))]
    , withdraw (requestField 4) actorDestination
    ]
  sweep = allChecks
    [ authority
    , changes [(0, sub (o 0) amount), (3, sub (o 3) amount)]
    , withdraw amount (destination 3)
    ]
  close = allChecks
    [ authority, same (o 1) (k 2), same (o 2) (k 2), same (o 0) (k 0)
    , allChecks [same (n i) (k 0) | i <- [0..15]]
    , inputFund (k 0), outCount 1
    , same (outVal 0) (k carrier), same (outScript 0) (destination 3)
    ]

-- Independent Integer fixtures use the source comparison and division rather
-- than the script's cross-multiplication.
type LedgerValues = [Integer]

update :: LedgerValues -> [(Int, Integer)] -> LedgerValues
update values fields =
  [maybe oldValue id (lookup i fields) | (i, oldValue) <- zip [0..15] (pad values)]

appendReference :: LedgerValues -> Integer -> Integer -> LedgerValues
appendReference oldState owner nominal =
  update oldState [(0, oldState H.!! 0 + nominal), (1, toInteger request),
                   (slot request, nominal), (slot request + 1, owner)]
 where request = fromInteger (oldState H.!! 1 + 1)

finalizeReference :: LedgerValues -> Integer -> Integer -> LedgerValues
finalizeReference oldState through maxRate =
  update oldState ([(2, through), (3, oldState H.!! 3 + surplus)] ++ records)
 where
  requestIds = [fromInteger (oldState H.!! 2 + 1)..fromInteger through]
  quotes = [(request, nominal, Math.claimAmountReference nominal maxRate)
           | request <- requestIds, let nominal = oldState H.!! slot request]
  surplus = H.sum [nominal - paid | (_, nominal, paid) <- quotes]
  records = concat [[(slot request + 2, maxRate `div` 2^64),
                    (slot request + 3, maxRate `mod` 2^64),
                    (slot request + 4, paid)]
                   | (request, _, paid) <- quotes]

claimReference :: LedgerValues -> Int -> LedgerValues
claimReference oldState request =
  update oldState [(0, oldState H.!! 0 - oldState H.!! (slot request + 4)),
                   (slot request + 5, 1)]

queueEntry :: Entry
queueEntry = entry "app-lido-fifo-withdrawal-queue"
  "Native Lido FIFO withdrawal requests, checkpoints and claims"
  "Lido core v4.1.0 WithdrawalQueueBase prefinalize, _finalize, _calcBatch, _claim and WithdrawalQueueERC721 owner transfer"
  [ "Two nonreusable request IDs with transferable ownership between two native keys. Appending a request locks its actual nominal BTC amount."
  , "Native enqueue conversion fixes totalShares / totalPooledEther at 3/4. Finalization authority signs the next FIFO prefix and a rate at E27 precision. Each request is a singleton batch; committed immutable checkpoints and locked amounts use the source's floor comparison and discounted payout."
  , "Cash equals unfinalized nominal collateral plus finalized unclaimed payouts plus realized surplus. Owners sign exact once-only payouts; the authority may withdraw only realized surplus and recover the carrier after both requests settle."
  , "This native model pre-funds the ETH-side equivalent with BTC at enqueue and projects out Ethereum token/rebase state and validator timestamps. Role keys and initialized queue lineage are fixed."
  ] queueT vectors
 where
  cmr = queueFixtureCmr
  empty = pad []
  one = appendReference empty 0 1001
  two = appendReference one 1 2000
  oneTransferred = update one [(slot 1 + 1, 1)]
  rateAtEquality = 1001 * Math.precision `div` 750
  lossRate = Math.precision
  highRate = 2 * Math.precision
  firstFinal = finalizeReference two 1 rateAtEquality
  bothFinal = finalizeReference firstFinal 2 lossRate
  sameCheckpoint = finalizeReference two 2 lossRate
  highCheckpoint = finalizeReference two 2 highRate
  lossFirst = finalizeReference one 1 lossRate
  firstPaid = claimReference bothFinal 1
  secondPaid = claimReference bothFinal 2
  allPaid = claimReference secondPaid 1
  secondTransferred = update bothFinal [(slot 2 + 1, 0)]
  paidAfterTransfer = claimReference secondTransferred 2
  surplus = allPaid H.!! 3
  swept = update allPaid [(0,0), (3,0)]
  positive label mode oldState newState owner number signer rate funding payout =
    go label mode oldState newState owner number signer rate funding payout Accept
  go label mode oldState newState owner number signer rate funding payout =
    vectorPayloadBound cmr label queueT mode oldState newState owner number signer
      (w256 rate, w256 0) funding payout 0xfffffffe
  pay state request owner = Just (owner, state H.!! (slot request + 4))
  closed label oldState signer paid expected = Vector label environment signed expected
   where
    environment actualCmr = mkEnv tx 0 (\root -> stateTap root (stateRef oldState)) actualCmr
     where
      lockingScript = stateScript actualCmr (stateRef oldState)
      tx = mkTx 2
        [mkInput (dummyOutpoint 0) (fromInteger (oldState H.!! 0 + carrier))
          (BL.fromStrict lockingScript) 0xfffffffe,
         mkInput (dummyOutpoint 1) 1000 (BL.fromStrict (recipient 9)) 0xfffffffe]
        [mkOutput (fromInteger paid) (recipient 3)] 0
    signed = (5,(oldState,empty),(3,0),(sig,zeroSig))
    sig = case environment cmr >>= (\e -> J.fastEval (J.unwrap (J.jetSubst SH.sigAllHash)) e ()) of
      Just message -> sigW (signMsg (keys H.!! signer) (w256ToBytes message))
      Nothing -> error "Lido terminal fixture message"
  vectors =
    [ positive "append funded request 1" 0 empty one 0 1001 0 0 1001 Nothing
    , positive "append funded request 2" 0 one two 1 2000 1 0 2000 Nothing
    , positive "transfer NFT before finalization" 1 one oneTransferred 0 1 0 0 0 Nothing
    , positive "FIFO finalization at floor equality locks the full 1001" 2 two firstFinal 3 1 3 rateAtEquality 0 Nothing
    , positive "next checkpoint discounts request 2 to 1500" 2 firstFinal bothFinal 3 2 3 lossRate 0 Nothing
    , positive "one checkpoint finalizes the complete two-request prefix" 2 two sameCheckpoint 3 2 3 lossRate 0 Nothing
    , positive "positive share rate cannot pay either request above nominal" 2 two highCheckpoint 3 2 3 highRate 0 Nothing
    , positive "authority can finalize only the currently issued request" 2 one lossFirst 3 1 3 lossRate 0 Nothing
    , positive "request 2 may claim before already-finalized request 1" 3 bothFinal secondPaid 1 2 1 0 0 (pay bothFinal 2 1)
    , positive "request 1 uses its original checkpoint after a lower one" 3 bothFinal firstPaid 0 1 0 0 0 (pay bothFinal 1 0)
    , positive "request 1 claims after request 2" 3 secondPaid allPaid 0 1 0 0 0 (pay bothFinal 1 0)
    , positive "transfer the finalized request NFT" 1 bothFinal secondTransferred 1 2 1 0 0 Nothing
    , positive "transferee claims exact discounted amount" 3 secondTransferred paidAfterTransfer 0 2 0 0 0 (pay bothFinal 2 0)
    , positive "withdraw only realized 500-sat surplus after both claims" 4 allPaid swept 3 surplus 3 0 0 (Just (3,surplus))
    , closed "authority recovers carrier after exhaustion" swept 3 carrier Accept
    , go "request nominal must be physically funded" 0 empty one 0 1001 0 0 1000 Nothing Reject
    , go "cannot reuse either request ID" 0 two two 0 1001 0 0 1001 Nothing Reject
    , go "cannot finalize an unissued request" 2 one firstFinal 3 2 3 lossRate 0 Nothing Reject
    , go "request 2 cannot finalize while request 1 remains pending" 2 two
        (update sameCheckpoint [(slot 1+2,0),(slot 1+3,0),(slot 1+4,0),
                                (3,500)]) 3 2 3 lossRate 0 Nothing Reject
    , go "other signer cannot authorize finalization" 2 two firstFinal 3 1 0 rateAtEquality 0 Nothing Reject
    , go "floor equality cannot lock the naive-min 1000 payout" 2 two
        (update firstFinal [(slot 1+4,1000),(3,1)]) 3 1 3 rateAtEquality 0 Nothing Reject
    , go "new checkpoint cannot overwrite an older valid checkpoint" 2 firstFinal
        (update bothFinal [(slot 1+3, (firstFinal H.!! (slot 1+3)) - 1)]) 3 2 3 lossRate 0 Nothing Reject
    , go "checkpoint below native rate bound" 2 two sameCheckpoint 3 2 3 (Math.precision `div` 2 - 1) 0 Nothing Reject
    , go "claim before finalization" 3 two two 1 2 1 0 0 (Just (1,1500)) Reject
    , go "previous owner cannot claim after transfer" 3 secondTransferred paidAfterTransfer 1 2 1 0 0 (pay bothFinal 2 1) Reject
    , go "current owner cannot redirect another beneficiary" 3 bothFinal secondPaid 1 2 1 0 0 (pay bothFinal 2 0) Reject
    , go "claimed NFT cannot be transferred" 1 firstPaid firstPaid 0 1 0 0 0 Nothing Reject
    , go "claimed NFT cannot be redeemed again" 3 secondPaid secondPaid 1 2 1 0 0 (pay bothFinal 2 1) Reject
    , go "authority cannot sweep from unclaimed backing" 4 bothFinal
        (update bothFinal [(0, bothFinal H.!! 0 - 501), (3,0)]) 3 501 3 0 0 (Just (3,501)) Reject
    , closed "carrier close cannot consume unclaimed payouts" bothFinal 3 carrier Reject
    , closed "carrier close requires the fixed authority" swept 0 carrier Reject
    ]

entries :: [Entry]
entries = [queueEntry]
