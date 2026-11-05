-- | Exact singleton-batch claim arithmetic from Lido WithdrawalQueueBase.
module JetDiscovery.Lib.LidoWithdrawalMath
  ( precision, minNominal, maxNominal, rateBounds, nominalBounds
  , claimAmount, claimAmountReference, requestSharesReference
  ) where

import Prelude hiding (drop, take)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (verify)
import qualified Simplicity.Programs.Word as W
import Simplicity.Term.Core
import Simplicity.Ty.Word
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Lib.Bytes (konst, w8)
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.StableMath as S

precision, minNominal, maxNominal :: Integer
precision = 10^27
minNominal = 1000
maxNominal = 10^9

nominalBounds :: (Assert t, TyC a) => t a Word64 -> t a ()
nominalBounds amount = G.allChecks
  [G.le (G.k minNominal) amount, G.le amount (G.k maxNominal)]

rateBounds :: (Assert t, TyC a) => t a Word128 -> t a ()
rateBounds rate = G.allChecks
  [L.le (L.ks (precision `div` 2)) rate >>> verify,
   L.le rate (L.ks (2 * precision)) >>> verify]

-- A fixed native enqueue conversion, corresponding to totalShares /
-- totalPooledEther = 3/4 in the source getSharesByPooledEth calculation.
requestShares :: Assert t => t Word64 Word64
requestShares = (konst (w8 2) &&& G.add (G.add iden iden) iden)
             >>> W.right_shift word8 word64

claimAmountRef :: Assert t => t (Word64, Word128) Word64
claimAmountRef = (bounds &&& iden) >>> drop
  ((iden &&& (oh >>> requestShares)) >>> G.select shouldDiscount discounted nominal)
 where
  bounds = G.allChecks [nominalBounds oh, rateBounds ih]
  nominal = take oh
  rate = take ih
  shares = S.u ih
  -- floor(nominal * E27 / shares) > rate holds exactly when
  -- nominal * E27 >= (rate + 1) * shares. At equality in the source
  -- comparison, return nominal, including a possible one-satoshi difference.
  shouldDiscount = (S.mul (S.add rate (L.ks 1)) shares
                 &&& S.mul (S.u nominal) (L.ks precision)) >>> A.le word128
  discounted = S.divide (S.mul rate shares) (L.ks precision) >>> S.narrow

claimWrapped :: J.WrappedSimplicity (Word64, Word128) Word64
claimWrapped = J.jetSubst claimAmountRef
{-# NOINLINE claimWrapped #-}

claimAmount :: Simplicity t => t (Word64, Word128) Word64
claimAmount = J.unwrap claimWrapped

requestSharesReference :: Integer -> Integer
requestSharesReference nominal = nominal * 3 `div` 4

-- Independent direct translation of the source's two integer divisions.
claimAmountReference :: Integer -> Integer -> Integer
claimAmountReference nominal maxRate
  | shareRate > maxRate = shares * maxRate `div` precision
  | otherwise = nominal
 where
  shares = requestSharesReference nominal
  shareRate = nominal * precision `div` shares
