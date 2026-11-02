-- | DeFi arithmetic kernel: Uniswap v2's getAmountOut with 112-bit reserves,
-- which needs 128x128-bit multiplication and 256-bit division.  Bitcoin has no
-- native tokens, so this is an arithmetic kernel, not a contract port.
module JetDiscovery.Corpus.DeFi
  ( entries
  ) where

import Prelude hiding (drop, take, not, and, or, subtract)

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes (konst)
import JetDiscovery.Tx
import JetDiscovery.Types

-- | amountOut = (in * 997 * reserveOut) / (reserveIn * 1000 + in * 997).
-- Input ((in, (reserveIn, reserveOut)), expected).
getAmountOut :: Assert term => term ((Word128, (Word128, Word128)), Word128) ()
getAmountOut = (take amountOut &&& ih) >>> eq >>> verify
 where
  k :: (Core term, TyC i) => Integer -> term i Word128
  k = konst . toWord128
  low = ih  -- low half of a double-width product (no overflow for 112-bit operands)
  inFee = (oh &&& k 997) >>> Arith.multiply word128 >>> low
  num = (inFee &&& iih) >>> Arith.multiply word128
  den = ((ioh &&& k 1000 >>> Arith.multiply word128 >>> low) &&& inFee) >>> Arith.add word128 >>> ih
  amountOut = (num &&& (k 0 &&& den)) >>> Arith.div_mod word256 >>> oh >>> ih

ref :: Integer -> Integer -> Integer -> Integer
ref i rIn rOut = (i * 997 * rOut) `div` (rIn * 1000 + i * 997)

entries :: [Entry]
entries =
  [ Entry
    { entryId = "xchain-uniswap-v2-amount-out"
    , entryTitle = "Uniswap v2 getAmountOut (128x128 multiply, 256-bit division)"
    , entrySpec = "Uniswap v2 UniswapV2Library.getAmountOut (0.3% fee)"
    , entryCategory = CrossChain
    , entryVectorSource = Derived "expected values from Haskell Integer arithmetic"
    , entryAssumptions = ["reserves and input below 2^112 (Uniswap v2's reserve width)", "operands and expected output are witness data"]
    , entryProgram = \((i, (a, b)), o) -> Prog (witness ((toWord128 i, (toWord128 a, toWord128 b)), toWord128 o) >>> getAmountOut)
    , entryVectors =
        [ Vector ("in " ++ show i ++ ", reserves " ++ show (a, b)) env ((i, (a, b)), ref i a b) Accept | (i, a, b) <- cases ] ++
        [ Vector "output one unit too large" env ((10 ^ 18, (10 ^ 21, 2 * 10 ^ 9)), ref (10 ^ 18) (10 ^ 21) (2 * 10 ^ 9) + 1) Reject ]
    }
  ]
 where
  env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  big = 2 ^ (112 :: Int) - 1
  cases = [(10 ^ 18, 10 ^ 21, 2 * 10 ^ 9), (1, 1000, 1000), (big, big, big), (12345678901234567, 98765432109876543210, 5555555555)]
