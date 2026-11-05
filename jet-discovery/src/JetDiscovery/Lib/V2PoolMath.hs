{-# LANGUAGE RankNTypes #-}
-- | Exact bounded multiplication, floor division and restoring floor sqrt.
module JetDiscovery.Lib.V2PoolMath (mul,divide,minimumT,sqrt44Ref,sqrt44) where

import Prelude hiding (drop,take,not,and,or)
import qualified Data.List as L
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (false,verify)
import qualified Simplicity.Programs.Word as W
import Simplicity.Term.Core
import Simplicity.Ty.Word (Word64,word64)
import qualified JetDiscovery.Corpus.ContractGrowth as G

mul :: (Assert t,TyC a) => t a Word64 -> t a Word64 -> t a Word64
mul x y = (x &&& y) >>> A.multiply word64 >>> ((G.same oh (G.k 0)) &&& ih) >>> ih

divide :: (Assert t,TyC a) => t a Word64 -> t a Word64 -> t a Word64
divide x y = (G.nonzero y &&& ((x &&& y) >>> A.div_mod word64 >>> oh)) >>> ih

minimumT :: (Assert t,TyC a) => t a Word64 -> t a Word64 -> t a Word64
minimumT x y = G.select ((x &&& y) >>> A.lt word64) x y

-- Restoring binary square root: consume 22 two-bit digits, most significant
-- first. Each trial either subtracts 4*root+1 and appends 1 or appends 0.
sqrt44Ref :: Assert t => t Word64 Word64
sqrt44Ref = (G.lt iden (G.k (2^44)) &&& (iden &&& (G.k 0 &&& G.k 0))) >>> ih >>> steps >>> ioh
 where
  steps = L.foldl' (>>>) iden [step i | i <- [21,20..0]]
  step i = (iden &&& remainder i) >>> (take oh &&& (root &&& leftover))
  digit i = ((oh >>> W.shift_const_by false word64 (negate (2*i))) &&& G.k 3) >>> W.bitwise_and word64
  remainder i = G.add (iih >>> W.shift_const_by false word64 2) (digit i)
  trial = G.add (take ioh >>> W.shift_const_by false word64 2) (G.k 1)
  decision = (trial &&& ih) >>> A.le word64
  shiftRoot = take ioh >>> W.shift_const_by false word64 1
  root = G.select decision (G.add shiftRoot (G.k 1)) shiftRoot
  leftover = G.select decision (G.sub ih trial) ih

{-# NOINLINE sqrtWrapped #-}
sqrtWrapped :: J.WrappedSimplicity Word64 Word64
sqrtWrapped = J.jetSubst sqrt44Ref

sqrt44 :: Simplicity t => t Word64 Word64
sqrt44 = J.unwrap sqrtWrapped
