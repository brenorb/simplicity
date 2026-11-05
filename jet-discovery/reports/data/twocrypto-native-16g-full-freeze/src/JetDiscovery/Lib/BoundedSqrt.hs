{-# LANGUAGE ScopedTypeVariables #-}
-- | Integer floor sqrt for128-bit unsigned input,64 restoring digit steps.
-- This independently implements the integer square-root operation referenced
-- by DODO SafeMath.sqrt; it does not execute downloaded Solidity.
module JetDiscovery.Lib.BoundedSqrt where
import Prelude hiding (drop,take,not,and,or)
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.StableMath as S
import qualified JetDiscovery.Corpus.ContractGrowth as G

sqrt128 :: Assert t => t Word128 Word64
sqrt128=(iden&&&(konst (w64 0)&&&S.k 0))>>>steps>>>ioh
 where
  pair i=((oh>>>W.shift_const_by false word128 (negate (2*(63-i))))&&&S.k 3)>>>W.bitwise_and word128
  remainder i=S.add (iih>>>W.shift_const_by false word128 2) (pair i)
  trial=S.add (S.u (take ioh)>>>W.shift_const_by false word128 2) (S.k 1)
  decision=(trial&&&ih)>>>A.le word128
  shiftedRoot=take ioh>>>W.shift_const_by false word64 1
  root=(decision&&&iden)>>>cond (G.add shiftedRoot (G.k 1)) shiftedRoot
  rem=(decision&&&iden)>>>cond (S.sub ih trial) ih
  step i=(iden&&&remainder i)>>>(take oh&&&(root&&&rem))
  steps=L.foldl' (>>>) iden [step i|i<-[0..63]]

sqrtInteger x|x<0=error "negative integer sqrt"|x<2=x|x<4=1|otherwise=go x (x `div`2+1)
 where go old next|next>=old=old|otherwise=go next ((x `div`next+next) `div`2)

-- Full uint256 input for DODO's target quadratic. All128 source digit pairs
-- are consumed; the result is the exact128-bit floor root, with no hint.
sqrt256 :: Assert t => t Word256 Word128
sqrt256=(iden&&&(S.k 0&&&konst (w256 0)))>>>steps>>>ioh
 where
  k n=konst (w256 n)
  add a b=(a&&&b)>>>A.add word256>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
  sub a b=(a&&&b)>>>A.subtract word256>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
  pair i=((oh>>>W.shift_const_by false word256 (negate (2*(127-i))))&&&k 3)>>>W.bitwise_and word256
  remainder i=add (iih>>>W.shift_const_by false word256 2) (pair i)
  trial=add ((S.k 0&&&take ioh)>>>W.shift_const_by false word256 2) (k 1)
  decision=(trial&&&ih)>>>A.le word256
  shiftedRoot=take ioh>>>W.shift_const_by false word128 1
  root=(decision&&&iden)>>>cond (S.add shiftedRoot (S.k 1)) shiftedRoot
  rem=(decision&&&iden)>>>cond (sub ih trial) ih
  step i=(iden&&&remainder i)>>>(take oh&&&(root&&&rem))
  steps=L.foldl' (>>>) iden [step i|i<-[0..127]]
