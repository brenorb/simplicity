{-# LANGUAGE ScopedTypeVariables #-}
-- | Checked wide arithmetic used by the bounded TwoCrypto profile.
module JetDiscovery.Lib.TwoCryptoArithmetic
  ( word, wide, promote, narrow, checks, checked, select, equal, same
  , lt, le, positive, add, sub, diff, addWide, subWide
  , product64, scaleWide, divideWide, ratio, quotient
  ) where

import Prelude hiding (drop,not,take)
import qualified Data.List as L
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (Bit,cond,false,not,verify)
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Word as W
import Simplicity.Term.Core
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes (konst,w64)

word :: (Core t,TyC a) => Integer -> t a Word64
word = konst . w64

wide :: (Core t,TyC a) => Integer -> t a Word128
wide = konst . toWord128

promote :: Core t => t Word64 Word128
promote = word 0&&&iden

narrow :: Assert t => t Word128 Word64
narrow = checked (same oh (word 0)) ih

checks :: (Core t,TyC a) => [t a ()] -> t a ()
checks = L.foldl' (\a b -> (a&&&b)>>>unit) unit

checked :: (Core t,TyC a,TyC b) => t a () -> t a b -> t a b
checked condition result = (condition&&&result)>>>ih

select :: (Core t,TyC a,TyC b) => t a Bit -> t a b -> t a b -> t a b
select predicate yes no = (predicate&&&iden)>>>cond yes no

equal :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a Bit
equal a b = (a&&&b)>>>eq

same :: (Assert t,TyC a,TyC b) => t a b -> t a b -> t a ()
same a b = equal a b>>>verify

lt,le :: (Assert t,TyC a) => t a Word64 -> t a Word64 -> t a ()
lt a b = (a&&&b)>>>A.lt word64>>>verify
le a b = (a&&&b)>>>A.le word64>>>verify

positive :: (Assert t,TyC a) => t a Word64 -> t a ()
positive = lt (word 0)

add,sub,diff :: (Assert t,TyC a) => t a Word64 -> t a Word64 -> t a Word64
add a b = (a&&&b)>>>A.add word64>>>checked (not oh>>>verify) ih
sub a b = (a&&&b)>>>A.subtract word64>>>checked (not oh>>>verify) ih
diff a b = select ((a&&&b)>>>A.le word64) (sub b a) (sub a b)

addWide,subWide :: (Assert t,TyC a) => t a Word128 -> t a Word128 -> t a Word128
addWide a b = (a&&&b)>>>A.add word128>>>checked (not oh>>>verify) ih
subWide a b = (a&&&b)>>>A.subtract word128>>>checked (not oh>>>verify) ih

product64 :: (Core t,TyC a) => t a Word64 -> t a Word64 -> t a Word128
product64 a b = (a&&&b)>>>A.multiply word64

scaleRef :: Assert t => t (Word128,Word64) Word128
scaleRef = (product64 ooh ih&&&product64 oih ih)>>>
  checked (same ooh (word 0)) (add oih ioh&&&iih)

{-# NOINLINE scaleWrapped #-}
scaleWrapped :: J.WrappedSimplicity (Word128,Word64) Word128
scaleWrapped = J.jetSubst scaleRef

scaleWide :: (Simplicity t,TyC a) => t a Word128 -> t a Word64 -> t a Word128
scaleWide a b = (a&&&b)>>>J.unwrap scaleWrapped

type Division = (Word128,Word64)

-- First divide the high limb. The remaining numerator has high limb below
-- the divisor. Left-shifting both by the same amount to set the divisor's
-- most significant bit preserves the exact low quotient and cannot overflow.
wideDivisionRef :: Assert t => t Division Word128
wideDivisionRef = checked (positive ih)
  (((ooh&&&ih)>>>A.div_mod word64)&&&(oih&&&ih))>>>
  (ooh&&&(((oih&&&ioh)&&&iih)>>>normalize>>>A.div2n1n word64>>>oh))
 where
  normalize = L.foldl' (>>>) iden (map shift [32,16,8,4,2,1])
  shift n = select ((ih&&&word (2^(64-n)))>>>A.lt word64)
    (take (W.shift_const_by false word128 n)&&&drop (W.shift_const_by false word64 n))
    iden

{-# NOINLINE wideDivisionWrapped #-}
wideDivisionWrapped :: J.WrappedSimplicity Division Word128
wideDivisionWrapped = J.jetSubst wideDivisionRef

divideWide :: (Simplicity t,TyC a) => t a Word128 -> t a Word64 -> t a Word128
divideWide n d = (n&&&d)>>>J.unwrap wideDivisionWrapped

ratio :: (Simplicity t,TyC a) => t a Word64 -> t a Word64 -> t a Word64 -> t a Word64
ratio a b d = divideWide (product64 a b) d>>>narrow

quotient :: (Assert t,TyC a) => t a Word64 -> t a Word64 -> t a Word64
quotient a b = checked (positive b) ((a&&&b)>>>A.divide word64)
