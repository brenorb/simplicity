{-# LANGUAGE ScopedTypeVariables #-}
-- | Bounded integer TwoCrypto NG invariant and the proven Newton fallback.
module JetDiscovery.Lib.TwoCryptoMath
  ( Balances, normalize, invariant, fallbackRatio, getY, dynamicFee, spotBound ) where

import Prelude hiding (drop,take)
import qualified Data.List as L
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (Bit,false,verify)
import Simplicity.Term.Core
import Simplicity.Ty.Word
import qualified JetDiscovery.Lib.BoundedSqrt as Sqrt
import JetDiscovery.Lib.TwoCryptoArithmetic
import qualified JetDiscovery.Ref.TwoCrypto as Ref

type Balances = (Word64,Word64)

normalize :: Assert t => t Balances Balances
normalize = scaled oh&&&scaled ih
 where scaled v = product64 v (word Ref.precision)>>>narrow

validBalance :: Assert t => t Word64 ()
validBalance = checks [le (word (Ref.minReserve*Ref.precision)) iden,
                      le iden (word (Ref.maxReserve*Ref.precision))]

validD :: Assert t => t Word64 ()
validD = checks [le (word (10^17)) iden,le iden (word (8*Ref.wad))]

{-# NOINLINE sqrtWrapped #-}
sqrtWrapped :: J.WrappedSimplicity Word128 Word64
sqrtWrapped = J.jetSubst Sqrt.sqrt128

mulOne :: (Simplicity t,TyC a) => t a Word64 -> t a Word64 -> t a Word128
mulOne d g = divideWide
  (scaleWide (divideWide (scaleWide (divideWide (product64 (word Ref.wad) d) (word Ref.gamma)) g)
                         (word Ref.gamma)) g)
  (word (Ref.ann `div` 10000))

g1 :: Assert t => t Word64 Word64
g1 = add (diff (word (Ref.wad+Ref.gamma)) iden) (word 1)

type DInputs = (Balances,Word64)
type DFactors = ((DInputs,Word64),(Word128,Word128))

dFactors :: Simplicity t => t (DInputs,Word64) DFactors
dFactors = (iden&&&(ih>>>g1))>>>
  (oh&&&(mulOne (ooh>>>ih) ih&&&divideWide (product64 (word (4*Ref.wad)) oih) ih))

dDerivative :: Simplicity t => t DFactors Word64
dDerivative = subWide
  (addWide (addWide (s>>>promote) (divideWide (scaleWide iih s) (word Ref.wad)))
           (divideWide (scaleWide ioh (word 2)) oih))
  (divideWide (scaleWide iih (ooh>>>ih)) (word Ref.wad))>>>narrow
 where s = ooh>>>oh>>>add oh ih

dUpdate :: Simplicity t => t (DFactors,Word64) Word64
dUpdate = (plus&&&minus)>>>select ((ih&&&oh)>>>A.lt word64) (sub oh ih)
  (quotient (sub ih oh) (word 2))
 where
  d = oh>>>ooh>>>ih
  s = oh>>>ooh>>>oh>>>add oh ih
  k0 = oh>>>oih
  m1 = oh>>>ioh
  plus = ratio d (add ih s) ih
  base = ratio d d ih
  correction = ratio (ratio d (divideWide m1 ih>>>narrow) (word Ref.wad)) (diff (word Ref.wad) k0) k0
  minus = select ((k0&&&word Ref.wad)>>>A.lt word64) (add base correction) (sub base correction)

dStep :: Simplicity t => t DInputs Word64
dStep = checked (ih>>>validD)
  (iden&&&ratio (ratio (word (4*Ref.wad)) ooh ih) oih ih)>>>
  dFactors>>>(iden&&&dDerivative)>>>dUpdate

{-# NOINLINE dStepWrapped #-}
dStepWrapped :: J.WrappedSimplicity DInputs Word64
dStepWrapped = J.jetSubst dStep

type DLoop = (Balances,(Word64,Bit))

startD :: Simplicity t => t Balances DLoop
startD = ordered>>>checked (checks [oh>>>validBalance,ih>>>validBalance,
    le (word (10^14)) (ratio ih (word Ref.wad) oh)])
  (iden&&&((product64 oh ih>>>J.unwrap sqrtWrapped>>>add iden iden)&&&false))
 where ordered = select ((oh&&&ih)>>>A.le word64) (ih&&&oh) iden

advanceD :: Simplicity t => t DLoop DLoop
advanceD = select iih iden ((iden&&&((oh&&&ioh)>>>J.unwrap dStepWrapped))>>>update)
 where
  update = ooh&&&(ih&&&converged)
  converged = (product64 (diff (oh>>>ioh) ih) (word (10^14))&&&
               ((ih&&&word (10^16))>>>A.max word64>>>promote))>>>A.lt word128

-- The upper source fraction bound exceeds Word64. An admissible projection
-- must already fit Word64 in the checked ratio above, so its upper comparison
-- is discharged in the narrowed type.
invariantRef :: Simplicity t => t Balances Word64
invariantRef = startD>>>L.foldl' (>>>) iden (replicate Ref.maxSteps advanceD)>>>
  checked (checks [iih>>>verify,ioh>>>validD,frac ooh,frac oih]) ioh
 where frac x = le (word (5*10^15)) (ratio x (word Ref.wad) ioh)

{-# NOINLINE invariantWrapped #-}
invariantWrapped :: J.WrappedSimplicity Balances Word64
invariantWrapped = J.jetSubst invariantRef

invariant :: Simplicity t => t Balances Word64
invariant = J.unwrap invariantWrapped

-- Source get_y's discriminant is strictly negative throughout this exact
-- ratio band for the pinned ANN and gamma. See check_twocrypto_profile.py.
fallbackRatio :: Assert t => t (Word64,Word64) ()
fallbackRatio = checks
  [ (product64 (word 45) oh&&&product64 (word 100) ih)>>>A.le word128>>>verify
  , (product64 (word 100) ih&&&product64 (word 55) oh)>>>A.le word128>>>verify
  ]

type YParams = (Word64,(Word64,Word64)) -- D, other balance, K0_i
type YInputs = (YParams,Word64)
type YFactors = ((YInputs,Word64),(Word128,Word128))
type YLoop = (YParams,(Word64,Bit))

yFactors :: Simplicity t => t (YInputs,Word64) YFactors
yFactors = (iden&&&(ih>>>g1))>>>
  (oh&&&(mulOne (ooh>>>ooh) ih&&&
        addWide (wide Ref.wad) (divideWide (product64 (word (2*Ref.wad)) oih) ih)))

ySlope :: Simplicity t => t YFactors (Word128,Word128)
ySlope = addWide (addWide (product64 (word Ref.wad) y) (scaleWide iih (add x y))) ioh
          &&& scaleWide iih d
 where
  d = ooh>>>ooh
  x = ooh>>>oioh
  y = ooh>>>ih

yStep :: Simplicity t => t YInputs (Word64,Bit)
yStep = checked (positive ih)
  (iden&&&ratio (add oiih oiih) ih ooh)>>>yFactors>>>(iden&&&ySlope)>>>
  select ((ioh&&&iih)>>>A.lt word128) (quotient prior (word 2)&&&false) normalStep
 where
  prior = oh>>>ooh>>>ih
  normalStep = (oh&&&subWide ioh iih)>>>
    (iden&&&(divideWide ih (oh>>>ooh>>>ih)>>>narrow))>>>
    (iden&&&(divideWide (ooh>>>ioh) ih>>>narrow))>>>
    (iden&&&newValue)>>>stopped
  -- (factor context and wide yfprime, fprime), first term of y_minus
  newValue = (plus&&&minus&&&oldY)>>>select ((oh&&&ioh)>>>A.lt word64)
    (quotient iih (word 2)) (sub oh ioh)
   where
    fact = ooh>>>oh
    f = oih
    d = fact>>>ooh>>>ooh
    x = fact>>>ooh>>>oioh
    oldY = fact>>>ooh>>>ih
    k0 = fact>>>oih
    base = ih
    plus = add (divideWide (addWide (ooh>>>ih) (product64 (word Ref.wad) d)) f>>>narrow)
               (ratio base (word Ref.wad) k0)
    minus = add base (ratio (word Ref.wad) (add x oldY) f)
  stopped = ih&&&((diff oldY ih&&&limit)>>>A.lt word64)
   where
    args = oh>>>ooh>>>oh>>>ooh
    oldY = args>>>ih
    d = args>>>ooh
    x = args>>>oioh
    limit = L.foldl' (\a b -> (a&&&b)>>>A.max word64) (word 100)
      [quotient v (word (10^14)) | v<-[d,x,ih]]

{-# NOINLINE yStepWrapped #-}
yStepWrapped :: J.WrappedSimplicity YInputs (Word64,Bit)
yStepWrapped = J.jetSubst yStep

getYRef :: Simplicity t => t (Word64,Word64) Word64
getYRef = checked (checks [fallbackRatio,oh>>>validD,ih>>>validBalance])
  ((oh&&&(ih&&&ratio (word (2*Ref.wad)) ih oh))&&&
   (ratio oh oh (add (add ih ih) (add ih ih))&&&false))>>>
  L.foldl' (>>>) iden (replicate Ref.maxSteps step)>>>
  checked (checks [iih>>>verify,positive ioh]) ioh
 where step = select iih iden (oh&&&((oh&&&ioh)>>>J.unwrap yStepWrapped))

{-# NOINLINE getYWrapped #-}
getYWrapped :: J.WrappedSimplicity (Word64,Word64) Word64
getYWrapped = J.jetSubst getYRef

getY :: Simplicity t => t (Word64,Word64) Word64
getY = J.unwrap getYWrapped

feeRef :: Simplicity t => t Balances Word64
feeRef = (iden&&&add oh ih)>>>
  ratio (ratio (word (4*Ref.wad)) ooh ih) oih ih>>>
  ratio (word (10^16)) iden (sub (add (ratio (word (10^16)) iden (word Ref.wad)) (word Ref.wad)) iden)>>>
  (addWide (product64 (word 30000000) iden) (product64 (word 50000000) (sub (word Ref.wad) iden)))>>>
  divideWide iden (word Ref.wad)>>>narrow

{-# NOINLINE feeWrapped #-}
feeWrapped :: J.WrappedSimplicity Balances Word64
feeWrapped = J.jetSubst feeRef

dynamicFee :: Simplicity t => t Balances Word64
dynamicFee = J.unwrap feeWrapped

spotBound :: Simplicity t => t (Balances,Word64) ()
spotBound = checked (checks [ooh>>>validBalance,oih>>>validBalance,ih>>>validD])
  (ratio (ratio (add (add ooh ooh) (add ooh ooh)) oih ih) (word Ref.wad) ih)>>>
  checks [le (word (95*Ref.wad `div` 100)) iden,lt iden (word (102*Ref.wad `div` 100))]
