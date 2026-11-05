{-# LANGUAGE ScopedTypeVariables #-}
-- | Bounded exact integer paths from Balancer LogExpMath (MIT, retained at
-- vendor-specs/contract-growth/*LogExpMath.sol with license/provenance).
-- This is not a floating approximation: decomposition constants,12 exp terms,
--6 ln terms,8 ln36 terms and signed truncation are preserved. Public bounds
-- specialize inputs to native pool demand, while every wide operation is checked.
module JetDiscovery.Lib.LogExpBounded where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes

type Signed=(Bit,Word128)
ks :: (Core t,TyC a) => Integer -> t a Word128
ks=konst . toWord128
select p a b=(p&&&iden)>>>cond a b
same a b=(a&&&b)>>>eq>>>verify
lt a b=(a&&&b)>>>A.lt word128
le a b=(a&&&b)>>>A.le word128
add a b=(a&&&b)>>>A.add word128>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
sub a b=(a&&&b)>>>A.subtract word128>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
divide a b=((b&&&ks 0)>>>eq>>>not iden>>>verify)&&&((a&&&b)>>>A.divide word128)>>>ih
fullMulDiv :: Assert t => t ((Word128,Word128),Word128) Word128
fullMulDiv=(nonzero&&&iden)>>>drop result
 where
  nonzero=(ih&&&ks 0)>>>eq>>>not iden>>>verify
  quotient=(take (A.multiply word128)&&&(ks 0&&&ih))>>>A.divide word256
  result=quotient>>>(((oh&&&ks 0)>>>eq>>>verify)&&&ih)>>>ih
fullQR :: Assert t => t ((Word128,Word128),Word128) (Word128,Word128)
fullQR=(nonzero&&&iden)>>>drop result
 where
  nonzero=(ih&&&ks 0)>>>eq>>>not iden>>>verify
  quotient=(take (A.multiply word128)&&&(ks 0&&&ih))>>>A.div_mod word256
  result=quotient>>>((same ooh (ks 0)&&&same ioh (ks 0))&&&(oih&&&iih))>>>ih
mdiv a b c=((a&&&b)&&&c)>>>fullMulDiv
mul a b=mdiv a b (ks 1)
u64 x=konst (w64 0)&&&x
ones=10^18
one20=10^20
one36=10^36
constants :: [(Integer,Integer)]
constants=[(3200000000000000000000,7896296018268069516100000000000000),(1600000000000000000000,888611052050787263676000000),(800000000000000000000,298095798704172827474000),(400000000000000000000,5459815003314423907810),(200000000000000000000,738905609893065022723),(100000000000000000000,271828182845904523536),(50000000000000000000,164872127070012814685),(25000000000000000000,128402541668774148407),(12500000000000000000,113314845306682631683),(6250000000000000000,106449445891785942956)]
-- z+z^3/3+... ; z has one sign throughout, represented as a magnitude.
oddSeries :: Assert t => Integer -> Int -> t Word128 Word128
oddSeries precision terms=((mdiv iden iden (ks precision))&&&(iden&&&iden))>>>steps>>>iih
 where
  next=mdiv ioh oh (ks precision)
  step denominator=(iden&&&next)>>>(take oh&&&(ih&&&add (take iih) (divide ih (ks (toInteger denominator)))))
  steps=L.foldl' (>>>) iden [step d|d<-[3,5..2*terms-1]]
lnPositive :: Assert t => t Word128 Word128
lnPositive=(mul iden (ks 100)&&&ks 0)>>>decompose>>>(ih&&&(oh>>>z>>>oddSeries one20 6))>>>divide (add oh (mul ih (ks 2))) (ks 100)
 where
  step (x,a)=select (le (ks a) oh) (mdiv oh (ks one20) (ks a)&&&add ih (ks x)) iden
  decompose=L.foldl' (>>>) iden (map step constants)
  z=mdiv (sub iden (ks one20)) (ks one20) (add iden (ks one20))
-- Exact near-one form, retaining the original scaled argument for x+ONE36.
ln36Exact :: Assert t => t Word128 Signed
ln36Exact=(lt iden (ks ones)&&&mul iden (ks ones))>>>(oh&&&mdiv difference (ks one36) (add ih (ks one36)))>>>(oh&&&(ih>>>oddSeries one36 8>>>mul iden (ks 2)))
 where difference=select oh (sub (ks one36) ih) (sub ih (ks one36))
ln18 :: Assert t => t Word128 Signed
ln18=(lt iden (ks ones)&&&iden)>>>(oh&&&(select oh (divide (ks one36) ih) ih>>>lnPositive))
near :: Assert t => t Word128 Bit
near=and (lt (ks (9*10^17)) iden) (lt iden (ks (11*10^17)))
lnRefT :: Assert t => t Word128 Signed
lnRefT=(bounds&&&iden)>>>drop (select near (ln36Exact>>>(oh&&&divide ih (ks ones))) ln18)
 where bounds=and (lt (ks 0) iden) (le iden (ks (3*ones)))>>>verify
expSeries :: Assert t => t Word128 Word128
expSeries=(iden&&&(iden&&&add (ks one20) iden))>>>steps>>>iih
 where
  step denominator=(iden&&&divide (mdiv ioh oh (ks one20)) (ks (toInteger denominator)))>>>(take oh&&&(ih&&&add (take iih) ih))
  steps=L.foldl' (>>>) iden [step d|d<-[2..12]]
expPositive :: Assert t => t Word128 Word128
expPositive=(mul iden (ks 100)&&&ks one20)>>>decompose>>>(iden&&&(oh>>>expSeries))>>>divide (mdiv (take ih) ih (ks one20)) (ks 100)
 where
  step (x,a)=select (le (ks x) oh) (sub oh (ks x)&&&mdiv ih (ks a) (ks one20)) iden
  decompose=L.foldl' (>>>) iden (map step (H.take 8 constants))
expRefT :: Assert t => t Signed Word128
expRefT=((le ih (ks (41*ones))>>>verify)&&&iden)>>>drop (oh&&&(ih>>>expPositive))>>>cond (divide (ks one36) iden) iden
powRefT :: Assert t => t (Word128,Word64) Word128
powRefT=(bounds&&&iden)>>>drop (select ((ih&&&konst (w64 0))>>>eq) (ks ones) (select ((oh&&&ks 0)>>>eq) (ks 0) power))
 where
  bounds=and (le oh (ks (3*ones))) ((ih&&&konst (w64 (4*ones)))>>>A.le word64)>>>verify
  power=select (oh>>>near) nearPower ordinaryPower
  ordinaryPower=(iden&&&(oh>>>ln18))>>>(ioh&&&mdiv iih (u64 (take ih)) (ks ones))>>>expRefT
  nearPower=(iden&&&(oh>>>ln36Exact))>>>(iden&&&((iih&&&ks ones)>>>A.div_mod word128))>>>product36>>>expRefT
  product36=take ioh&&&divide (add (mul ioh (u64 (take (take ih)))) (mdiv iih (u64 (take (take ih))) (ks ones))) (ks ones)
powWrapped :: J.WrappedSimplicity (Word128,Word64) Word128
powWrapped=J.jetSubst powRefT
{-# NOINLINE powWrapped #-}
powRaw :: Simplicity t => t (Word128,Word64) Word128
powRaw=J.unwrap powWrapped
-- FixedPoint source error envelope and optimized exponent1/2/4 paths.
powDown,powUp :: Simplicity t => t (Word128,Word64) Word128
powDown=powRounded False
powUp=powRounded True
powRounded :: Simplicity t => Bool -> t (Word128,Word64) Word128
powRounded up=select (sameY ones) oh (select (sameY (2*ones)) square (select (sameY (4*ones)) (square>>>squareOne) generic))
 where
  sameY value=(ih&&&konst (w64 value))>>>eq
  rounded a b=((a&&&b)&&&ks ones)>>>fullQR>>>select ((ih&&&ks 0)>>>eq) oh (if up then add oh (ks 1) else oh)
  square=rounded oh oh
  squareOne=rounded iden iden
  generic=powRaw>>>(iden&&&add (ceilError iden) (ks 1))>>>if up then add oh ih else select (lt oh ih) (ks 0) (sub oh ih)
  ceilError raw=divide (add (mul raw (ks 10000)) (ks (ones-1))) (ks ones)

-- Independent Integer reference, using the same published fixed-point floors.
oddInteger precision count z=snd (H.foldl step (z,z) [3,5..2*count-1])
 where z2=z*z `div`precision;step (num,total) d=let n=num*z2 `div`precision in (n,total+n `div`toInteger d)
lnPositiveInteger value=(total+2*oddInteger one20 6 z) `div`100
 where
  (a,total)=H.foldl step (value*100,0) constants
  step (x,s) (c,e)=if x>=e then (x*one20 `div`e,s+c) else (x,s)
  z=(a-one20)*one20 `div`(a+one20)
ln36Integer value=let x=value*ones;z=abs (x-one36)*one36 `div`(x+one36) in 2*oddInteger one36 8 z
lnInteger value=if value<ones then negate magnitude else magnitude
 where magnitude=if 9*10^17<value &&value<11*10^17 then ln36Integer value `div`ones else lnPositiveInteger (if value<ones then one36 `div`value else value)
expPositiveInteger value=(product*series `div`one20) `div`100
 where
  (x,product)=H.foldl step (value*100,one20) (H.take 8 constants)
  step (r,p) (c,e)=if r>=c then (r-c,p*e `div`one20) else (r,p)
  series=snd (H.foldl (\(term,s) d->let n=(term*x `div`one20) `div`d in (n,s+n)) (x,one20+x) [2..12])
expInteger value=if value<0 then one36 `div`expPositiveInteger (-value) else expPositiveInteger value
powInteger x y|y==0=ones|x==0=0|otherwise=expInteger (if x<ones then negate magnitude else magnitude)
 where
  nearOne=9*10^17<x&&x<11*10^17
  lnmag=if nearOne then ln36Integer x else abs (lnInteger x)
  magnitude=if nearOne then ((lnmag `div`ones)*y+(lnmag `mod`ones)*y `div`ones) `div`ones else lnmag*y `div`ones
