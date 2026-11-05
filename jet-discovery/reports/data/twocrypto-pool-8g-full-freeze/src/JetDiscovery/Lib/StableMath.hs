{-# LANGUAGE ScopedTypeVariables #-}
-- | Curve3pool integer Newton arithmetic at A100, three equal native units.
-- Balances are positive and <=1e9; checked128-bit intermediates reject overflow.
-- Unlike the earlier D-only component, get_y is included for real pool swaps.
module JetDiscovery.Lib.StableMath where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import qualified Data.List as L
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes

type Bal=(Word64,(Word64,Word64))
k :: (Core t,TyC a) => Integer -> t a Word128
k=konst . toWord128
u a=konst (w64 0)&&&a
add a b=(a&&&b)>>>A.add word128>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
sub a b=(a&&&b)>>>A.subtract word128>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
mul a b=(a&&&b)>>>A.multiply word128>>>((((oh&&&k 0)>>>eq>>>verify)&&&ih)>>>ih)
divide a b=((b&&&k 0)>>>eq>>>not iden>>>verify)&&&((a&&&b)>>>A.divide word128)>>>ih
sumB :: Assert t => t Bal Word128
sumB=add (u oh) (add (u ioh) (u iih))
fits64 :: Assert t => t Word128 ()
fits64=(oh&&&konst (w64 0))>>>eq>>>verify
narrow :: Assert t => t Word128 Word64
narrow=(fits64&&&ih)>>>ih
close a b=(((a&&&b)>>>A.max word128)&&&((a&&&b)>>>A.min word128))>>>A.subtract word128>>>ih>>>(iden&&&k 1)>>>A.le word128
newtonD :: Assert t => t (Bal,Word128) Word128
newtonD=(iden&&&ih)>>>dp oh>>>dp ioh>>>dp iih>>>next
 where
  dp balance=oh&&&divide (mul ih oih) (mul (u (take (take balance))) (k 3))
  numerator=mul (add (mul (take (take sumB)) (k 300)) (mul ih (k 3))) oih
  denominator=add (mul oih (k 299)) (mul ih (k 4))
  next=divide numerator denominator
curveDRefT :: Assert t => t Bal Word64
curveDRefT=(checks&&&iden)>>>drop (start>>>loops>>>done)
 where
  checks=H.foldl (\a b->(a&&&b)>>>unit) unit [((x&&&konst (w64 0))>>>eq>>>not iden>>>verify)&&&((x&&&konst (w64 (10^9)))>>>A.le word64>>>verify)>>>unit|x<-[oh,ioh,iih]]
  start=iden&&&(sumB&&&false)
  update=(iden&&&((oh&&&ioh)>>>newtonD))>>>(take oh&&&(ih&&&close (take ioh) ih))
  step=(iih&&&iden)>>>cond iden update
  loops=L.foldl' (>>>) iden (replicate 32 step)
  done=(iih>>>verify)&&&(ioh>>>narrow)>>>ih
curveDWrapped :: J.WrappedSimplicity Bal Word64
curveDWrapped=J.jetSubst curveDRefT
{-# NOINLINE curveDWrapped #-}
curveD :: Simplicity t => t Bal Word64
curveD=J.unwrap curveDWrapped
-- D, replacement input balance, remaining third balance. The target balance is
-- not provided as a hint; all32 get_y iterations execute/freeze inside Simplicity.
type YInput=(Word64,(Word64,Word64))
curveYRefT :: Assert t => t YInput Word64
curveYRefT=(bounds&&&iden)>>>drop ((iden&&&u oh)>>>cStep (take ioh)>>>cStep (take iih)>>>lastC>>>parameters>>>start>>>loops>>>done)
 where
  bounds=H.foldl (\a b->(a&&&b)>>>unit) unit [((x&&&konst (w64 0))>>>eq>>>not iden>>>verify)|x<-[oh,ioh,iih]]
  cStep balance=oh&&&divide (mul ih (u (take oh))) (mul (u balance) (k 3))
  lastC=oh&&&divide (mul ih (u (take oh))) (k 900)
  b=add (add (u (take ioh)) (u (take iih))) (divide (u (take oh)) (k 300))
  parameters=ih&&&(b&&&u (take oh))
  start=iden&&&(iih&&&false)
  y=ioh;c=take oh;bb=take (drop oh);d=take (drop ih)
  next=divide (add (mul y y) c) (sub (add (mul y (k 2)) bb) d)
  update=(iden&&&next)>>>(take oh&&&(ih&&&close (take ioh) ih))
  step=(iih&&&iden)>>>cond iden update
  loops=L.foldl' (>>>) iden (replicate 32 step)
  done=(iih>>>verify)&&&(ioh>>>narrow)>>>ih
curveYWrapped :: J.WrappedSimplicity YInput Word64
curveYWrapped=J.jetSubst curveYRefT
{-# NOINLINE curveYWrapped #-}
curveY :: Simplicity t => t YInput Word64
curveY=J.unwrap curveYWrapped

curveDInteger xs=go 255 (H.sum xs)
 where
  go 0 _=error "CurveD did not converge"
  go n d=let {dp=H.foldl (\p x->p*d `div`(3*x)) d xs;z=(300*H.sum xs+3*dp)*d `div`(299*d+4*dp)} in if abs (z-d)<=1 then z else go (n-1) z
curveYInteger d x other=go 255 d
 where
  c0=d*d `div`(3*x);c1=c0*d `div`(3*other);c=c1*d `div`900;b=x+other+d `div`300
  go 0 _=error "CurveY did not converge"
  go n y=let z=(y*y+c) `div`(2*y+b-d) in if abs (z-y)<=1 then z else go (n-1) z
