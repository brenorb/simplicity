{-# LANGUAGE ScopedTypeVariables #-}
-- | Balancer WeightedMath over a fixed80/20 native coupon pair. Source
-- FixedPoint powUp/powDown, ratio limits and join taxable-amount rounding run
-- inside Simplicity. Mathematical helper; no application count of its own.
module JetDiscovery.Lib.WeightedMath where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import Simplicity.Term.Core hiding (one)
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.StableMath as S
import qualified JetDiscovery.Corpus.ContractGrowth as G

one,w0,w1 :: Integer
one=10^18
w0=8*10^17
w1=2*10^17
select p a b=(p&&&iden)>>>cond a b
is a b=(a&&&b)>>>eq
k :: (Core t,TyC a) => Integer -> t a Word64
k=konst . w64
narrow :: Assert t => t Word128 Word64
narrow=S.narrow
up128 a b d=((a&&&b)&&&d)>>>L.fullQR>>>select (is ih (L.ks 0)) oh (L.add oh (L.ks 1))
-- ((balanceA,balanceB),(direction,amount)), direction0 is A->B.
type SwapInput=((Word64,Word64),(Word64,Word64))
zeroDir :: Core t => t SwapInput Bit
zeroDir=is ioh (k 0)
inBalance,outBalance :: Core t => t SwapInput Word64
inBalance=select zeroDir ooh oih
outBalance=select zeroDir oih ooh
netInput :: Simplicity t => t SwapInput Word64
netInput=G.sub iih (G.ceilRatio iih (k 3) (k 1000))
commonBounds :: Assert t => t SwapInput ()
commonBounds=G.allChecks [G.lt ioh (k 2),G.nonzero ooh,G.nonzero oih,G.le ooh (k (10^9)),G.le oih (k (10^9))]
swapInRef :: Simplicity t => t SwapInput (Word64,Word64)
swapInRef=(commonBounds&&&iden)>>>drop ((iden&&&netInput)>>>range>>>(iden&&&power)>>>(take (take iih)&&&amountOut))
 where
  range=(G.le ih (G.floorRatio (take inBalance) (k 3) (k 10))&&&iden)>>>drop iden
  base=up128 (L.u64 (take inBalance)) (L.ks one) (L.u64 (G.add (take inBalance) ih))
  exponent=select (take zeroDir) (k (4*one)) (k (one `div`4))
  power=(base&&&exponent)>>>L.powUp
  complement=select (L.lt ih (L.ks one)) (L.sub (L.ks one) ih) (L.ks 0)
  amountOut=L.mdiv (L.u64 (take (take outBalance))) complement (L.ks one)>>>narrow
swapOutRef :: Simplicity t => t SwapInput (Word64,Word64)
swapOutRef=(G.allChecks [commonBounds,G.le iih (G.floorRatio outBalance (k 3) (k 10))]&&&iden)>>>drop ((iden&&&power)>>>(amountIn&&&take iih))
 where
  base=up128 (L.u64 outBalance) (L.ks one) (L.u64 (G.sub outBalance iih))
  exponent=select zeroDir (k (one `div`4)) (k (4*one))
  power=(base&&&exponent)>>>L.powUp
  net=up128 (L.u64 (take inBalance)) (L.sub ih (L.ks one)) (L.ks one)
  amountIn=up128 net (L.ks 1000) (L.ks 997)>>>narrow
swapInWrapped,swapOutWrapped :: J.WrappedSimplicity SwapInput (Word64,Word64)
swapInWrapped=J.jetSubst swapInRef
swapOutWrapped=J.jetSubst swapOutRef
{-# NOINLINE swapInWrapped #-}
{-# NOINLINE swapOutWrapped #-}
invariantRef :: Simplicity t => t (Word64,Word64) Word64
invariantRef=((L.u64 oh&&&k w0)>>>L.powDown)&&&((L.u64 ih&&&k w1)>>>L.powDown)>>>L.mdiv oh ih (L.ks one)>>>narrow
invariantWrapped :: J.WrappedSimplicity (Word64,Word64) Word64
invariantWrapped=J.jetSubst invariantRef
{-# NOINLINE invariantWrapped #-}
type JoinInput=((Word64,Word64),((Word64,Word64),Word64))
-- LP initialization is an explicit native2*invariant policy. No foreign locked
-- minimum BPT or external Vault storage is assumed.
joinRef :: Simplicity t => t JoinInput Word64
joinRef=select (is iih (k 0)) initialize (normal>>>narrow)
 where
  old c=if c==0 then ooh else oih
  deposit c=if c==0 then drop (take oh) else drop (take ih)
  new c=G.add (old c) (deposit c)
  initialize=((new 0&&&new 1)>>>J.unwrap invariantWrapped)>>>(iden&&&iden)>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
  ratio c=L.mdiv (L.u64 (new c)) (L.ks one) (L.u64 (old c))
  ratios=ratio 0&&&ratio 1
  avg=L.add (L.mdiv ioh (L.ks w0) (L.ks one)) (L.mdiv iih (L.ks w1) (L.ks one))
  withoutFee c=select (L.lt ih r) (L.sub quantity fee) quantity
   where
    r=if c==0 then take ioh else take iih
    quantity=L.u64 (take (take (deposit c)))
    oldBalance=L.u64 (take (take (old c)))
    nonTaxable=select (L.lt (L.ks one) ih) (L.mdiv oldBalance (L.sub ih (L.ks one)) (L.ks one)) (L.ks 0)
    fee=up128 (L.sub quantity nonTaxable) (L.ks 3) (L.ks 1000)
  netAmounts=withoutFee 0&&&withoutFee 1
  net c=if c==0 then ioh else iih
  power c=select (is (net c) (L.ks 0)) (L.ks one) ((balanceRatio&&&k (if c==0 then w0 else w1))>>>L.powDown)
   where balanceRatio=L.mdiv (L.add (L.u64 (take (take (take (old c))))) (net c)) (L.ks one) (L.u64 (take (take (take (old c)))))
  invariantRatio=L.mdiv (power 0) (power 1) (L.ks one)
  normal=(iden&&&ratios)>>>(iden&&&avg)>>>(iden&&&netAmounts)>>>(iden&&&invariantRatio)>>>select (L.lt (L.ks one) ih) (L.mdiv (L.u64 (take (take (take (take iih))))) (L.sub ih (L.ks one)) (L.ks one)) (L.ks 0)
joinWrapped :: J.WrappedSimplicity JoinInput Word64
joinWrapped=J.jetSubst joinRef
{-# NOINLINE joinWrapped #-}

ceilDiv a b=(a+b-1) `div`b
powRounded up x y
 |y==one=x
 |y==2*one=rounded x x
 |y==4*one=let q=rounded x x in rounded q q
 |otherwise=let raw=L.powInteger x y;err=ceilDiv (raw*10000) one+1 in if up then raw+err else max 0 (raw-err)
 where rounded a b=if up then ceilDiv (a*b) one else a*b `div`one
invariantInteger a b=powRounded False a w0*powRounded False b w1 `div`one
swapInInteger a b direction amount=(amount,bo*max 0 (one-power) `div`one)
 where
  (bi,bo,wi,wo)=if direction==0 then (a,b,w0,w1) else (b,a,w1,w0)
  net=amount-ceilDiv (amount*3) 1000
  base=ceilDiv (bi*one) (bi+net);power=powRounded True base (wi*one `div`wo)
swapOutInteger a b direction amount=(ceilDiv (net*1000) 997,amount)
 where
  (bi,bo,wi,wo)=if direction==0 then (a,b,w0,w1) else (b,a,w1,w0)
  base=ceilDiv (bo*one) (bo-amount);power=powRounded True base (ceilDiv (wo*one) wi)
  net=ceilDiv (bi*(power-one)) one
joinInteger a b x y supply
 |supply==0=2*invariantInteger (a+x) (b+y)
 |otherwise=supply*max 0 (ratio-one) `div`one
 where
  avg=((a+x)*one `div`a)*w0 `div`one+((b+y)*one `div`b)*w1 `div`one
  net balance amount=if (balance+amount)*one `div`balance>avg then amount-ceilDiv ((amount-balance*max 0 (avg-one) `div`one)*3) 1000 else amount
  p balance amount weight=let n=net balance amount in if n==0 then one else powRounded False ((balance+n)*one `div`balance) weight
  ratio=p a x w0*p b y w1 `div`one
