{-# LANGUAGE ScopedTypeVariables #-}
-- | Exact fixed-k0.1 DODO quadratic/integral math, derived from pinned
-- DODOMath.sol (Apache2.0). Native balances/targets are bounded by the caller;
-- checked128-bit outputs and full256-bit products fail instead of wrapping.
module JetDiscovery.Lib.DodoMath where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import Simplicity.Term.Core hiding (one)
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.StableMath as S
import qualified JetDiscovery.Lib.BoundedSqrt as Q
import qualified JetDiscovery.Corpus.ContractGrowth as G

one,kappa :: Integer
one=10^18
kappa=10^17
select p a b=(p&&&iden)>>>cond a b
same a b=(a&&&b)>>>eq>>>verify
nonzero a=(a&&&L.ks 0)>>>eq>>>not iden>>>verify
up128 a b d=((a&&&b)&&&d)>>>L.fullQR>>>select ((ih&&&L.ks 0)>>>eq) oh (L.add oh (L.ks 1))
wideDiv :: Assert t => t ((Word128,Word128),Word128) Word256
wideDiv=((nonzero ih)&&&iden)>>>drop ((take (A.multiply word128)&&&(L.ks 0&&&ih))>>>A.divide word256)
add256 a b=(a&&&b)>>>A.add word256>>>((oh>>>not iden>>>verify)&&&ih)>>>ih
-- V1,delta,i. Fixed0<k<1 branch of _SolveQuadraticFunctionForTarget.
type TargetInput=(Word64,(Word64,Word64))
targetRef :: Assert t => t TargetInput Word64
targetRef=select ((oh&&&konst (w64 0))>>>eq) (konst (w64 0)) ((iden&&&root)>>>L.mdiv (L.u64 (take oh)) premium (L.ks one)>>>S.narrow)
 where
  ki=S.mul (L.ks (4*kappa)) (L.u64 iih)
  square=((ki&&&L.u64 ioh)&&&L.u64 oh)>>>wideDiv
  root=(add256 square (L.ks 0&&&L.ks (one*one)))>>>Q.sqrt256
  premium=L.add (L.ks one) (L.mdiv (L.sub ih (L.ks one)) (L.ks one) (L.ks (2*kappa)))
-- V0,V1,delta,i. Fixed0<k<1 branch of _SolveQuadraticFunctionForTrade.
type TradeInput=(Word64,(Word64,(Word64,Word64)))
tradeRef :: Assert t => t TradeInput Word64
tradeRef=(G.nonzero oh&&&iden)>>>drop (select ((iioh&&&konst (w64 0))>>>eq) (konst (w64 0)) calculate)
 where
  part1=S.mul (L.ks (one-kappa)) (L.u64 ioh)
  part2=L.add (S.mul (L.divide (S.mul (L.ks kappa) (L.u64 oh)) (L.u64 ioh)) (L.u64 oh)) (S.mul (L.u64 iiih) (L.u64 iioh))
  negative=L.lt ioh iih
  bAbs=L.divide (select negative (L.sub iih ioh) (L.sub ioh iih)) (L.ks one)
  curve=L.mdiv (L.ks (4*(one-kappa))) (S.mul (L.mdiv (L.ks kappa) (L.u64 oh) (L.ks one)) (L.u64 oh)) (L.ks one)
  root=L.add (S.mul iih iih) (take curve)>>>Q.sqrt128>>>L.u64 iden
  numerator=select (take ioh) ((L.sub ih (take iih))>>>((nonzero iden)&&&iden)>>>ih) (L.add (take iih) ih)
  v2=up128 numerator (L.ks one) (L.ks (2*(one-kappa)))
  oldV1=L.u64 (take (take (take ioh)))
  calculate=(iden&&&(part1&&&part2))>>>(take iden&&&(negative&&&bAbs))>>>(iden&&&root)>>>(iden&&&v2)>>>select (L.lt oldV1 ih) (L.ks 0) (L.sub oldV1 ih)>>>S.narrow
-- V0,V1,V2,i. Full GeneralIntegrate with its required intermediate floors.
type IntegralInput=(Word64,(Word64,(Word64,Word64)))
integrateRef :: Assert t => t IntegralInput Word64
integrateRef=(G.nonzero oh&&&iden)>>>drop (L.mdiv factor fair (L.ks (one*one))>>>S.narrow)
 where
  fair=S.mul (L.u64 iiih) (L.sub (L.u64 ioh) (L.u64 iioh))
  ratio=L.mdiv (L.divide (S.mul (L.u64 oh) (L.u64 oh)) (L.u64 ioh)) (L.ks one) (L.u64 iioh)
  factor=L.add (L.ks (one-kappa)) (L.mdiv (L.ks kappa) ratio (L.ks one))

-- Independent Integer translations, with integer sqrt independently checked
-- against dense and maximum-width cases in CheckBoundedSqrt.
targetInteger v delta price
 |v==0=0
 |otherwise=v*premium `div`one
 where
  square=4*kappa*price*delta `div`v+one*one
  root=Q.sqrtInteger square
  premium=(root-one)*one `div`(2*kappa)+one
tradeInteger v0 v1 delta price
 |v0<=0=error "DODO zero target"
 |delta==0=0
 |otherwise=if v2>v1 then 0 else v1-v2
 where
  p1=(one-kappa)*v1;p2=(kappa*v0 `div`v1)*v0+price*delta
  b=abs (p1-p2) `div`one
  curve=(4*(one-kappa))*((kappa*v0 `div`one)*v0) `div`one
  root=Q.sqrtInteger (b*b+curve)
  numerator=if p2>p1 then root-b else b+root
  v2=if p2>p1&&numerator==0 then error "DODO zero numerator" else (numerator*one+2*(one-kappa)-1) `div`(2*(one-kappa))
integrateInteger v0 v1 v2 price=(((one-kappa)+kappa*ratio `div`one)*price*(v1-v2)) `div`(one*one)
 where ratio=(v0*v0 `div`v1)*one `div`v2
