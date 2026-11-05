-- | Complete two-band traversal for initialized tick map {-120,0,120}.
-- Price limits stay strictly inside the endpoints. The only crossable tick
-- is zero, so two source SwapMath steps exhaust the supported traversal.
module JetDiscovery.Lib.V3FiniteSwap where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import Simplicity.Ty.Word
import qualified JetDiscovery.Lib.ClaimLedger as C
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.V3BoundedMath as V

lower,upper :: Integer
lower=78754240422856966435523493930 -- TickMath(-120)
upper=79704936542881920863903188246 -- TickMath(120)
type Input=((Word128,Word128),((Word64,Word64),(Bit,(Bit,Word64))))
type Output=(Word128,(Bit,(Word64,(Word64,(Word128,Word128)))))
-- prices=current,limit; liquidities=left,right; flags=left,exactInput,quantity
cur,limit :: Core t => t Input Word128
cur=ooh;limit=oih
leftL,rightL :: Core t => t Input Word64
leftL=drop (take oh);rightL=drop (take ih)
left,exact :: Core t => t Input Bit
left=drop (drop oh);exact=drop (drop (drop oh))
quantity :: Core t => t Input Word64
quantity=drop (drop (drop ih))
inside price=C.allChecks [L.lt (L.ks lower) price>>>verify,L.lt price (L.ks upper)>>>verify]
sideConsistent p side=C.select side (L.le p (L.ks V.q96)>>>verify) (L.le (L.ks V.q96) p>>>verify)
stepPrice t=t>>>oh
stepIn t=t>>>ioh
stepOut t=t>>>iioh
stepFee t=t>>>iiih
paid t=C.add (stepIn t) (stepFee t)

fillRef :: Simplicity t => t Input Output
fillRef=V.guarded checks ((iden&&&crossIntent)>>>(iden&&&firstStep)>>>(iden&&&(crossed&&&leftover))>>>(iden&&&secondStep)>>>(iden&&&(firstGrowth&&&secondGrowth))>>>finish)
 where
  checks=C.allChecks [inside cur,inside limit,sideConsistent cur left,C.is cur limit>>>not iden>>>verify,C.nonzero quantity,C.le quantity (C.k (10^9))]
  down=L.lt limit cur
  crossIntent=C.select down (and (not left) (L.le limit (L.ks V.q96))) (and left (L.le (L.ks V.q96) limit))
  activeL=C.select left leftL rightL
  oppositeL=C.select left rightL leftL
  -- A=(Input,crossIntent), B=(A,firstStep).
  firstTarget=C.select ih (L.ks V.q96) (take limit)
  firstStep=((take cur&&&firstTarget)&&&(take activeL&&&(take exact&&&take quantity)))>>>V.swapStep
  crossed=and (take ih) (C.is (stepPrice ih) (L.ks V.q96))
  leftover=C.sub (take (take quantity)) (C.select (take (take exact)) (paid ih) (stepOut ih))
  -- C=(B,(crossed,remaining)); the post-cross liquidity is derived from the
  -- fixed complete map, never provided as a separate witness.
  firstC=take ih
  inputC f=take (take (take f))
  needSecond=and ioh (and (not (C.is iih (C.k 0))) (not (C.is (stepPrice firstC) (inputC limit))))
  secondStep=C.select needSecond (((stepPrice firstC&&&inputC limit)&&&(inputC oppositeL&&&(inputC exact&&&iih)))>>>V.swapStep) (stepPrice firstC&&&(C.k 0&&&(C.k 0&&&C.k 0)))
  -- D=(C,secondStep); the two growths are staged once before allocation.
  firstD=take firstC
  firstGrowth=(stepFee firstD&&&take (inputC activeL))>>>V.feeGrowth
  secondGrowth=(stepFee ih&&&take (inputC oppositeL))>>>V.feeGrowth
  -- E=(D,(growthFirst,growthSecond)).
  firstE=take firstD;secondE=take ih
  oldLeft=take (take (inputC left))
  newLeft=C.select (take (take ioh)) (not oldLeft) oldLeft
  allocate=C.select oldLeft ih (iih&&&ioh)
  finish=stepPrice secondE&&&(newLeft&&&(C.add (paid firstE) (paid secondE)&&&(C.add (stepOut firstE) (stepOut secondE)&&&allocate)))
fillWrapped :: J.WrappedSimplicity Input Output
fillWrapped=J.jetSubst fillRef
{-# NOINLINE fillWrapped #-}
fill :: Simplicity t => t Input Output
fill=J.unwrap fillWrapped

-- Source _modifyPosition token deltas: clamp the current price to the fixed
-- position endpoints, then compute the two source-rounded legs. At tick zero
-- either side convention yields the same amounts because one leg is zero.
type LpInput=(Word128,((Bit,Bit),Word64)) -- price,(leftRange,mintRoundUp),Ldelta
lpRef :: Simplicity t => t LpInput (Word64,Word64)
lpRef=(iden&&&C.select iooh (L.ks lower&&&L.ks V.q96) (L.ks V.q96&&&L.ks upper))>>>(iden&&&clamped)>>>C.select (take (take ioih)) (legs True) (legs False)
 where
  clamped=(ioh&&&((take oh&&&iih)>>>A.min word128))>>>A.max word128
  liq=take (take iih)
  legs up=((ih&&&(take iih&&&liq))>>>V.amountDelta True up)&&&((take ioh&&&(ih&&&liq))>>>V.amountDelta False up)
lpWrapped :: J.WrappedSimplicity LpInput (Word64,Word64)
lpWrapped=J.jetSubst lpRef
{-# NOINLINE lpWrapped #-}
lpAmounts :: Simplicity t => t LpInput (Word64,Word64)
lpAmounts=J.unwrap lpWrapped
lpInteger price leftRange roundUp liquidity=(V.deltaInteger True roundUp clipped high liquidity,V.deltaInteger False roundUp low clipped liquidity)
 where
  (low,high)=if leftRange then (lower,V.q96) else (V.q96,upper)
  clipped=max low (min high price)

fillInteger cur limit l0 l1 left exactIn quantity=(p2,newLeft,in1+fee1+in2+fee2,out1+out2,g0,g1)
 where
  down=cur>limit
  intend=if down then H.not left&&limit<=V.q96 else left&&limit>=V.q96
  target1=if intend then V.q96 else limit
  active=if left then l0 else l1
  opposite=if left then l1 else l0
  (p1,in1,out1,fee1)=V.stepInteger cur target1 active exactIn quantity
  crossed=intend&&p1==V.q96
  remaining=quantity-(if exactIn then in1+fee1 else out1)
  (p2,in2,out2,fee2)=if crossed&&remaining>0&&p1/=limit then V.stepInteger p1 limit opposite exactIn remaining else (p1,0,0,0)
  newLeft=if crossed then H.not left else left
  g a liquidity=if a==0 then 0 else a*V.q128 `div`liquidity
  (g0,g1)=if left then (g fee1 active,g fee2 opposite) else (g fee2 opposite,g fee1 active)
