{-# LANGUAGE ScopedTypeVariables #-}
-- | Source-exact Uniswap V3 SqrtPriceMath/SwapMath on a finite price region.
-- Liquidity and amounts <=1e9, prices within1% of Q96; full256-bit products
-- where needed. The source's overflow fallback is unreachable on this domain.
module JetDiscovery.Lib.V3BoundedMath where
import Prelude hiding (drop,take,not,and,or)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import Simplicity.Ty.Word
import qualified JetDiscovery.Lib.ClaimLedger as C
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.StableMath as S
import qualified JetDiscovery.Corpus.ContractGrowth as G

q96,q128,feePips,feeDen :: Integer
q96=2^96
q128=2^128
feePips=3000
feeDen=10^6
priceLo,priceHi :: Integer
priceLo=q96*99 `div`100
priceHi=q96*101 `div`100
validPrice x=C.allChecks [L.le (L.ks priceLo) x>>>verify,L.le x (L.ks priceHi)>>>verify]
guarded p body=(p&&&iden)>>>drop body
ceil128 a b=L.divide (L.add a (L.sub b (L.ks 1))) b
mulUp a b d=((a&&&b)&&&d)>>>L.fullQR>>>C.select ((ih&&&L.ks 0)>>>eq) oh (L.add oh (L.ks 1))
liqQ96 a=S.mul (L.u64 a) (L.ks q96)

type Delta=(Word128,(Word128,Word64))
amountDeltaRef :: Assert t => Bool -> Bool -> t Delta Word64
amountDeltaRef token0 roundUp=guarded bounds (body>>>S.narrow)
 where
  bounds=C.allChecks [validPrice oh,validPrice ioh,C.le iih (C.k (10^9))]
  low=(oh&&&ioh)>>>A.min word128
  high=(oh&&&ioh)>>>A.max word128
  diff=L.sub high low
  -- Keep the source's two sequential divisions for token0; token1 needs
  -- only a checked128 product under the explicit liquidity/price bounds.
  body
   |token0&&roundUp=ceil128 (mulUp (liqQ96 iih) diff high) low
   |token0=L.divide (L.mdiv (liqQ96 iih) diff high) low
   |roundUp=ceil128 (S.mul (L.u64 iih) diff) (L.ks q96)
   |otherwise=L.divide (S.mul (L.u64 iih) diff) (L.ks q96)

amount0UpW,amount0DownW,amount1UpW,amount1DownW :: J.WrappedSimplicity Delta Word64
amount0UpW=J.jetSubst (amountDeltaRef True True)
amount0DownW=J.jetSubst (amountDeltaRef True False)
amount1UpW=J.jetSubst (amountDeltaRef False True)
amount1DownW=J.jetSubst (amountDeltaRef False False)
{-# NOINLINE amount0UpW #-}
{-# NOINLINE amount0DownW #-}
{-# NOINLINE amount1UpW #-}
{-# NOINLINE amount1DownW #-}
amountDelta :: Simplicity t => Bool -> Bool -> t Delta Word64
amountDelta True True=J.unwrap amount0UpW
amountDelta True False=J.unwrap amount0DownW
amountDelta False True=J.unwrap amount1UpW
amountDelta False False=J.unwrap amount1DownW

type PriceInput=(Word128,(Word64,Word64)) -- current, liquidity, amount
nextPriceRef :: Assert t => Bool -> Bool -> t PriceInput Word128
nextPriceRef exactInput zeroForOne=guarded bounds (next>>>guarded (validPrice iden) iden)
 where
  bounds=C.allChecks [validPrice oh,C.nonzero ioh,C.le ioh (C.k (10^9)),C.le iih (C.k (10^9))]
  a=L.u64 iih;l=L.u64 ioh;lq=liqQ96 ioh
  product=S.mul a oh
  fixedAmount=S.mul a (L.ks q96)
  next
   |exactInput&&zeroForOne=mulUp lq oh (L.add lq product)
   |exactInput=L.add oh (L.divide fixedAmount l)
   |zeroForOne=L.sub oh (ceil128 fixedAmount l)
   |otherwise=mulUp lq oh (L.sub lq product)
nextIn0W,nextIn1W,nextOut0W,nextOut1W :: J.WrappedSimplicity PriceInput Word128
nextIn0W=J.jetSubst (nextPriceRef True True)
nextIn1W=J.jetSubst (nextPriceRef True False)
nextOut0W=J.jetSubst (nextPriceRef False True)
nextOut1W=J.jetSubst (nextPriceRef False False)
{-# NOINLINE nextIn0W #-}
{-# NOINLINE nextIn1W #-}
{-# NOINLINE nextOut0W #-}
{-# NOINLINE nextOut1W #-}
nextPrice :: Simplicity t => Bool -> Bool -> t PriceInput Word128
nextPrice True True=J.unwrap nextIn0W
nextPrice True False=J.unwrap nextIn1W
nextPrice False True=J.unwrap nextOut0W
nextPrice False False=J.unwrap nextOut1W

type StepInput=((Word128,Word128),(Word64,(Bit,Word64)))
type StepOutput=(Word128,(Word64,(Word64,Word64))) -- next price, in, out, fee
current,target :: Core t => t StepInput Word128
current=ooh;target=oih
liquidity,remaining :: Core t => t StepInput Word64
liquidity=ioh;remaining=iiih
exactIn :: Core t => t StepInput Bit
exactIn=iioh
zeroForOne :: Core t => t StepInput Bit
zeroForOne=(target&&&current)>>>A.le word128
stepRef :: Simplicity t => t StepInput StepOutput
stepRef=guarded bounds ((iden&&&(maximumAtTarget&&&available))>>>(iden&&&next)>>>(iden&&&(actualIn&&&actualOut))>>>finish)
 where
  bounds=C.allChecks [validPrice current,validPrice target,C.le liquidity (C.k (10^9)),C.le remaining (C.k (10^9))]
  atTarget token0 up=(current&&&(target&&&liquidity))>>>amountDelta token0 up
  maxIn=C.select zeroForOne (atTarget True True) (atTarget False True)
  maxOut=C.select zeroForOne (atTarget False False) (atTarget True False)
  maximumAtTarget=C.select exactIn maxIn maxOut
  available=C.select exactIn (G.floorRatio remaining (C.k (feeDen-feePips)) (C.k feeDen)) remaining
  -- Domain A=(StepInput,(maximumAtTarget,available)).
  partial byInput zero=(take current&&&(take liquidity&&&iih))>>>nextPrice byInput zero
  partialIn=C.select (take zeroForOne) (partial True True) (partial True False)
  partialOut=C.select (take zeroForOne) (partial False True) (partial False False)
  next=C.select ((ioh&&&iih)>>>A.le word64) (take target) (C.select (take exactIn) partialIn partialOut)
  -- Domain B=(A,next). Reuse the source maximum only in its matching mode.
  inB=take (take exactIn)
  dirB=take (take zeroForOne)
  hitB=C.is ih (take (take target))
  actual token0 up=(take (take current)&&&(ih&&&take (take liquidity)))>>>amountDelta token0 up
  actualIn=C.select (and hitB inB) (take ioh) (C.select dirB (actual True True) (actual False True))
  actualOut=C.select (and hitB (not inB)) (take ioh) (C.select dirB (actual False False) (actual True False))
  -- Domain C=(B,(amountIn,uncappedAmountOut)).
  inC=take inB
  remC=take (take (take remaining))
  outC=C.select (and (not inC) ((remC&&&iih)>>>A.lt word64)) remC iih
  fee=C.select (and inC (not (take hitB))) (C.sub remC ioh) (G.ceilRatio ioh (C.k feePips) (C.k (feeDen-feePips)))
  finish=take ih&&&(ioh&&&(outC&&&fee))
stepWrapped :: J.WrappedSimplicity StepInput StepOutput
stepWrapped=J.jetSubst stepRef
{-# NOINLINE stepWrapped #-}
swapStep :: Simplicity t => t StepInput StepOutput
swapStep=J.unwrap stepWrapped

-- Exact source floor(fee*Q128/L). Only the native persisted increment is
-- bounded to128 bits; a 256-bit numerator is used before the division.
feeGrowthRef :: Assert t => t (Word64,Word64) Word128
feeGrowthRef=C.select (C.is oh (C.k 0)) (L.ks 0) (guarded (C.nonzero ih) (((L.u64 oh&&&L.ks 0)&&&(L.ks 0&&&L.u64 ih))>>>A.divide word256>>>((L.same oh (L.ks 0))&&&ih)>>>ih))
feeGrowthWrapped :: J.WrappedSimplicity (Word64,Word64) Word128
feeGrowthWrapped=J.jetSubst feeGrowthRef
{-# NOINLINE feeGrowthWrapped #-}
feeGrowth :: Simplicity t => t (Word64,Word64) Word128
feeGrowth=J.unwrap feeGrowthWrapped
earned :: Assert t => t (Word128,Word64) Word64
earned=(oh&&&L.u64 ih)>>>A.multiply word128>>>oh>>>S.narrow

ceilInteger a b=(a+b-1) `div`b
deltaInteger token0 up a b liquidity
 |token0&&up=ceilInteger (ceilInteger (liquidity*q96*diff) high) low
 |token0=liquidity*q96*diff `div`high `div`low
 |up=ceilInteger (liquidity*diff) q96
 |otherwise=liquidity*diff `div`q96
 where low=min a b;high=max a b;diff=high-low
nextInteger exactInput zeroForOne current liquidity amount
 |exactInput&&zeroForOne=ceilInteger (base*current) (base+amount*current)
 |exactInput=current+amount*q96 `div`liquidity
 |zeroForOne=current-ceilInteger (amount*q96) liquidity
 |otherwise=ceilInteger (base*current) (base-amount*current)
 where base=liquidity*q96
stepInteger current target liquidity exactInput remaining=(next,amountIn,amountOut,fee)
 where
  zeroForOne=current>=target
  maxIn=deltaInteger zeroForOne True current target liquidity
  maxOut=deltaInteger (notH zeroForOne) False current target liquidity
  notH x=if x then False else True
  available=if exactInput then remaining*(feeDen-feePips) `div`feeDen else remaining
  next=if available>=if exactInput then maxIn else maxOut then target else nextInteger exactInput zeroForOne current liquidity available
  hit=next==target
  amountIn=if hit&&exactInput then maxIn else deltaInteger zeroForOne True current next liquidity
  rawOut=if hit&&notH exactInput then maxOut else deltaInteger (notH zeroForOne) False current next liquidity
  amountOut=if exactInput then rawOut else min rawOut remaining
  fee=if exactInput&&notH hit then remaining-amountIn else ceilInteger (amountIn*feePips) (feeDen-feePips)
