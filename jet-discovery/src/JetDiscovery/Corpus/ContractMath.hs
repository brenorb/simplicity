{-# LANGUAGE ScopedTypeVariables #-}
-- | Exact published arithmetic paths, separately labeled as kernels rather
-- than counted as complete multi-asset smart contracts.
module JetDiscovery.Corpus.ContractMath (entries,tickSqrt,curveD) where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as P
import qualified Data.List as L
import Data.Bits (testBit,shiftR)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Programs.Word as W
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

-- Mathematical fixed-point factors published in Uniswap TickMath.sol.
factors :: [Integer]
factors=[0xfffcb933bd6fad37aa2d162d1a594001,0xfff97272373d413259a46990580e213a,0xfff2e50f5f656932ef12357cf3c7fdcc,0xffe5caca7e10e4e61c3624eaa0941cd0,0xffcb9843d60f6159c9db58835c926644,0xff973b41fa98c081472e6896dfb254c0,0xff2ea16466c96a3843ec78b326b52861,0xfe5dee046a99a2a811c461f1969c3053,0xfcbe86c7900a88aedcffc83b479aa3a4,0xf987a7253ac413176f2b074cf7815e54,0xf3392b0822b70005940c7a398e4b70f3,0xe7159475a2c29b7443b29c7fa6e889d9,0xd097f3bdfd2022b8845ad8f792aa5825,0xa9f746462d870fdf8a65dc1f90e061e5,0x70d869a156d2a1b890bb3df62baf32f7,0x31be135f97d08fd981231505542fcfa6,0x9aa508b5b7a84e1c677de54f3e99bc9,0x5d6af8dedb81196699c329225ee604,0x2216e584f5fa1ea926041bedfe98,0x48a170391f7dc42444e8fa2]
pick :: (Core t,TyC a,TyC b) => Bool -> t a b -> t (a,a) b
pick False=take
pick True=drop
bit32 :: Core t => Int -> t Word32 Bit
bit32 i=pick (testBit j 4) (pick (testBit j 3) (pick (testBit j 2) (pick (testBit j 1) (pick (testBit j 0) iden)))) where j=31-i

-- | (negative sign, absolute tick) -> sqrt(1.0001^tick)*2^96 rounded up.
-- All twenty bit positions, reciprocal and rounding run inside Simplicity.
tickSqrt :: forall t. Assert t => t (Bit,Word32) Word256
tickSqrt=(rangeOk&&&iden)>>>drop calculate
 where
  rangeOk=(ih&&&konst (w32 887272))>>>A.le word32>>>verify
  start=ih&&&konst (w256 (2^128))
  step i=oh&&&((take (bit32 i)&&&ih)>>>cond ((iden&&&konst (w256 (factors!!i)))>>>A.multiply word256>>>(oih&&&ioh)) iden)
  loops=L.foldl' (>>>) iden [step i|i<-[0..19]]
  inverse=(konst (w256 (2^256-1))&&&iden)>>>A.divide word256
  ratio=(oh&&&(start>>>loops>>>ih))>>>cond iden inverse
  lowBits=(iden&&&konst (w256 (2^32-1)))>>>W.bitwise_and word256
  roundUp=((lowBits&&&konst (w256 0)>>>eq)&&&(W.shift_const_by false word256 (-32)))>>>cond iden ((iden&&&konst (w256 1))>>>A.add word256>>>ih)
  calculate=ratio>>>roundUp

tickRef :: Integer -> Integer
tickRef tick=(ratio`div`2^32)+if ratio`mod`2^32==0 then 0 else 1
 where
  low=L.foldl' (\r (i,c)->if testBit (abs tick) i then r*c`div`2^128 else r) (2^128) (zip [0..] factors)
  ratio=if tick>0 then (2^256-1)`div`low else low

-- Full-width unsigned multiply/divide, failing on zero divisor or quotient overflow.
mulDiv :: Assert t => t ((Word256,Word256),Word256) Word256
mulDiv=(nonzero&&&iden)>>>drop calc
 where
  nonzero=(ih&&&konst (w256 0)>>>eq>>>not iden>>>verify)
  quotient=(take (A.multiply word256)&&&(konst (w256 0)&&&ih))>>>A.divide word512
  calc=quotient>>>((oh&&&konst (w256 0)>>>eq>>>verify)&&&ih)>>>ih

type Bal=(Word256,(Word256,Word256))
k :: (Core t,TyC a) => Integer -> t a Word256
k=konst . w256
add a b=(a&&&b)>>>A.add word256>>>ih
mulSmall a c=(a&&&k c)>>>A.multiply word256>>>ih
sumBal :: Assert t => t Bal Word256
sumBal=add (add oh ioh) iih

-- | One Curve3pool get_D Newton step at amplification100. Inputs are normalized
-- positive balances <=2^64-1. The intermediates fit256 bits except the final
-- multiplication, for which mulDiv deliberately retains all512 bits.
newton :: forall t. Assert t => t (Bal,Word256) Word256
newton=(iden&&&ih)>>>dpSteps>>>next
 where
  dpStep balance=oh&&&(((ih&&&oih)&&&mulSmall (take (take balance)) 3)>>>mulDiv)
  dpSteps=L.foldl' (>>>) iden [dpStep oh,dpStep ioh,dpStep iih]
  -- after dp: ((balances,D),D_P)
  numerator=add (take (take sumBal)>>>mulSmall iden 300) (mulSmall ih 3)
  denominator=add (mulSmall oih 299) (mulSmall ih 4)
  next=(numerator&&&oih)&&&denominator>>>mulDiv

-- | Full bounded Curve invariant evaluation: up to32 Newton updates, stopping
-- when consecutive values differ by<=1; rejects if no convergence in the bound.
curveD :: forall t. Assert t => t Bal Word256
curveD=checks&&&iden>>>drop (start>>>loops>>>done)
 where
  nonzero x=(x&&&k 0>>>eq>>>not iden>>>verify)
  bound x=(x&&&k (2^64-1))>>>A.le word256>>>verify
  checks=(nonzero oh&&&nonzero ioh&&&nonzero iih&&&bound oh&&&bound ioh&&&bound iih)>>>unit
  start=iden&&&(sumBal&&&false)
  update=iden&&&((oh&&&ioh)>>>newton)>>>take oh&&&(ih&&&converged)
  old=take ioh
  converged=(((old&&&ih)>>>A.max word256)&&&((old&&&ih)>>>A.min word256))>>>A.subtract word256>>>ih>>>(iden&&&k 1)>>>A.le word256
  step=(iih&&&iden)>>>cond iden update
  loops=L.foldl' (>>>) iden (replicate 32 step)
  done=(iih>>>verify)&&&ioh>>>ih

curveRef :: [Integer] -> Integer
curveRef xs=go 255 (P.sum xs)
 where
  s=P.sum xs
  go 0 _=error "Curve reference convergence"
  go n d=let dp=L.foldl' (\a x->a*d`div`(3*x)) d xs
             d'=(300*s+3*dp)*d`div`(299*d+4*dp)
          in if abs (d'-d)<=1 then d' else go (n-1) d'

simpleEnv=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
entries :: [Entry]
entries=
 [Entry "xchain-uniswap-v3-tick-math" "Uniswap v3 full-range getSqrtRatioAtTick" "Pinned Uniswap/v3-core TickMath.sol getSqrtRatioAtTick; mathematical factors retained in module" CrossChain
  (Derived "integer reference follows all20 factors, inversion and exact rounding; source min/max ratios checked explicitly")
  ["arithmetic kernel, not an entire pool; negative bit plus absolute tick<=887272", "result is full uint160 sqrtPriceX96 represented as Word256"]
  (\(tick,expected)->Prog ((witness (if tick<0 then Right () else Left (),w32 (abs tick))>>>tickSqrt)&&&witness (w256 expected)>>>eq>>>verify))
  ([Vector "source MIN_SQRT_RATIO" simpleEnv (-887272,4295128739) Accept,Vector "source MAX_SQRT_RATIO" simpleEnv (887272,1461446703485210103287273052203988822378723970342) Accept]++
   [Vector ("tick "++show i) simpleEnv (i,tickRef i) Accept|i<-[-200000,-1,0,1,200000]]++
   [Vector "rounded value altered" simpleEnv (1,tickRef 1+1) Reject,Vector "tick out of range" simpleEnv (887273,0) Reject])
 ,Entry "xchain-curve-stableswap-invariant" "Curve3pool Newton invariant D with bounded convergence" "Pinned curvefi/curve-contract StableSwap3Pool.vy get_D; amp=100,3coins" CrossChain
  (Derived "independent Integer get_D runs up to255 steps; program runs up to32 and requires convergence")
  ["arithmetic kernel; three strictly positive normalized balances<=2^64-1", "32-update bound with early freezing; reject nonconvergence; final multiply/divide retains512 bits", "does not implement mint/burn/swap or token custody"]
  (\(xs,expected)->let [a,b,c]=xs in Prog ((witness (w256 a,(w256 b,w256 c))>>>curveD)&&&witness (w256 expected)>>>eq>>>verify))
  ([Vector (show xs) simpleEnv (xs,curveRef xs) Accept|xs<-[[1000000,1000000,1000000],[1000000,2000000,4000000],[10^18,10^18,2*10^18],[1,1000,1000000]]]++
   [Vector "invariant altered" simpleEnv ([1000000,2000000,4000000],curveRef [1000000,2000000,4000000]+1) Reject,
    Vector "zero balance" simpleEnv ([0,1000000,1000000],0) Reject])
 ,Entry "xchain-fullmath-muldiv" "Uniswap full-width512-bit mulDiv" "Pinned Uniswap/v3-core FullMath.sol mulDiv floor(a*b/denominator)" CrossChain
  (Derived "Haskell arbitrary-precision multiplication/division with zero/overflow negatives") ["arithmetic kernel; full256-bit operands,256-bit quotient; overflow and zero denominator reject"]
  (\(a,b,d,q)->Prog ((witness ((w256 a,w256 b),w256 d)>>>mulDiv)&&&witness (w256 q)>>>eq>>>verify))
  [Vector "product overflows256 but quotient fits" simpleEnv (2^200,2^100,2^80,2^220) Accept,
   Vector "rounding down" simpleEnv (10,20,3,66) Accept,Vector "wrong rounding" simpleEnv (10,20,3,67) Reject,
   Vector "zero denominator" simpleEnv (1,1,0,0) Reject,Vector "quotient overflow" simpleEnv (2^255,2^255,1,0) Reject]
 ]
