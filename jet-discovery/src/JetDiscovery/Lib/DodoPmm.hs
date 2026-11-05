{-# LANGUAGE ScopedTypeVariables #-}
-- | Exact fixed-k0.1 DPP PMMPricing paths, including all R regimes, crossings,
-- precision caps and DPP's directional stored-target updates. Fee rates are0.
module JetDiscovery.Lib.DodoPmm where
import Prelude hiding (drop,take,not,and,or,minimum)
import qualified Prelude as H
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
import qualified JetDiscovery.Lib.DodoMath as D
import JetDiscovery.Lib.Bytes

-- B,Q,B0,Q0,R,i, with enumONE0/ABOVE1/BELOW2. True sells base.
type State=(Word64,(Word64,(Word64,(Word64,(Word64,Word64)))))
type Input=(State,(Bit,Word64))
type Output=(Word64,(Word64,(Word64,Word64))) -- receipt,B0',Q0',R'
field :: Core t => Int -> t State Word64
field 0=oh
field 1=ioh
field 2=iioh
field 3=drop (drop (drop oh))
field 4=drop (drop (drop (drop oh)))
field 5=drop (drop (drop (drop ih)))
field _=error "six-field PMM state"
f i=take (field i)
direction :: Core t => t Input Bit
direction=drop oh
delta :: Core t => t Input Word64
delta=drop ih
select p a b=(p&&&iden)>>>cond a b
is a b=(a&&&b)>>>eq
minimum a b=select ((a&&&b)>>>A.lt word64) a b

targetWrapped :: J.WrappedSimplicity D.TargetInput Word64
targetWrapped=J.jetSubst D.targetRef
{-# NOINLINE targetWrapped #-}
target :: Simplicity t => t D.TargetInput Word64
target=J.unwrap targetWrapped
tradeWrapped :: J.WrappedSimplicity D.TradeInput Word64
tradeWrapped=J.jetSubst D.tradeRef
{-# NOINLINE tradeWrapped #-}
trade :: Simplicity t => t D.TradeInput Word64
trade=J.unwrap tradeWrapped
integrateWrapped :: J.WrappedSimplicity D.IntegralInput Word64
integrateWrapped=J.jetSubst D.integrateRef
{-# NOINLINE integrateWrapped #-}
integrate :: Simplicity t => t D.IntegralInput Word64
integrate=J.unwrap integrateWrapped
reciprocal x=L.divide (L.ks (D.one*D.one)) (L.u64 x)>>>S.narrow

quoteRef :: Simplicity t => t Input Output
quoteRef=(iden&&&(baseTarget&&&quoteTarget))>>>(iden&&&select (take direction) sellBase sellQuote)>>>result
 where
  baseTarget=select (is (f 4) (C.k 1)) ((f 0&&&(C.sub (f 1) (f 3)&&&reciprocal (f 5)))>>>target) (f 2)
  quoteTarget=select (is (f 4) (C.k 2)) ((f 1&&&(C.sub (f 0) (f 2)&&&f 5))>>>target) (f 3)
  -- Domain here is(Input,(adjustedB0,adjustedQ0)).
  x i=take (f i)
  pay=take delta
  base0=ioh
  quote0=iih
  price=x 5
  invPrice=reciprocal price
  backBase=C.sub base0 (x 0)
  backQuote=C.sub (x 1) quote0
  backQuotePay=C.sub quote0 (x 1)
  backBaseRecv=C.sub (x 0) base0
  tradeAt v0 v1 quantity rate=(v0&&&(v1&&&(quantity&&&rate)))>>>trade
  integrateAt v0 v1 v2 rate=(v0&&&(v1&&&(v2&&&rate)))>>>integrate
  oneBase quantity=tradeAt quote0 quote0 quantity price
  oneQuote quantity=tradeAt base0 base0 quantity invPrice
  sellBase=select (is (x 4) (C.k 0)) (oneBase pay&&&C.k 2)
    (select (is (x 4) (C.k 1)) aboveBase (tradeAt quote0 (x 1) pay price&&&C.k 2))
  aboveBase=select ((pay&&&backBase)>>>A.lt word64)
    (minimum (integrateAt base0 (C.add (x 0) pay) (x 0) price) backQuote&&&C.k 1)
    (select (is pay backBase) (backQuote&&&C.k 0) (C.add backQuote (oneBase (C.sub pay backBase))&&&C.k 2))
  sellQuote=select (is (x 4) (C.k 0)) (oneQuote pay&&&C.k 1)
    (select (is (x 4) (C.k 1)) (tradeAt base0 (x 0) pay invPrice&&&C.k 1) belowQuote)
  belowQuote=select ((pay&&&backQuotePay)>>>A.lt word64)
    (minimum (integrateAt quote0 (C.add (x 1) pay) (x 1) invPrice) backBaseRecv&&&C.k 2)
    (select (is pay backQuotePay) (backBaseRecv&&&C.k 0) (C.add backBaseRecv (oneQuote (C.sub pay backQuotePay))&&&C.k 1))
  -- Domain is((Input,(adjustedB0,adjustedQ0)),(receipt,newR)).
  changed=not (is iih (take (x 4)))
  result=ioh&&&(select (and (take (take direction)) changed) (take base0) (take (x 2))&&&(select (and (not (take (take direction))) changed) (take quote0) (take (x 3))&&&iih))

-- Independent unbounded Integer source translation; caller validates the native
-- state and physical funding separately. Preserve DPP's conditional target store.
quoteInteger :: [Integer] -> Bool -> Integer -> (Integer,Integer,Integer,Integer)
quoteInteger [b,q,b0,q0,r,price] sellBase pay=(receipt,storedB0,storedQ0,newR)
 where
  inverse=D.one*D.one `div`price
  adjustedB0=if r==1 then D.targetInteger b (q-q0) inverse else b0
  adjustedQ0=if r==2 then D.targetInteger q (b-b0) price else q0
  oneBase x=D.tradeInteger adjustedQ0 adjustedQ0 x price
  oneQuote x=D.tradeInteger adjustedB0 adjustedB0 x inverse
  backBase=adjustedB0-b
  backQuote=q-adjustedQ0
  backQuotePay=adjustedQ0-q
  backBaseRecv=b-adjustedB0
  (receipt,newR)
   |sellBase&&r==0=(oneBase pay,2)
   |sellBase&&r==1&&pay<backBase=(min (D.integrateInteger adjustedB0 (b+pay) b price) backQuote,1)
   |sellBase&&r==1&&pay==backBase=(backQuote,0)
   |sellBase&&r==1=(backQuote+oneBase (pay-backBase),2)
   |sellBase=(D.tradeInteger adjustedQ0 q pay price,2)
   |r==0=(oneQuote pay,1)
   |r==1=(D.tradeInteger adjustedB0 b pay inverse,1)
   |pay<backQuotePay=(min (D.integrateInteger adjustedQ0 (q+pay) q inverse) backBaseRecv,2)
   |pay==backQuotePay=(backBaseRecv,0)
   |otherwise=(backBaseRecv+oneQuote (pay-backQuotePay),1)
  storedB0=if sellBase&&newR/=r then adjustedB0 else b0
  storedQ0=if H.not sellBase&&newR/=r then adjustedQ0 else q0
quoteInteger _ _ _=error "six-field PMM state"
