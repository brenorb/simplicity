{-# LANGUAGE ScopedTypeVariables #-}
-- | Source accounting for the fixed-price TwoCrypto reserve and LP profile.
module JetDiscovery.Lib.TwoCryptoPool
  ( Pool, balances, invariantD, supply, virtualPrice, profit, profitAnchor, adminCredit
  , assemble, encodePool, joinPool, swapPool, exitPool, sweepPool ) where

import Prelude hiding (drop,take)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Programs.Bit (Bit)
import Simplicity.Term.Core
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes (w64)
import JetDiscovery.Lib.TwoCryptoArithmetic
import qualified JetDiscovery.Lib.TwoCryptoMath as M
import qualified JetDiscovery.Ref.TwoCrypto as R

type Pool = ((M.Balances,(Word64,Word64)),((Word64,Word64),(Word64,Word64)))

balances :: Core t => t Pool M.Balances
balances = ooh

invariantD,supply,virtualPrice,profit,profitAnchor,adminCredit :: Core t => t Pool Word64
invariantD = oioh
supply = oiih
virtualPrice = iooh
profit = ioih
profitAnchor = iioh
adminCredit = iiih

assemble :: (Core t,TyC a) => t a M.Balances -> t a Word64 -> t a Word64
         -> t a Word64 -> t a Word64 -> t a Word64 -> t a Word64 -> t a Pool
assemble xs d shares vp p anchor credit = (xs&&&(d&&&shares))&&&((vp&&&p)&&&(anchor&&&credit))

encodePool :: R.Pool -> Pool
encodePool p = (((w64 x,w64 y),(w64 (R.storedD p),w64 (R.supply p))),
  ((w64 (R.virtualPrice p),w64 (R.profit p)),(w64 (R.profitAnchor p),w64 (R.adminCredit p))))
 where (x,y) = R.reserves p

xcp :: Assert t => t Word64 Word64
xcp = quotient iden (word 2)

type Tweak = (Pool,(M.Balances,(Word64,(Word64,Word64))))

tweak :: forall t. Simplicity t => t Tweak Pool
tweak = (iden&&&nextPrice)>>>checked
  (checks [lt (take (old>>>virtualPrice)) ih,le ih (word (2*R.wad)),
    (take (nextBalances>>>M.normalize)&&&take nextD)>>>M.spotBound]) update
 where
  old = oh
  nextBalances = ioh
  nextD = iih>>>oh
  nextSupply = iih>>>ioh
  nextCredit = iih>>>iih
  nextPrice = add (ratio (word R.wad) (nextD>>>xcp) nextSupply) (word 1)
  update = (iden&&&ratio (take (old>>>profit)) ih (take (old>>>virtualPrice)))>>>
    checked (checks [le (word R.wad) ih,le ih (word (4*R.wad))])
      (assemble (ooh>>>nextBalances) (ooh>>>nextD) (ooh>>>nextSupply) oih ih
                (ooh>>>old>>>profitAnchor) (ooh>>>nextCredit))

type Join = (Pool,M.Balances)
type JoinWork = (Join,(M.Balances,Word64))

joinRef :: forall t. Simplicity t => t Join (Pool,Word64)
joinRef = checked (positive (ih>>>add oh ih)) (iden&&&(newBalances&&&newD))>>>
  select (equal (ooh>>>supply) (word 0)) initial existing
 where
  newBalances = add (oh>>>balances>>>oh) ioh&&&add (oh>>>balances>>>ih) iih
  newD = newBalances>>>M.normalize>>>M.invariant
  initial :: t JoinWork (Pool,Word64)
  initial = (iden&&&(iih>>>xcp))>>>
    checked (positive ih)
      (assemble (oh>>>ioh) (oh>>>iih) ih (word R.wad) (word R.wad) (word R.wad)
        (oh>>>ooh>>>adminCredit)&&&ih)
  existing :: t JoinWork (Pool,Word64)
  existing = (iden&&&gross)>>>(iden&&&tokenFee)>>>(iden&&&sub oih ih)>>>
    checked (positive ih) (transition&&&ih)
  gross = sub (ratio (ooh>>>supply) iih (ooh>>>invariantD)) (ooh>>>supply)
  -- Equal even precisions make normalized Sdiff/S equal to |a-b|/(a+b).
  tokenFee = add (ratio tokenRate ih (word (10^10))) (word 1)
   where
    d0 = take (oih>>>oh)
    d1 = take (oih>>>ih)
    curveFee = take (ioh>>>M.normalize>>>M.dynamicFee)
    tokenRate = add (ratio (quotient curveFee (word 2)) (diff d0 d1) (add d0 d1)) (word (10^5))
  transition = (old&&&(new&&&(d&&&(newSupply&&&newCredit))))>>>tweak
   where
    context = ooh>>>oh
    old = context>>>ooh
    new = context>>>ioh
    d = context>>>iih
    newSupply = add (old>>>supply) ih
    newCredit = add (old>>>adminCredit) (quotient oih (word 2))

{-# NOINLINE joinWrapped #-}
joinWrapped :: J.WrappedSimplicity Join (Pool,Word64)
joinWrapped = J.jetSubst joinRef

joinPool :: Simplicity t => t Join (Pool,Word64)
joinPool = J.unwrap joinWrapped

type Swap = (Pool,(Bit,Word64))

swapRef :: forall t. Simplicity t => t Swap (Pool,Word64)
swapRef = checked (checks [positive iih,positive (oh>>>supply)])
  (iden&&&(postInput>>>M.normalize))>>>(iden&&&solve)>>>
  (iden&&&gross)>>>(iden&&&received)>>>
  checked (positive ih) (transition&&&ih)
 where
  postInput = select ioh ((oh>>>balances>>>oh)&&&add (oh>>>balances>>>ih) iih)
                        (add (oh>>>balances>>>oh) iih&&&(oh>>>balances>>>ih))
  -- In source xp order. The first flooring in the fee makes the order
  -- observable even though the real-valued formula is symmetric.
  solve = (ooh>>>invariantD)&&&select (oh>>>ioh) iih ioh>>>M.getY
  gross = quotient (sub (sub (select (ooh>>>ioh) (oih>>>oh) (oih>>>ih)) ih) (word 1))
                   (word R.precision)
  received = sub ih (ratio ih (feeXp>>>M.dynamicFee) (word (10^10)))
   where
    before = ooh
    dir = before>>>oh>>>ioh
    adjusted = oih
    feeXp = select dir (adjusted&&&(before>>>ih>>>ih)) ((before>>>ih>>>oh)&&&adjusted)
  transition = (old&&&(newBalances&&&((newBalances>>>M.normalize>>>M.invariant)&&&
                ((old>>>supply)&&&(old>>>adminCredit)))))>>>tweak
   where
    input = ooh>>>ooh
    old = input>>>oh
    d = input>>>iih
    side = input>>>ioh
    x = old>>>balances>>>oh
    y = old>>>balances>>>ih
    newBalances = select side (sub x ih&&&add y d) (add x d&&&sub y ih)

{-# NOINLINE swapWrapped #-}
swapWrapped :: J.WrappedSimplicity Swap (Pool,Word64)
swapWrapped = J.jetSubst swapRef

swapPool :: Simplicity t => t Swap (Pool,Word64)
swapPool = J.unwrap swapWrapped

type Exit = (Pool,Word64)

exitRef :: Simplicity t => t Exit (Pool,M.Balances)
exitRef = checked (checks [positive ih,le ih (oh>>>supply)]) (iden&&&adjusted)>>>
  (iden&&&payments)>>>(newPool&&&ih)
 where
  adjusted = select (equal ih (oh>>>supply)) ih (sub ih (word 1))
  payments = ratio (ooh>>>balances>>>oh) ih (ooh>>>supply)&&&
             ratio (ooh>>>balances>>>ih) ih (ooh>>>supply)
  newPool = assemble
    (sub (old>>>balances>>>oh) ioh&&&sub (old>>>balances>>>ih) iih)
    (sub (old>>>invariantD) (ratio (old>>>invariantD) oih (old>>>supply)))
    (sub (old>>>supply) (ooh>>>ih))
    (old>>>virtualPrice) (old>>>profit) (old>>>profitAnchor) (old>>>adminCredit)
   where old = ooh>>>oh

{-# NOINLINE exitWrapped #-}
exitWrapped :: J.WrappedSimplicity Exit (Pool,M.Balances)
exitWrapped = J.jetSubst exitRef

exitPool :: Simplicity t => t Exit (Pool,M.Balances)
exitPool = J.unwrap exitWrapped

sweepRef :: Simplicity t => t Pool (Pool,M.Balances)
sweepRef = checked (checks [lt profitAnchor profit,le (word R.wad) supply]) (iden&&&fees)>>>
  checked (positive ih) (iden&&&share)>>>
  checked (positive ih) (iden&&&add (ooh>>>supply) ih)>>>
  (iden&&&outAmounts)>>>
  checked (positive (ih>>>add oh ih)) (newPool&&&ih)
 where
  fees = quotient (sub profit profitAnchor) (word 4)
  share = add (oh>>>adminCredit) (ratio (oh>>>supply) fraction (word R.wad))
   where
    vp = oh>>>virtualPrice
    fraction = sub (ratio vp (word R.wad) (sub vp ih)) (word R.wad)
  outAmounts = ratio (ooh>>>oh>>>balances>>>oh) oih ih&&&
               ratio (ooh>>>oh>>>balances>>>ih) oih ih
  newPool = (iden&&&vp)>>>
    checked (checks [le (word R.wad) ih,le ih (word (2*R.wad))]) update
   where
    old = ooh>>>ooh
    including = oih
    vp = ratio (word R.wad) (old>>>invariantD>>>xcp) including
    update = assemble
      (sub (take (old>>>balances>>>oh)) (oih>>>oh)&&&sub (take (old>>>balances>>>ih)) (oih>>>ih))
      (sub (take (old>>>invariantD)) (ratio (take (old>>>invariantD))
        (take (ooh>>>ih)) (take including)))
      (take (old>>>supply)) ih nextProfit
      ((take (old>>>profitAnchor)&&&nextProfit)>>>A.max word64) (word 0)
    nextProfit = sub (take (old>>>profit)) (add oldFees oldFees)
    oldFees = take (ooh>>>oih)

{-# NOINLINE sweepWrapped #-}
sweepWrapped :: J.WrappedSimplicity Pool (Pool,M.Balances)
sweepWrapped = J.jetSubst sweepRef

sweepPool :: Simplicity t => t Pool (Pool,M.Balances)
sweepPool = J.unwrap sweepWrapped
