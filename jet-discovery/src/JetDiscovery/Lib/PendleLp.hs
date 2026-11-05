-- | Exact bounded Pendle MarketMathCore add-liquidity quote.
module JetDiscovery.Lib.PendleLp where
import Prelude hiding (drop,take)
import Simplicity.Term.Core
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity)
import Simplicity.Ty.Word
import qualified JetDiscovery.Lib.BoundedSqrt as Q
import qualified JetDiscovery.Lib.ClaimLedger as C
import qualified JetDiscovery.Corpus.ContractGrowth as G

type Input=(Word64,(Word64,(Word64,(Word64,Word64)))) -- reserves,LP,supplied SY/PT
type Output=(Word64,(Word64,(Word64,Word64))) -- used SY/PT,mint,locked mint
syDesired,ptDesired :: Core t => t Input Word64
syDesired=drop (drop (drop oh))
ptDesired=drop (drop (drop ih))
joinRef :: Simplicity t => t Input Output
joinRef=(C.allChecks [C.nonzero syDesired,C.nonzero ptDesired]&&&iden)>>>drop (C.select (C.is iioh (C.k 0)) first normal)>>>(iden&&&C.allChecks [C.nonzero oh,C.nonzero ioh,C.nonzero iioh])>>>oh
 where
  root=(syDesired&&&ptDesired)>>>A.multiply word64>>>Q.sqrt128
  first=syDesired&&&(ptDesired&&&(C.sub root (C.k 1000)&&&C.k 1000))
  byPt=G.floorRatio ptDesired iioh ioh
  bySy=G.floorRatio syDesired iioh oh
  normal=(iden&&&(byPt&&&bySy))>>>C.select ((ioh&&&iih)>>>A.lt word64)
    (G.ceilRatio (take oh) ioh (take iioh)&&&(take ptDesired&&&(ioh&&&C.k 0)))
    (take syDesired&&&(G.ceilRatio (take ioh) iih (take iioh)&&&(iih&&&C.k 0)))
joinWrapped :: J.WrappedSimplicity Input Output
joinWrapped=J.jetSubst joinRef
{-# NOINLINE joinWrapped #-}
joinQuote :: Simplicity t => t Input Output
joinQuote=J.unwrap joinWrapped

joinInteger sy pt lp syWant ptWant
 |lp==0=(syWant,ptWant,Q.sqrtInteger (syWant*ptWant)-1000,1000)
 |byPt<bySy=((sy*byPt+lp-1) `div`lp,ptWant,byPt,0)
 |otherwise=(syWant,(pt*bySy+lp-1) `div`lp,bySy,0)
 where byPt=ptWant*lp `div`pt;bySy=syWant*lp `div`sy
