{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Complete bounded DODO private-pool adaptation over fully BTC-backed coupons.
-- This is DPP (all three R regimes), not DVM's restricted pool implementation.
module JetDiscovery.Corpus.NativePmmPool where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.ClaimLedger
import qualified JetDiscovery.Lib.DodoMath as D
import qualified JetDiscovery.Lib.DodoPmm as P
import JetDiscovery.Types
import Simplicity.Digest (Hash256)
import JetDiscovery.Tx (hashFromInteger)

-- Offchain fixture only, independently derived from the complete typed kernel.
-- The priority driver compares actual canonical CMR before every vector batch.
pmmFixtureCmr :: Hash256
pmmFixtureCmr=hashFromInteger 0xfc1be04a86d81a9fafeab4eaa2b968d35fc2004ccc9799a6dbbbec312a4a057f

pmmWrapped :: J.WrappedSimplicity P.Input P.Output
pmmWrapped=J.jetSubst P.quoteRef
{-# NOINLINE pmmWrapped #-}
pmmQuote :: Simplicity t => t P.Input P.Output
pmmQuote=J.unwrap pmmWrapped

validPool :: Assert t => t Ledger ()
validPool=allChecks [validClaims field,allChecks [same (field i) (k 0)|i<-[9..13]++[15]++[20..31]],le (k (D.one `div`2)) (field 19),le (field 19) (k (2*D.one)),le (field 18) (k 2),select (is (field 7) (k 0)) closed active]
 where
  closed=allChecks [same (field i) (k 0)|i<-[8,16,17,18]]
  active=allChecks ([nonzero (field i)|i<-[7,8,16,17]]++[le (field i) (k (10^9))|i<-[7,8]]++[le (field i) (k (4*10^9))|i<-[16,17]]++[select (is (field 18) (k 0)) (allChecks [same (field 7) (field 16),same (field 8) (field 17)]) (select (is (field 18) (k 1)) (le (field 17) (field 8)) (le (field 16) (field 7)))])

pmmT :: (Simplicity t,Primitive t) => CT t
pmmT=allChecks [base,old>>>validPool,new>>>validPool,choose (claimBranches++[(16,reset True),(17,reset False),(18,swap True),(19,swap False)])]
 where
  -- Owner-signed funding/withdraw/reset follows DPP.reset's target=reserve and
  -- R=ONE rule. Moving existing coupons never fabricates native collateral.
  reset funding=allChecks [same actor (k 0),sigAt 0 0,changes ([(7,nextBase),(8,nextQuote),(16,nextBase),(17,nextQuote),(18,k 0),(19,aux 1),nonce,(3,userBase),(5,userQuote)]),noCash]
   where
    nextBase=(if funding then add else sub) (o 7) amount
    nextQuote=(if funding then add else sub) (o 8) (aux 0)
    userBase=(if funding then sub else add) (o 3) amount
    userQuote=(if funding then sub else add) (o 5) (aux 0)
  state=(o 7&&&(o 8&&&(o 16&&&(o 17&&&(o 18&&&o 19)))))
  swap baseIn=(iden&&&((state&&&(konst (toBit baseIn)&&&amount))>>>pmmQuote))>>>swapChecks baseIn
  -- Every projected quote is staged once alongside the one bound Input.
  swapChecks baseIn=allChecks [take actorSig,take (nonzero amount),nonzero receipt,take noCash,allChecks [same (take (n i)) (maybe (take (o i)) id (lookup i updates))|i<-[0..31]]]
   where
    receipt=drop oh
    baseTarget=drop ioh
    quoteTarget=drop iioh
    rState=drop (drop (drop ih))
    quantity=take amount
    actorBalance isB=take (userBalance isB o)
    accountP a b=select (is (take actor) (k 0)) a b
    userChanges isB value=if isB then [(5,accountP value (take (o 5))),(6,accountP (take (o 6)) value)] else [(3,accountP value (take (o 3))),(4,accountP (take (o 4)) value)]
    updates=[(7,(if baseIn then add else sub) (take (o 7)) (if baseIn then quantity else receipt)),(8,(if baseIn then sub else add) (take (o 8)) (if baseIn then receipt else quantity)),(16,baseTarget),(17,quoteTarget),(18,rState),(14,add (take (o 14)) (k 1))]
      ++userChanges False ((if baseIn then sub else add) (actorBalance False) (if baseIn then quantity else receipt))
      ++userChanges True ((if baseIn then add else sub) (actorBalance True) (if baseIn then receipt else quantity))

stateValues xs=[xs H.!!i|i<-[7,8,16,17,18,19]]
swapState state who baseIn quantity=step state ([(7,baseReserve),(8,quoteReserve),(16,bt),(17,qt),(18,r),(aIndex,aBalance),(bIndex,bBalance)])
 where
  (receipt,bt,qt,r)=P.quoteInteger (stateValues state) baseIn quantity
  baseReserve=state H.!!7+(if baseIn then quantity else negate receipt)
  quoteReserve=state H.!!8+(if baseIn then negate receipt else quantity)
  aIndex=3+who;bIndex=5+who
  aBalance=state H.!!aIndex+(if baseIn then negate quantity else receipt)
  bBalance=state H.!!bIndex+(if baseIn then receipt else negate quantity)
step state xs=update state ((14,state H.!!14+1):xs)

pmmEntry=entry "app-proactive-market-maker-private-pool" "Native DODO private proactive-market-maker lifecycle" "DODO PMMPricing/DODOMath and DPPTrader/DPPStorage/DPPVault.reset; exact pinned source"
 ["DPP private owner0 and two coupon traders; fixed k0.1, LP fee0 and maintainer fee0 (supported source configuration); all ONE/ABOVE_ONE/BELOW_ONE paths, adjusted targets, exact crossings and source precision caps are retained", "two independently redeemable fully BTC-backed native coupon classes, not foreign ERC20 assets; no LP share issuance in this private-owner profile; owner funds/withdraws existing coupon inventory and resets targets/reserves/R/price, while only signed owners can move their coupon balances", "native pool reserves1..1e9 and stored targets1..4e9, price0.5..2 at1e18 precision; both reserves empty or both positive; nonzero-output swaps; checked128/256-bit arithmetic and full integer square roots", "owner-signed price reset is an authenticated configuration event, not a claim of current external oracle freshness; no source callbacks, flash execution, arbitrary admin module or global token registry"] pmmT vectors
 where
  empty=update [] [(0,4000000),(1,2000000),(2,2000000),(3,1700000),(4,300000),(5,1600000),(6,400000),(19,D.one)]
  initial=step empty [(3,700000),(5,600000),(7,1000000),(8,1000000),(16,1000000),(17,1000000)]
  resetPrice=step initial [(19,12*10^17)]
  withdrawal=step initial [(3,710000),(5,620000),(7,990000),(8,980000),(16,990000),(17,980000)]
  closed=step initial [(3,1700000),(5,1600000),(7,0),(8,0),(16,0),(17,0)]
  below=swapState initial 0 True 30000
  above=swapState initial 1 False 40000
  (b,q,b0,q0,price)=(above H.!!7,above H.!!8,above H.!!16,above H.!!17,above H.!!19)
  backBase=D.targetInteger b (q-q0) (D.one*D.one `div`price)-b
  backQuote=D.targetInteger (below H.!!8) (below H.!!7-below H.!!16) (below H.!!19)-below H.!!8
  traded baseIn state who quantity=swapState state who baseIn quantity
  issueA=step initial [(0,4000500),(1,2000500),(3,700500)]
  issueB=step initial [(0,4000700),(2,2000700),(6,400700)]
  moveA=step initial [(3,699500),(4,300500)]
  moveB=step initial [(5,600500),(6,399500)]
  burnA=step initial [(0,3999500),(1,1999500),(3,699500)]
  burnB=step initial [(0,3999500),(2,1999500),(6,399500)]
  v=vectorBound pmmFixtureCmr
  go label m a b who quantity extras signer funding payout height expected=v label pmmT m a b who quantity extras [signer] funding payout height expected
  swapV label baseIn state who quantity=go label (if baseIn then 18 else 19) state (traded baseIn state who quantity) (toInteger who) quantity [] who 0 Nothing 0 Accept
  vectors=[
   go "owner funds both private-pool reserves and initializes targets" 16 empty initial 0 1000000 [1000000,D.one] 0 0 Nothing 0 Accept,
   go "owner resets price without inventing inventory" 16 initial resetPrice 0 0 [0,12*10^17] 0 0 Nothing 0 Accept,
   go "owner withdraws inventory and resets both targets" 17 initial withdrawal 0 10000 [20000,D.one] 0 0 Nothing 0 Accept,
   go "owner fully withdraws to the defined safe closed state" 17 initial closed 0 1000000 [1000000,D.one] 0 0 Nothing 0 Accept,
   swapV "ONE sell base enters BELOW_ONE" True initial 0 30000,
   swapV "ONE sell quote enters ABOVE_ONE" False initial 1 40000,
   swapV "BELOW_ONE further base trade uses quadratic target" True below 0 10000,
   swapV "ABOVE_ONE further quote trade uses reciprocal price" False above 1 10000,
   swapV "ABOVE_ONE base trade before target uses integral" True above 1 (backBase `div`2),
   swapV "ABOVE_ONE exact base return enters ONE" True above 1 backBase,
   swapV "ABOVE_ONE base crosses into BELOW_ONE" True above 1 (backBase+10000),
   swapV "BELOW_ONE quote trade before target uses integral" False below 0 (backQuote `div`2),
   swapV "BELOW_ONE exact quote return enters ONE" False below 0 backQuote,
   swapV "BELOW_ONE quote crosses into ABOVE_ONE" False below 0 (backQuote+10000),
   swapV "nonunit owner price feeds exact quadratic trade" True resetPrice 0 15000,
   go "native A issuance funds actual collateral" 0 initial issueA 0 500 [] 0 500 Nothing 0 Accept,
   go "native B issuance authenticates owner1" 1 initial issueB 1 700 [] 1 700 Nothing 0 Accept,
   go "native A transfer preserves complete supply" 2 initial moveA 0 500 [] 0 0 Nothing 0 Accept,
   go "native B transfer preserves complete supply" 3 initial moveB 1 500 [] 1 0 Nothing 0 Accept,
   go "A mature burn pays native owner0" 4 initial burnA 0 500 [] 0 0 (Just (0,500)) 800000 Accept,
   go "B mature burn uses distinct later maturity" 5 initial burnB 1 500 [] 1 0 (Just (1,500)) 900000 Accept,
   go "nonowner cannot withdraw private reserves" 17 initial withdrawal 0 10000 [20000,D.one] 1 0 Nothing 0 Reject,
   go "one-sided reserve shutdown rejected" 17 initial (step initial [(3,1700000),(7,0),(16,0)]) 0 1000000 [0,D.one] 0 0 Nothing 0 Reject,
   go "wrong stored target after R transition rejected" 18 initial (update below [(16,999999)]) 0 30000 [] 0 0 Nothing 0 Reject,
   go "wrong R state after ONE swap rejected" 18 initial (update below [(18,1)]) 0 30000 [] 0 0 Nothing 0 Reject,
   go "invented swap recipient coupon rejected" 18 initial (update below [(5,below H.!!5+1),(8,below H.!!8-1)]) 0 30000 [] 0 0 Nothing 0 Reject,
   go "wrong trader signature rejected" 18 initial below 0 30000 [] 1 0 Nothing 0 Reject,
   go "out-of-domain owner price rejected" 16 initial (step initial [(19,2*D.one+1)]) 0 0 [0,2*D.one+1] 0 0 Nothing 0 Reject,
   go "native issuance cannot hide a1sat funding shortfall" 0 initial issueA 0 500 [] 0 499 Nothing 0 Reject,
   go "coupon maturity cannot use an earlier chosen lock height" 5 initial burnB 1 500 [] 1 0 (Just (1,500)) 800000 Reject,
   go "native burn destination is exact" 4 initial burnA 0 500 [] 0 0 (Just (1,500)) 800000 Reject]
entries=[pmmEntry]
