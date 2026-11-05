{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Complete bounded native V3 two-position market. The only crossable tick is
-- zero; price limits cannot cross either endpoint. Each adjacent range has one
-- fixed position owner and exact Q128 fee growth since its last LP checkpoint.
module JetDiscovery.Corpus.NativeV3Pool where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import Simplicity.Term.Core
import qualified Simplicity.Programs.Bit as B
import qualified Simplicity.Programs.Arith as A
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.ClaimLedger
import qualified JetDiscovery.Lib.LogExpBounded as L
import qualified JetDiscovery.Lib.V3BoundedMath as V
import qualified JetDiscovery.Lib.V3FiniteSwap as F
import JetDiscovery.Types
import Simplicity.Digest (Hash256)
import JetDiscovery.Tx (hashFromInteger)

-- Offchain fixture only: independently derived from the full typed kernel.
-- The native driver checks exact canonical parity before vector execution.
v3FixtureCmr :: Hash256
v3FixtureCmr=hashFromInteger 0x1cb95c48fcee2dcd5d809ed6e4fd29d9cbc6fcea6762c8c370455d7761a90a8c

-- 7/8 pool balances include both positions' owed claims. Owed and accrued
-- fees are liabilities against those balances, never a second asset supply.
-- 9/10 L0/L1;11/12 sqrtPriceX96;13 side;14 nonce;16..23 fee-growth deltas;
-- 24..27 owed0A/0B/1A/1B. No witness-provided tick or liquidity hints.
wide source offset=source offset&&&source (offset+1)
price source=wide source 11
side source=is (source 13) (k 1)
growthAt band tokenB=16+4*band+(if tokenB then 2 else 0)
owedAt band tokenB=24+2*band+(if tokenB then 1 else 0)
earned source band tokenB=(wide source (growthAt band tokenB)&&&source (9+band))>>>V.earned
validV3Ref :: Assert t => t Ledger ()
validV3Ref=allChecks [le (add (field 1) (field 2)) (field 0),same (field 1) (sumT (map field [3,4,7])),same (field 2) (sumT (map field [5,6,8])),F.inside (price field),le (field 13) (k 1),F.sideConsistent (price field) (side field),le (field 9) (k (10^9)),le (field 10) (k (10^9)),le (owed False) (field 7),le (owed True) (field 8),allChecks [same (field i) (k 0)|i<-[15]++[28..31]],allChecks [select (is (field (9+i)) (k 0)) (allChecks [same (field j) (k 0)|j<-[16+4*i..19+4*i]]) unit|i<-[0,1]]]
 where owed b=sumT [field (owedAt 0 b),field (owedAt 1 b),earned field 0 b,earned field 1 b]
validWrapped :: J.WrappedSimplicity Ledger ()
validWrapped=J.jetSubst validV3Ref
{-# NOINLINE validWrapped #-}
validV3 :: Simplicity t => t Ledger ()
validV3=J.unwrap validWrapped

v3T :: (Simplicity t,Primitive t) => CT t
v3T=allChecks [base,old>>>validV3,new>>>validV3,choose (claimBranches++[(16,modify True),(17,modify False),(18,collect),(20,swap True),(21,swap False)])]
 where
  leftOwner=is actor (k 0)
  ownerL=account (o 9) (o 10)
  ownerOwed b=account (o (owedAt 0 b)) (o (owedAt 1 b))
  priceLimit=aux 0&&&aux 1
  lpQuote mint=(price o&&&((leftOwner&&&konst (toBit mint))&&&amount))>>>F.lpAmounts
  fees=(account (earned o 0 False) (earned o 1 False))&&&(account (earned o 0 True) (earned o 1 True))
  modify mint=(allChecks [actorSig,if mint then nonzero amount else nonzero ownerL]&&&iden)>>>drop ((iden&&&(lpQuote mint&&&fees))>>>modifyChecks mint)
  modifyChecks mint=allChecks [changesAt op np [] ([(9,accountP nextL (op 9)),(10,accountP (op 10) nextL),(14,add (op 14) (k 1))]++assetChanges False++assetChanges True++reset),take noCash]
   where
    op i=take (o i);np i=take (n i)
    accountP a b=select (take leftOwner) a b
    nextL=(if mint then add else sub) (take ownerL) (take amount)
    qty b=drop (take (if b then ih else oh))
    accrued b=drop (drop (if b then ih else oh))
    nextOwed b=add (add (take (ownerOwed b)) (accrued b)) (if mint then k 0 else qty b)
    assetChanges b=let {a=owedAt 0 b; c=owedAt 1 b; pool=if b then 8 else 7; u=if b then 5 else 3; w=u+1; owned=sub (take (userBalance b o)) (qty b)} in
      [(a,accountP (nextOwed b) (op a)),(c,accountP (op c) (nextOwed b))]++if mint then [(pool,add (op pool) (qty b)),(u,accountP owned (op u)),(w,accountP (op w) owned)] else []
    reset=[(i,select (take leftOwner) (if i<20 then k 0 else op i) (if i<20 then op i else k 0))|i<-[16..23]]
  collectQuote=((aux 0&&&ownerOwed False)>>>A.min word64)&&&((aux 1&&&ownerOwed True)>>>A.min word64)
  collect=(actorSig&&&iden)>>>drop ((iden&&&collectQuote)>>>collectChecks)
  collectChecks=allChecks [nonzero (add ioh iih),changesAt op np [] ([(14,add (op 14) (k 1))]++pay False++pay True),take noCash]
   where
    op i=take (o i);np i=take (n i)
    accountP a b=select (take leftOwner) a b
    pay b=let {qty=if b then iih else ioh; a=owedAt 0 b; c=owedAt 1 b; u=if b then 5 else 3; w=u+1; pool=if b then 8 else 7; credit=add (take (userBalance b o)) qty} in
      [(a,accountP (sub (op a) qty) (op a)),(c,accountP (op c) (sub (op c) qty)),(u,accountP credit (op u)),(w,accountP (op w) credit),(pool,sub (op pool) qty)]
  swapQuote isIn=((price o&&&priceLimit)&&&((o 9&&&o 10)&&&(side o&&&(konst (toBit isIn)&&&amount))))>>>F.fill
  swap isIn=(actorSig&&&iden)>>>drop ((iden&&&swapQuote isIn)>>>swapChecks isIn)
  swapChecks isIn=allChecks [nonzero spent,nonzero received,le (if isIn then spent else received) (take amount),select (is (take (aux 2)) (k 0)) unit (le spent (take (aux 2))),le (take (aux 3)) received,changesAt op np [16..23] ([(11,drop oh>>>oh),(12,drop oh>>>ih),(13,select (drop ioh) (k 1) (k 0)),(14,add (op 14) (k 1))]++settle False++settle True),allChecks [same (wide np i) (L.add (wide op i) (select (tokenIn b) (growth band) (L.ks 0)))|band<-[0,1],b<-[False,True],let i=growthAt band b],take noCash]
   where
    op i=take (o i);np i=take (n i)
    down=L.lt (take priceLimit) (take (price o))
    tokenIn b=if b then B.not down else down
    spent=drop iioh
    received=drop (drop (drop (drop oh)))
    growth band=drop (drop (drop (drop ih)))>>>if band==0 then oh else ih
    accountP a b=select (take leftOwner) a b
    settle b=let {pool=if b then 8 else 7; u=if b then 5 else 3; w=u+1; user=take (userBalance b o);balance=select (tokenIn b) (sub user spent) (add user received); reserve=select (tokenIn b) (add (op pool) spent) (sub (op pool) received)} in
      [(u,accountP balance (op u)),(w,accountP (op w) balance),(pool,reserve)]
  changesAt src dst exclude updates=allChecks [same (dst i) (maybe (src i) id (lookup i updates))|i<-[0..31],i `notElem`exclude]

-- Independent Integer fixture transitions; no offchain quote is a script input.
wordPair n=[n `div`2^64,n `mod`2^64]
wideInteger state i=(state H.!!i)*2^64+state H.!!(i+1)
putWide i n=zip [i,i+1] (wordPair n)
step state xs=update state ((14,state H.!!14+1):xs)
lpReference state owner mint liq=step state ([(9+owner,(state H.!!(9+owner))+(if mint then liq else negate liq))]++concat [asset b q|(b,q)<-[(False,a),(True,b)]]++[(i,0)|i<-[16+4*owner..19+4*owner]])
 where
  (a,b)=F.lpInteger (wideInteger state 11) (owner==0) mint liq
  asset tokenB q=let { idx=owedAt owner tokenB; pool=if tokenB then 8 else 7; user=(if tokenB then 5 else 3)+owner; fee=wideInteger state (growthAt owner tokenB)*(state H.!!(9+owner)) `div`V.q128 } in
   [(idx,state H.!!idx+fee+(if mint then 0 else q))]++if mint then [(pool,state H.!!pool+q),(user,state H.!!user-q)] else []
collectReference state owner capA capB=step state (asset False capA++asset True capB)
 where
  asset tokenB cap=let { idx=owedAt owner tokenB; pool=if tokenB then 8 else 7; user=(if tokenB then 5 else 3)+owner; q=min cap (state H.!!idx) } in
   [(idx,state H.!!idx-q),(pool,state H.!!pool-q),(user,state H.!!user+q)]
swapReference state owner isIn quantity limit=(step state (putWide 11 finalPrice++[(13,if finalLeft then 1 else 0)]++asset False++asset True++concat [putWide i (wideInteger state i+g)|(band,g)<-[(0,g0),(1,g1)],let i=growthAt band (notH down)]),paid,received)
 where
  oldPrice=wideInteger state 11
  down=limit<oldPrice
  notH x=if x then False else True
  (finalPrice,finalLeft,paid,received,g0,g1)=F.fillInteger oldPrice limit (state H.!!9) (state H.!!10) (state H.!!13==1) isIn quantity
  asset tokenB=let { pool=if tokenB then 8 else 7; user=(if tokenB then 5 else 3)+owner; delta=if tokenB/=down then paid else negate received } in
   [(pool,state H.!!pool+delta),(user,state H.!!user-delta)]
swapArgs limit cap floorOut=wordPair limit++[cap,floorOut]

v3Entry=entry "app-concentrated-pool-swap" "Native two-range Uniswap V3 concentrated pool" "Pinned Uniswap V3 Pool/SwapMath/SqrtPriceMath/Tick/Position/TickMath; exact supported step and LP rounding"
 ["two adjacent fixed position ranges [-120,0) and [0,120), one fixed owner per range; the complete finite map is derived from both committed liquidities. Exact sqrtPriceX96 and boundary side determine active band; no generic tick index or external map witness", "strictly interior limits, only tick0 can be crossed, at most two exact source steps. Both directions and exact-input/output modes, actual consumed amount at price limit, optional spend/receive limits. Fee3000/1e6 and protocol fee0; liquidity and requested amounts<=1e9", "Q128 fee growth is accumulated per active band since its last LP update. With one position per band this is the source inside-growth difference, without redundant global/outside fields. Checkpoint/mint/burn settle source floor(growth*oldL/2^128) then reset that delta; growth must fit128 bits. Collect only owed balances, never unchecked pending fees", "mint rounds token amounts up, burn rounds down and records owed principal until collection; zero burn checkpoints an existing position. Two independently fully BTC-backed coupons, explicit pool/user/supply conservation and actual native coupon funding/redemption. One initialized lineage; no arbitrary additional ticks, oracle observations, flash/callback or foreign NFT transfer claim"] v3T vectors
 where
  midLeft=78990846045029531151608375686 -- TickMath(-60)
  midRight=79466191966197645195421774833 -- TickMath(60)
  initial=update [] ([(0,40000000),(1,20000000),(2,20000000),(3,10000000),(4,10000000),(5,10000000),(6,10000000),(13,1)]++putWide 11 midLeft)
  leftMint=lpReference initial 0 True 100000000
  bothMint=lpReference leftMint 1 True 200000000
  (up,upPaid,upOut)=swapReference bothMint 1 True 1000000 midRight
  (down,_,_)=swapReference up 0 True 800000 midLeft
  (withinLeft,_,_)=swapReference bothMint 1 True 100000 ((F.lower+midLeft) `div`2)
  (withinRight,_,_)=swapReference up 0 True 100000 ((F.upper+midRight) `div`2)
  (outDown,_,_)=swapReference up 1 False 100000 midLeft
  (outUp,_,_)=swapReference bothMint 1 False 600000 midRight
  (boundary,_,_)=swapReference bothMint 1 True 1000000 V.q96
  (zeroCrossDown,_,_)=swapReference boundary 0 True 100000 midLeft
  leftClosed=lpReference bothMint 0 False 100000000
  (emptyCrossUp,_,_)=swapReference leftClosed 1 True 100000 midRight
  pokeLeft=lpReference up 0 False 0
  pokeRight=lpReference withinRight 1 False 0
  collectLeft=collectReference pokeLeft 0 0 (pokeLeft H.!!25)
  collectRight=collectReference pokeRight 1 0 ((pokeRight H.!!27) `div`2)
  burnLeft=lpReference down 0 False 5000000
  collectBurn=collectReference burnLeft 0 (burnLeft H.!!24) (burnLeft H.!!25)
  issueA=step initial [(0,40000500),(1,20000500),(3,10000500)]
  issueB=step initial [(0,40000700),(2,20000700),(6,10000700)]
  moveA=step initial [(3,9999500),(4,10000500)]
  moveB=step initial [(5,10000500),(6,9999500)]
  burnA=step initial [(0,39999500),(1,19999500),(3,9999500)]
  burnB=step initial [(0,39999500),(2,19999500),(6,9999500)]
  poor=update initial [(3,0),(4,20000000)]
  wrongCollect=update collectLeft [(5,pokeLeft H.!!5),(6,pokeLeft H.!!6+pokeLeft H.!!25)]
  v=vectorBound v3FixtureCmr
  go label mode a b who q extra signer fund payout height expected=v label v3T mode a b who q extra [signer] fund payout height expected
  swapV label isIn oldState newState who q limit=go label (if isIn then 20 else 21) oldState newState (toInteger who) q (swapArgs limit 0 1) who 0 Nothing 0 Accept
  forgedOld=update bothMint [(9,100000001)]
  forged=let x=go "actual input cannot substitute committed active liquidity" 20 forgedOld up 1 1000000 (swapArgs midRight 0 0) 1 0 Nothing 0 Reject in resignVector v3FixtureCmr [1] (x {vecEnv=environment bothMint up 0 Nothing 0})
  positives=[
   go "left-range mint pays both rounded-up deltas" 16 initial leftMint 0 100000000 [] 0 0 Nothing 0 Accept,
   go "inactive right-range mint pays token0 only" 16 leftMint bothMint 1 200000000 [] 1 0 Nothing 0 Accept,
   swapV "upward exact input crosses tick0 and allocates fee growth to both bands" True bothMint up 1 1000000 midRight,
   swapV "downward exact input crosses tick0 back" True up down 0 800000 midLeft,
   swapV "partial exact input inside left band" True bothMint withinLeft 1 100000 ((F.lower+midLeft) `div`2),
   swapV "partial exact input inside right band" True up withinRight 0 100000 ((F.upper+midRight) `div`2),
   swapV "downward exact output uses source next-price rounding" False up outDown 1 100000 midLeft,
   swapV "upward exact output crosses tick0" False bothMint outUp 1 600000 midRight,
   swapV "hitting limit at tick0 still switches active side" True bothMint boundary 1 1000000 V.q96,
   swapV "zero-cost boundary crossing then uses committed left liquidity" True boundary zeroCrossDown 0 100000 midLeft,
   go "burn all left liquidity creates owed principal" 17 bothMint leftClosed 0 100000000 [] 0 0 Nothing 0 Accept,
   swapV "empty left interval traverses without fabricated liquidity" True leftClosed emptyCrossUp 1 100000 midRight,
   go "zero burn checkpoints exact earned left fees" 17 up pokeLeft 0 0 [] 0 0 Nothing 0 Accept,
   go "right checkpoint rounds cumulative two-swap Q128 growth once" 17 withinRight pokeRight 1 0 [] 1 0 Nothing 0 Accept,
   go "collect exact owed fee into left owner balance" 18 pokeLeft collectLeft 0 0 [0,pokeLeft H.!!25] 0 0 Nothing 0 Accept,
   go "partial right fee collection preserves remaining owed" 18 pokeRight collectRight 1 0 [0,(pokeRight H.!!27) `div`2] 1 0 Nothing 0 Accept,
   go "partial LP burn rounds principal down and records owed" 17 down burnLeft 0 5000000 [] 0 0 Nothing 0 Accept,
   go "collect burned principal and checkpointed fees" 18 burnLeft collectBurn 0 0 [burnLeft H.!!24,burnLeft H.!!25] 0 0 Nothing 0 Accept,
   go "native A coupon issuance uses actual funding" 0 initial issueA 0 500 [] 0 500 Nothing 0 Accept,
   go "native B coupon issuance uses actual funding" 1 initial issueB 1 700 [] 1 700 Nothing 0 Accept,
   go "native A transfer preserves supply" 2 initial moveA 0 500 [] 0 0 Nothing 0 Accept,
   go "native B transfer preserves supply" 3 initial moveB 1 500 [] 1 0 Nothing 0 Accept,
   go "native A burn pays at its lower height" 4 initial burnA 0 500 [] 0 0 (Just (0,500)) 800000 Accept,
   go "native B burn pays at its separate lower height" 5 initial burnB 1 500 [] 1 0 (Just (1,500)) 900000 Accept]
  negatives=[forged,
   go "cannot mint liquidity without owned coupons" 16 poor leftMint 0 100000000 [] 0 0 Nothing 0 Reject,
   go "LP burn needs the correct position owner" 17 bothMint leftClosed 0 100000000 [] 1 0 Nothing 0 Reject,
   go "cannot burn more than actual position liquidity" 17 bothMint leftClosed 0 100000001 [] 0 0 Nothing 0 Reject,
   go "cannot collect pending fees before checkpoint" 18 up (step up []) 0 0 [0,1000000] 0 0 Nothing 0 Reject,
   go "collect cannot move owned fee to the other account" 18 pokeLeft wrongCollect 0 0 [0,pokeLeft H.!!25] 0 0 Nothing 0 Reject,
   go "tick0 side cannot remain stale at price limit" 20 bothMint (update boundary [(13,1)]) 1 1000000 (swapArgs V.q96 0 0) 1 0 Nothing 0 Reject,
   go "successor sqrt price must match exact source step" 20 bothMint (update up (putWide 11 (wideInteger up 11+1))) 1 1000000 (swapArgs midRight 0 0) 1 0 Nothing 0 Reject,
   go "fee growth cannot credit wrong input token" 20 bothMint (update up (putWide 16 1)) 1 1000000 (swapArgs midRight 0 0) 1 0 Nothing 0 Reject,
   go "swap cannot alter the committed post-cross position liquidity" 20 bothMint (update up [(10,200000001)]) 1 1000000 (swapArgs midRight 0 0) 1 0 Nothing 0 Reject,
   go "swap maximum paid amount enforced" 20 bothMint up 1 1000000 (swapArgs midRight (upPaid-1) 0) 1 0 Nothing 0 Reject,
   go "swap minimum received amount enforced" 20 bothMint up 1 1000000 (swapArgs midRight 0 (upOut+1)) 1 0 Nothing 0 Reject,
   go "unsupported outer tick endpoint cannot be crossed" 20 bothMint withinLeft 1 100000 (swapArgs F.lower 0 0) 1 0 Nothing 0 Reject,
   go "coupon issue cannot fabricate actual input funding" 0 initial issueA 0 500 [] 0 499 Nothing 0 Reject,
   go "native B burn cannot redirect actual output" 5 initial burnB 1 500 [] 1 0 (Just (0,500)) 900000 Reject]
  vectors=positives++negatives
entries=[v3Entry]
