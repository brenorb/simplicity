{-# LANGUAGE RankNTypes,ScopedTypeVariables #-}
-- | Three fully BTC-backed native coupon classes and a complete bounded pool
-- interface: issuance/transfer/redemption, swap, LP join/exit/transfer and fees.
module JetDiscovery.Corpus.StablePool where
import Prelude hiding (drop,take,not,and,or)
import qualified Prelude as H
import qualified Simplicity.Programs.Arith as A
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import qualified Simplicity.Bitcoin.Programs.TimeLock as TL
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.ClaimLedger
import qualified JetDiscovery.Lib.StableMath as S
import qualified JetDiscovery.Corpus.ContractGrowth as G
import JetDiscovery.Types
import Simplicity.Digest (Hash256)
import JetDiscovery.Tx (hashFromInteger)

-- Offchain signature-fixture CMR only, derived independently from the actual
-- unchanged typed program. The actual whole-program and vector checks remain.
stableFixtureCmr :: Hash256
stableFixtureCmr=hashFromInteger 0xd4d0a54c2f0a267534468b5d575cc34272811d2120b3ddaa950971e72a650fe2

nonceP :: Assert t => (Int,t Input Word64)
nonceP=(19,add (o 19) (k 1))
coinBalance source c=account (source (4+2*c)) (source (5+2*c))
setCoin c value=[(4+2*c,account value (o (4+2*c))),(5+2*c,account (o (5+2*c)) value)]
validPoolT :: Assert t => t Ledger ()
validPoolT=allChecks [le (sumT (map field [1..3])) (field 0),same (field 16) (add (field 17) (field 18)),allChecks [same (field (1+c)) (sumT (map field [4+2*c,5+2*c,10+c,13+c]))|c<-[0..2]],allChecks [same (field i) (k 0)|i<-[20..31]],select (is (field 16) (k 0)) (allChecks [same (field i) (k 0)|i<-[10..12]]) (allChecks [nonzero (field i)&&&le (field i) (k (10^9))>>>unit|i<-[10..12]])]
changesP source target xs=allChecks [same (target i) (maybe (source i) id (lookup i xs))|i<-[0..31]]
smallBal source=(source 10)&&&((source 11)&&&(source 12))
selectBalance index source=H.foldr (\c rest->select (is index (k (toInteger c))) (source c) rest) (k 0) [0..2]
balField 0=oh
balField 1=ioh
balField _=iih
type QInput=(S.Bal,((Word64,Word64),Word64))
quoteRef :: Assert t => t QInput (Word64,Word64)
quoteRef=(iden&&&(take S.curveDRefT))>>>((take iden)&&&y)>>>raw>>>(iden&&&floorR iden (k 4) (k 10000))>>>(sub oh ih&&&floorR ih (k 1) (k 2))
 where
  floorR a b d=(((a&&&b)&&&d)>>>G.ratioRef)>>>oh
  qi=drop (take oh);qj=drop (take ih);dx=drop ih
  chosen index=selectBalance index (\c->take (balField c))
  other=sumT [select (or (is (take qi) (k (toInteger c))) (is (take qj) (k (toInteger c)))) (k 0) (take (take (balField c)))|c<-[0..2]]
  y=(ih&&&(add (take (chosen qi)) (take dx)&&&other))>>>S.curveYRefT
  raw=sub (take (chosen qj)) (add ih (k 1))
quoteWrapped :: J.WrappedSimplicity QInput (Word64,Word64)
quoteWrapped=J.jetSubst quoteRef
{-# NOINLINE quoteWrapped #-}
poolT :: (Simplicity t,Primitive t) => CT t
poolT=allChecks [base,old>>>validPoolT,new>>>validPoolT,choose (claims++[(16,swap),(17,join),(18,exit),(19,adminPull),(20,transferLp)])]
 where
  claims=[(toInteger m,claim c action)|m<-[0..8],let c=m `mod`3,let action=m `div`3]
  claim c action=allChecks [actorSig,nonzero amount,case action of
   0->allChecks [changes ([(0,add (o 0) amount),(1+c,add (o (1+c)) amount),nonceP]++setCoin c (add (coinBalance o c) amount)),deposit amount]
   1->allChecks [changes [nonceP,(4+2*c,account (sub (o (4+2*c)) amount) (add (o (4+2*c)) amount)),(5+2*c,account (add (o (5+2*c)) amount) (sub (o (5+2*c)) amount))],noCash]
   _->allChecks [konst (w32 (800000+100000*toInteger c))>>>TL.checkLockHeight,changes ([(0,sub (o 0) amount),(1+c,sub (o (1+c)) amount),nonceP]++setCoin c (sub (coinBalance o c) amount)),withdraw amount actorDestination]]
  indices=allChecks [lt (aux 0) (k 3),lt (aux 1) (k 3),(aux 0&&&aux 1)>>>eq>>>not iden>>>verify]
  quote=(smallBal o&&&((aux 0&&&aux 1)&&&amount))>>>J.unwrap quoteWrapped
  os i=take (o i);ns i=take (n i)
  input t=take t
  swap=(allChecks [actorSig,nonzero amount,indices,nonzero (o 16)]&&&iden)>>>drop ((iden&&&quote)>>>allChecks [le (input (aux 2)) ioh,nonzero ioh,changesP os ns ([ (19,add (os 19) (k 1))]++concat [[(4+2*c,select (is (input actor) (k 0)) (updatedUser c (os (4+2*c))) (os (4+2*c))),(5+2*c,select (is (input actor) (k 1)) (updatedUser c (os (5+2*c))) (os (5+2*c))),(10+c,sub (add (os (10+c)) (ifIn c (input amount))) (ifOut c (add ioh iih))),(13+c,add (os (13+c)) (ifOut c iih))]|c<-[0..2]]),input noCash])
   where
    ifIn c value=select (is (input (aux 0)) (k (toInteger c))) value (k 0)
    ifOut c value=select (is (input (aux 1)) (k (toInteger c))) value (k 0)
    updatedUser c balance=add (sub balance (ifIn c (input amount))) (ifOut c ioh)
  -- Stage old/new D, every imbalance fee, and fee-adjusted D exactly once.
  rawReserve c=add (o (10+c)) (aux c)
  d0=select (is (o 16) (k 0)) (k 0) (smallBal o>>>S.curveD)
  d1=(rawReserve 0&&&(rawReserve 1&&&rawReserve 2))>>>S.curveD
  fee c=select (is (take (o 16)) (k 0)) (k 0) (G.floorRatio difference (k 3) (k 20000))
   where
    ideal=G.floorRatio iih (take (o (10+c))) ioh
    actual=take (rawReserve c)
    difference=select ((ideal&&&actual)>>>A.le word64) (sub actual ideal) (sub ideal actual)
  fees=fee 0&&&(fee 1&&&fee 2)
  feeAt c=drop (balField c)
  d2=select (is (take (take (o 16))) (k 0)) (take iih) ((net 0&&&(net 1&&&net 2))>>>S.curveD)
   where net c=sub (take (take (rawReserve c))) (feeAt c)
  jOld i=take (take (take (o i)));jNew i=take (take (take (n i)))
  jAmount c=take (take (take (aux c)))
  jActor=take (take (take actor))
  jFee c=take (drop (balField c))
  jD0=take (take ioh);jD1=take (take iih)
  mint=select (is (jOld 16) (k 0)) jD1 (G.floorRatio (jOld 16) (sub ih jD0) jD0)
  jAccount a b=select (is jActor (k 0)) a b
  join=(actorSig&&&iden)>>>drop ((iden&&&(d0&&&d1))>>>(iden&&&fees)>>>(iden&&&d2)>>>allChecks [nonzero mint,le (take (take (take (aux 3)))) mint,changesP jOld jNew ([(16,add (jOld 16) mint),(17,jAccount (add (jOld 17) mint) (jOld 17)),(18,jAccount (jOld 18) (add (jOld 18) mint)),(19,add (jOld 19) (k 1))]++concat [[(4+2*c,jAccount (sub (jOld (4+2*c)) (jAmount c)) (jOld (4+2*c))),(5+2*c,jAccount (jOld (5+2*c)) (sub (jOld (5+2*c)) (jAmount c))),(10+c,sub (add (jOld (10+c)) (jAmount c)) (G.floorRatio (jFee c) (k 1) (k 2))),(13+c,add (jOld (13+c)) (G.floorRatio (jFee c) (k 1) (k 2)))]|c<-[0..2]]),take (take (take noCash))])
  out c=G.floorRatio (o (10+c)) amount (o 16)
  outs=out 0&&&(out 1&&&out 2)
  ex c=drop (balField c)
  exit=(allChecks [actorSig,nonzero amount,le amount (account (o 17) (o 18))]&&&iden)>>>drop ((iden&&&outs)>>>allChecks [allChecks [le (take (aux c)) (ex c)|c<-[0..2]],changesP os ns ([(16,sub (os 16) (take amount)),(17,select (is (take actor) (k 0)) (sub (os 17) (take amount)) (os 17)),(18,select (is (take actor) (k 1)) (sub (os 18) (take amount)) (os 18)),(19,add (os 19) (k 1))]++concat [[(4+2*c,select (is (take actor) (k 0)) (add (os (4+2*c)) (ex c)) (os (4+2*c))),(5+2*c,select (is (take actor) (k 1)) (add (os (5+2*c)) (ex c)) (os (5+2*c))),(10+c,sub (os (10+c)) (ex c))]|c<-[0..2]]),take noCash])
  adminPull=allChecks [sigAt 3 0,nonzero amount,lt (aux 0) (k 3),chooseCoin [pull c|c<-[0..2]]]
   where
    chooseCoin branches=H.foldr (\(c,t) rest->select (is (aux 0) (k c)) t rest) failure (zip [0..] branches)
    pull c=allChecks [konst (w32 (800000+100000*toInteger c))>>>TL.checkLockHeight,changes [(0,sub (o 0) amount),(1+c,sub (o (1+c)) amount),(13+c,sub (o (13+c)) amount),nonceP],withdraw amount (destination 3)]
  transferLp=allChecks [actorSig,nonzero amount,changes [nonceP,(17,account (sub (o 17) amount) (add (o 17) amount)),(18,account (add (o 18) amount) (sub (o 18) amount))],noCash]

poolEntry=entry "app-stableswap-pool-transition" "Native three-claim StableSwap pool and LP lifecycle" "Curve3pool get_D/get_y/add_liquidity/exchange/remove_liquidity; pinned source"
 ["three BTC-backed coupon classes redeem after800000/900000/1000000; complete committed owner balances, supplies, pool/admin holdings and LP ownership; physical collateral>=totalA+totalB+totalC", "A100, equal native normalization units, exchange fee4/10000 and50% admin share; join imbalance fee3/20000 with source D0/D1/D2 rounding;32 Newton updates with convergence required, positive reserves<=1e9", "bounded native interface supports all6 swap directions, arbitrary3-coin deposits, proportional LP exit, LP transfer and native coupon/admin redemption; foreign single-coin/imbalance withdrawal APIs, token decimals, fee-on-transfer and ramp governance are unsupported"] poolT vectors
 where
  initial=update [] [(0,6000000),(1,2000000),(2,2000000),(3,2000000),(4,1000000),(5,1000000),(6,1000000),(7,1000000),(8,1000000),(9,1000000)]
  step state xs=update state ((19,state H.!!19+1):xs)
  bal state=[state H.!!(10+c)|c<-[0..2]]
  joinRef state who amounts=step state ([(16,state H.!!16+mint),(17+who,state H.!!(17+who)+mint)]++concat [[(4+2*c+who,state H.!!(4+2*c+who)-amounts H.!!c),(10+c,newBal H.!!c-admin H.!!c),(13+c,state H.!!(13+c)+admin H.!!c)]|c<-[0..2]])
   where
    oldBal=bal state;newBal=zipWith (+) oldBal amounts;supply=state H.!!16
    d0=if supply==0 then 0 else S.curveDInteger oldBal;d1=S.curveDInteger newBal
    fees=if supply==0 then [0,0,0] else [abs (d1*x `div`d0-y)*3 `div`20000|(x,y)<-zip oldBal newBal]
    admin=map (`div`2) fees;d2=S.curveDInteger (zipWith (-) newBal fees)
    mint=if supply==0 then d1 else supply*(d2-d0) `div`d0
  swapRef state who i j dx=step state [(4+2*i+who,state H.!!(4+2*i+who)-dx),(4+2*j+who,state H.!!(4+2*j+who)+dy),(10+i,state H.!!(10+i)+dx),(10+j,state H.!!(10+j)-dy-admin),(13+j,state H.!!(13+j)+admin)]
   where
    xs=bal state;d=S.curveDInteger xs;other=head [xs H.!!c|c<-[0..2],c/=i,c/=j];y=S.curveYInteger d (xs H.!!i+dx) other
    raw=xs H.!!j-y-1;fee=raw*4 `div`10000;dy=raw-fee;admin=fee `div`2
  exitRef state who shares=step state ([(16,state H.!!16-shares),(17+who,state H.!!(17+who)-shares)]++concat [[(4+2*c+who,state H.!!(4+2*c+who)+q),(10+c,state H.!!(10+c)-q)]|c<-[0..2],let q=state H.!!(10+c)*shares `div`(state H.!!16)])
  joined=joinRef initial 0 [500000,500000,500000]
  imbalanced=joinRef joined 1 [100000,0,0]
  swapped=swapRef imbalanced 1 0 1 10000
  exited=exitRef swapped 0 100000
  lpMoved=step swapped [(17,swapped H.!!17-10000),(18,swapped H.!!18+10000)]
  drained=exitRef joined 0 (joined H.!!16)
  adminBurn=step imbalanced [(0,5999999),(1,1999999),(13,imbalanced H.!!13-1)]
  issueC=step initial [(0,6000500),(3,2000500),(9,1000500)]
  transferC=step initial [(8,999500),(9,1000500)]
  redeemC=step initial [(0,5999500),(3,1999500),(9,999500)]
  v=vectorBound stableFixtureCmr
  go label action a b who quantity args signer funding payout height expected=v label poolT action a b who quantity args [signer] funding payout height expected
  directions=[go ("exact swap direction"++show (i,j)) 16 imbalanced (swapRef imbalanced 1 i j 10000) 1 10000 [toInteger i,toInteger j,1] 1 0 Nothing 0 Accept|i<-[0..2],j<-[0..2],i/=j,(i,j)/=(0,1)]
  vectors=directions++[go "initial three-coin deposit mints exact D LP" 17 initial joined 0 0 [500000,500000,500000,0] 0 0 Nothing 0 Accept,
   go "imbalanced deposit charges fees before D2 LP issuance" 17 joined imbalanced 1 0 [100000,0,0,0] 1 0 Nothing 0 Accept,
   go "Newton swap updates reserves and half admin fee" 16 imbalanced swapped 1 10000 [0,1,1] 1 0 Nothing 0 Accept,
   go "proportional LP burn credits all three owned claims" 18 swapped exited 0 100000 [0,0,0] 0 0 Nothing 0 Accept,
   go "LP transfer moves real reserve ownership" 20 swapped lpMoved 0 10000 [] 0 0 Nothing 0 Accept,
   go "complete LP exit empties reserves safely" 18 joined drained 0 (joined H.!!16) [0,0,0] 0 0 Nothing 0 Accept,
   go "administrator burns backed A fee into native payout" 19 imbalanced adminBurn 0 1 [0] 3 0 (Just (3,1)) 800000 Accept,
   go "third coupon issuance requires real native input" 2 initial issueC 1 500 [] 1 500 Nothing 0 Accept,
   go "third coupon transfer preserves supply" 5 initial transferC 0 500 [] 0 0 Nothing 0 Accept,
   go "third coupon burn uses later native maturity" 8 initial redeemC 1 500 [] 1 0 (Just (1,500)) 1000000 Accept,
   go "swap cannot choose identical input/output class" 16 imbalanced swapped 1 10000 [0,0,0] 1 0 Nothing 0 Reject,
   go "swap cannot substitute an optimistic quote" 16 imbalanced (update swapped [(7,swapped H.!!7+1),(11,swapped H.!!11-1)]) 1 10000 [0,1,1] 1 0 Nothing 0 Reject,
   go "swap minimum output is enforced" 16 imbalanced swapped 1 10000 [0,1,100000] 1 0 Nothing 0 Reject,
   go "join LP supply cannot inflate one unit" 17 joined (update imbalanced [(16,imbalanced H.!!16+1),(18,imbalanced H.!!18+1)]) 1 0 [100000,0,0,0] 1 0 Nothing 0 Reject,
   go "initial join must fund every positive reserve" 17 initial joined 0 0 [500000,0,500000,0] 0 0 Nothing 0 Reject,
   go "wrong owner cannot burn LP" 18 swapped exited 0 100000 [0,0,0] 1 0 Nothing 0 Reject,
   go "admin native redemption binds fee recipient" 19 imbalanced adminBurn 0 1 [0] 3 0 (Just (1,1)) 800000 Reject,
   go "third coupon cannot redeem at B maturity" 8 initial redeemC 1 500 [] 1 0 (Just (1,500)) 900000 Reject]
entries=[poolEntry]
