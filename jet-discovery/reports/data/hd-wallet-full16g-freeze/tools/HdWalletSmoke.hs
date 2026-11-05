{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM,unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word
import JetDiscovery.Lib.HdWallet
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Ref.Bip340 as R
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import JetDiscovery.Tx
import System.Environment(getArgs)
import System.Exit(exitFailure)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 hSetBuffering stdout LineBuffering
 args<-getArgs
 if args==["core"]then core else if args==["all"]then core>>(entry>>=check)else entry>>=check
core=do
 let Just env=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 BL.empty 0xffffffff][mkOutput 999(unhex "51")]0)0 defaultTap(hashFromInteger 1)
 rows<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth6/bip32-public-ckd-vectors.tsv"
 assert "all6source publicCKD cases present"(length rows==6)
 mapM_(\row->case row of
  [group,path,parent,chain,index,_,_,expected,expectedChain,_,_]->do
   let public=unhex parent
       input=(w8(toInteger(B.head public)),w256FromBytes(B.tail public))
       actual=J.fastEval(ckdPublic(w256FromBytes(unhex chain))input)env(w32(read index))
       encoded=case actual of Just((x,y),code)->Just(B.singleton(if odd(fromWord256 y)then 3 else 2)<>w256ToBytes x,w256ToBytes code);_->Nothing
   assert("source"++group++" "++path++" actual HMAC+CKDpub point+chain")(encoded==Just(unhex expected,unhex expectedChain))
  _->fail "source public columns")rows
 let first=head rows;parent=unhex(first!!2);public=(w8(toInteger(B.head parent)),w256FromBytes(B.tail parent));private=R.intFromBytes(unhex(first!!9))
     digest il=(w256 il,w256 0)
     scalarCase il=J.fastEval(ckdFromDigest public)env(digest il)
     expectedPoint=case R.pointMul R.gPt private of Just(x,y)->(w256 x,w256 y);_->error "parent"
 assert "IL0 valid CKDpub keeps parent point"(scalarCase 0==Just(expectedPoint,w256 0))
 assert "IL=n rejects before scalar reduction"(scalarCase R.n==Nothing)
 assert "canonical IL yielding infinity rejects"(scalarCase(R.n-private)==Nothing)
check(Entry ident _ _ _ _ _ make vectors)=do
 let first=case vectors of v:_->make(vecWitness v);_->error "empty"
     cmr=progCmr first
     eligible=case boundView first of Just(BoundView kernel _)->boundEligible kernel;_->False
 _<-evaluate eligible
 putStrLn(ident++" vectors="++show(length vectors)++" prepared_kernel_eligible="++show eligible++" CMR="++show cmr)
 results<-forM(runVectors make cmr vectors)$ \r->do
  ok<-evaluate(vrOk r);putStrLn(vrName r++" expected="++show(vrExpect r)++" actual="++vrNote r++" pass="++show ok);return ok
 unless(eligible&&and results)exitFailure
 putStrLn "all native public-HD wallet vectors pass with per-vector canonical CMR"
