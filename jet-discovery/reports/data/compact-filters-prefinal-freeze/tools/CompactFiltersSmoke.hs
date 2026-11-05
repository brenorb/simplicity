{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM,unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Lib.CompactFilters
import qualified JetDiscovery.Ref.CompactFilters as R
import JetDiscovery.Types
import JetDiscovery.Run(progCmr,runVectors,VectorResult(..))
import JetDiscovery.Tx
import System.Exit(exitFailure)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
fields delimiter s=case break(==delimiter)s of(a,[])->[a];(a,_:b)->a:fields delimiter b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 hSetBuffering stdout LineBuffering
 let Just environment=mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 BL.empty 0xffffffff][mkOutput 999(unhex "51")]0)0 defaultTap(hashFromInteger 1)
 rows<-map(fields '\t').drop 1.lines <$>readFile "vendor-specs/bitcoin-growth4/bip158-all-vectors.tsv"
 assert "complete official source vector inventory10"(length rows==10)
 mapM_(\row->case row of
  [index,_,display,_,previous,encoded,expected,items,_,_]->do
   let serialized=unhex encoded;scripts=if null items then[]else map unhex(fields ',' items)
       candidates=if null scripts then[(unhex "51",False)]else[(head scripts,True)]
       absent=head[x|x<-map(B.singleton.fromIntegral)[1..255],R.matchBasic(R.displayHashToRaw display)serialized x==Just False]
       context script answer=Context(R.displayHashToRaw display)(R.displayHashToRaw previous)(R.displayHashToRaw expected)script answer
   mapM_(\(script,answer)->assert("row"++index++" actual Simplicity GCS/header query answer"++show answer)(J.fastEval(filterKernel(context script answer))environment(filterProof serialized)==Just()))(candidates++[(absent,False)])
   let malformed=[serialized<>B.singleton 0,B.take(B.length serialized-1)serialized]
       script=if null scripts then unhex "51"else head scripts
   mapM_(\bad->do
     let authenticatedMalformed=Context(R.displayHashToRaw display)(R.displayHashToRaw previous)(R.filterHeaderRaw bad(R.displayHashToRaw previous))script(not(null scripts))
     assert("row"++index++" malformed GCS rejected with its own valid filter-header hash")(J.fastEval(filterKernel authenticatedMalformed)environment(filterProof bad)==Nothing))malformed
   assert("row"++index++" false membership claim rejected")(J.fastEval(filterKernel(context absent True))environment(filterProof serialized)==Nothing)
  _->fail "source columns")rows
 entry>>=check
check(Entry ident _ _ _ _ _ make vectors)=do
 let first=case vectors of v:_->make(vecWitness v);_->error "empty"
     cmr=progCmr first
     eligible=case boundView first of Just(BoundView kernel _)->boundEligible kernel;_->False
 _<-evaluate eligible
 putStrLn(ident++" vectors="++show(length vectors)++" prepared_kernel_eligible="++show eligible++" CMR="++show cmr)
 results<-forM(runVectors make cmr vectors)$ \r -> do
  ok<-evaluate(vrOk r);putStrLn(vrName r++" expected="++show(vrExpect r)++" actual="++vrNote r++" pass="++show ok);return ok
 unless(eligible&&and results)exitFailure
 putStrLn "all complete compact-filter client vectors pass with per-vector canonical CMR"
