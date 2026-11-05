{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding (drop,take)
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.LmsrCost as L
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx
amount x=(toBit (x<0),w64 (abs x))
encode (f,a,b,qa,qb,expected)=((w64 f,((w64 a,w64 b),(amount qa,amount qb))),amount expected)
check :: (Simplicity t,Primitive t) => t (L.Input,L.Output) ()
check=(take L.cost&&&ih)>>>eq>>>verify
env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
main=do
 let funding=1000000
     buy=L.costInteger funding funding funding 10000 0
     afterA=funding+buy-10000
     afterB=funding+buy
     cases=[(funding,funding,funding,0,0),(funding,funding,funding,10000,0),(funding,funding,funding,0,10000),(funding,funding,funding,10000,10000),(funding,funding,funding,-10000,-10000),(funding,afterA,afterB,-5000,0),(funding,afterA,afterB,0,5000),(funding,afterA,afterB,10000,-10000),(1000,1000,1000,1,0),(1000,1000,1000,1000,0),(1000,10000,0,-1000,1000),(funding,5000000,9000000,-funding,funding)]
     vectors=[Vector (show (f,a,b,qa,qb)) env (f,a,b,qa,qb,L.costInteger f a b qa qb) Accept|(f,a,b,qa,qb)<-cases]++[Vector "cheapened buy" env (funding,funding,funding,10000,0,buy-1) Reject,Vector "funding below bound" env (999,999,999,1,0,0) Reject,Vector "inventory bound" env (1000,10001,1000,1,0,0) Reject,Vector "trade bound" env (1000,1000,1000,1001,0,0) Reject]
     program=boundProgram check . encode
     cmr=progCmr (program (vecWitness (head vectors)))
 putStrLn "LMSR exact two-outcome cost START";hFlush stdout
 oks<-forM (runVectors program cmr vectors) $ \r->do
  putStrLn (vrName r++"\t"++show (vrOk r)++"\t"++vrNote r);hFlush stdout
  pure (vrOk r)
 putStrLn ("LMSR cost "++show (length oks)++" vectors "++if and oks then "PASS" else "FAIL")
 unless (and oks) exitFailure
