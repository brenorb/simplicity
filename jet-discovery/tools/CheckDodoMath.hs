{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding (drop,take)
import Control.Monad (forM,unless)
import System.Exit (exitFailure)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.DodoMath as D
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx

env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
check :: (Simplicity t,Primitive t,TyC a) => t a Word64 -> t (a,Word64) ()
check f=(take f&&&ih)>>>eq>>>verify
run :: TyC a => String -> (forall t. (Simplicity t,Primitive t) => t a Word64) -> [(String,a,Integer,Expect)] -> IO Bool
run label term cases=do
 let program=boundProgram (check term)
     vectors=[Vector name env (input,w64 expected) expect|(name,input,expected,expect)<-cases]
     cmr=progCmr (program (vecWitness (head vectors)))
 putStrLn (label++" START");hFlush stdout
 rows<-forM (runVectors program cmr vectors) $ \r->do
  putStrLn (label++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r);hFlush stdout
  pure (vrOk r)
 putStrLn (label++" "++show (length rows)++" vectors "++if and rows then "PASS" else "FAIL");hFlush stdout
 pure (and rows)
main=do
 args<-getArgs
 let want x=null args||x `elem` args
     one=D.one
     targets=[(1000000,0,one),(1000000,10000,one),(1000000,200000,one `div`2),(1000000,200000,2*one),(100,1,one),(10^9,10^8,one),(0,1,one)]
     trades=[(1000000,1000000,0,one),(1000000,1000000,10000,one),(1000000,900000,10000,one),(1000000,1100000,200000,one),(1000000,1000000,30000,one `div`2),(1000000,1000000,30000,2*one),(1000,1000,100000,one),(10^9,10^9,10^8,one)]
     integrals=[(1000000,1010000,1000000,one),(1000000,1100000,1050000,one),(1000000,1000000,900000,one),(1000,1001,1000,one),(10^9,10^9,9*10^8,2*one)]
 a<-if want "target" then run "DODO target k0.1" D.targetRef ([(show (v,d,i),(w64 v,(w64 d,w64 i)),D.targetInteger v d i,Accept)|(v,d,i)<-targets]++[("altered target",(w64 1000000,(w64 10000,w64 one)),D.targetInteger 1000000 10000 one+1,Reject)]) else pure True
 b<-if want "trade" then run "DODO trade k0.1" D.tradeRef ([(show (v0,v1,d,i),(w64 v0,(w64 v1,(w64 d,w64 i))),D.tradeInteger v0 v1 d i,Accept)|(v0,v1,d,i)<-trades]++[("altered trade",(w64 1000000,(w64 1000000,(w64 10000,w64 one))),D.tradeInteger 1000000 1000000 10000 one+1,Reject),("zero target",(w64 0,(w64 1000000,(w64 1,w64 one))),0,Reject),("zero reserve",(w64 1000000,(w64 0,(w64 1,w64 one))),0,Reject)]) else pure True
 c<-if want "integrate" then run "DODO integral k0.1" D.integrateRef ([(show (v0,v1,v2,i),(w64 v0,(w64 v1,(w64 v2,w64 i))),D.integrateInteger v0 v1 v2 i,Accept)|(v0,v1,v2,i)<-integrals]++[("altered integral",(w64 1000000,(w64 1010000,(w64 1000000,w64 one))),D.integrateInteger 1000000 1010000 1000000 one+1,Reject),("reversed interval",(w64 1000000,(w64 900000,(w64 1000000,w64 one))),0,Reject)]) else pure True
 unless (a&&b&&c) exitFailure
