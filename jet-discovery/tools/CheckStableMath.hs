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
import qualified JetDiscovery.Lib.StableMath as S
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx

type I=(S.Bal,Word64)
check :: (Simplicity t,Primitive t) => t S.Bal Word64 -> t I ()
check f=((take f)&&&ih)>>>eq>>>verify
encode ([a,b,c],expected)=((w64 a,(w64 b,w64 c)),w64 expected)
encode _=error "three balance helper input"
env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
run :: String -> (forall t. (Simplicity t,Primitive t) => t S.Bal Word64) -> [Vector ([Integer],Integer)] -> IO Bool
run label f vectors=do
 let program=boundProgram (check f) . encode
     cmr=progCmr (program (vecWitness (head vectors)))
     rows=runVectors program cmr vectors
 oks<-forM rows $ \r->do
  putStrLn (label++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r)
  hFlush stdout
  pure (vrOk r)
 pure (and oks)
main=do
 let dCases=[[1000000,1000000,1000000],[1000000,2000000,4000000],[1,1000,1000000],[10^9,10^9,10^9]]
     yCases=[(3000000,1010000,1000000),(S.curveDInteger [1000000,2000000,4000000],1100000,4000000),(3000000000,1000000000,1000000000)]
 a<-run "get_D128" S.curveD ([Vector (show xs) env (xs,S.curveDInteger xs) Accept|xs<-dCases]++[Vector "altered D" env ([1000000,1000000,1000000],3000001) Reject,Vector "zero reserve" env ([0,1000000,1000000],0) Reject,Vector "balance bound" env ([10^9+1,10^9,10^9],0) Reject])
 b<-run "get_y128" S.curveY ([Vector (show (d,x,k)) env ([d,x,k],S.curveYInteger d x k) Accept|(d,x,k)<-yCases]++[Vector "altered y" env ([3000000,1010000,1000000],S.curveYInteger 3000000 1010000 1000000+1) Reject,Vector "zero replacement reserve" env ([3000000,0,1000000],0) Reject])
 unless (a&&b) exitFailure
