{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding (drop,take)
import Control.Monad (unless)
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.BoundedSqrt as S
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx
main=do
 let env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
     program=boundProgram (((take S.sqrt128)&&&ih)>>>eq>>>verify)
     cases=[(show x,(toWord128 x,w64 (S.sqrtInteger x)),Accept)|x<-[0..100]++[10^36-1,10^36,10^36+1,2^128-1]]++[("altered square root",(toWord128 9,w64 4),Reject)]
     vectors=[Vector n env v expected|(n,v,expected)<-cases]
     cmr=progCmr (program (vecWitness (head vectors)))
     results=runVectors program cmr vectors
 mapM_ (\r->putStrLn (vrName r++"\t"++show (vrOk r)++"\t"++vrNote r)) results
 unless (all vrOk results) (error "integer sqrt vector failed")

 let program256=boundProgram (((take S.sqrt256)&&&ih)>>>eq>>>verify)
     values256=[0,1,2,3,4,9,10^36,10^44+12345,2^256-1]
     vectors256=[Vector (show x) env (w256 x,toWord128 (S.sqrtInteger x)) Accept|x<-values256]++[Vector "altered256-bit root" env (w256 9,toWord128 4) Reject]
     cmr256=progCmr (program256 (vecWitness (head vectors256)))
     results256=runVectors program256 cmr256 vectors256
 mapM_ (\r->putStrLn ("sqrt256 "++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r)) results256
 unless (all vrOk results256) (error "integer sqrt256 vector failed")
