{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding (drop,take)
import Control.Monad (forM,unless)
import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hFlush,stdout)
import Simplicity.Term.Core
import Simplicity.Programs.Bit (verify)
import Simplicity.Programs.Generic (eq)
import Simplicity.Bitcoin.Term (Simplicity,Primitive)
import Simplicity.Ty.Word hiding (Vector)
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.Fixed192Bounded as F
import JetDiscovery.Run
import JetDiscovery.Types
import JetDiscovery.Tx
env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
check :: (Simplicity t,Primitive t,TyC a,TyC b) => t a b -> t (a,b) ()
check f=(take f&&&ih)>>>eq>>>verify
run :: (TyC a,TyC b) => String -> (forall t. (Simplicity t,Primitive t)=>t a b) -> [(String,a,b,Expect)] -> IO Bool
run label term rows=do
 let program=boundProgram (check term)
     vectors=[Vector name env (input,expected) ex|(name,input,expected,ex)<-rows]
     cmr=progCmr (program (vecWitness (head vectors)))
 putStrLn (label++" START");hFlush stdout
 oks<-forM (runVectors program cmr vectors) $ \r->do
  putStrLn (label++"\t"++vrName r++"\t"++show (vrOk r)++"\t"++vrNote r);hFlush stdout
  pure (vrOk r)
 putStrLn (label++" "++show (length oks)++" vectors "++if and oks then "PASS" else "FAIL");hFlush stdout
 pure (and oks)
main=do
 args<-getArgs
 let want x=null args||x `elem`args
     one=F.one
     powCases=[0,1,one `div`2,one,one+one `div`3,63*one+one `div`2,64*one,64*one+1,128*one,160*one+123,3394200909562557497344,184*one,191*one,192*one-1]
     logCases=[one,one+1,2*one,3*one,2^128-1,2^128,2^192,2^248,2^248+2^200,2^249-1,2^256-1]
 a<-if want "pow" then run "Gnosis pow2Upper" F.pow2Upper ([(show x,toWord128 x,w256 (F.pow2UpperInteger x),Accept)|x<-powCases]++[("altered upper bound",toWord128 (184*one),w256 (F.pow2UpperInteger (184*one)+1),Reject),("exponent domain",toWord128 (192*one),w256 0,Reject)]) else pure True
 b<-if want "log" then run "Gnosis binaryLogUpper" F.log2Upper ([(show x,w256 x,toWord128 (F.log2UpperInteger x),Accept)|x<-logCases]++[("altered log upper",w256 (2*one),toWord128 (one+5),Reject),("zero log domain",w256 0,toWord128 0,Reject),("below admitted ONE",w256 (one-1),toWord128 0,Reject)]) else pure True
 unless (a&&b) exitFailure
