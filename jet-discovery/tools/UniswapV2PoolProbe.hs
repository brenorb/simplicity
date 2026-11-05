{-# LANGUAGE RankNTypes #-}
module Main where
import Control.Monad (forM,unless)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Digest (hash0)
import Simplicity.Ty.Word (fromWord64,toWord64)
import System.Exit (exitFailure)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import JetDiscovery.Corpus.UniswapV2Pool (entries,referenceAudit)
import JetDiscovery.Lib.V2PoolMath (sqrt44Ref)
import qualified JetDiscovery.Ref.UniswapV2Pool as Ref
import JetDiscovery.Run
import JetDiscovery.Tx
import JetDiscovery.Types
main :: IO ()
main = do
 hSetBuffering stdout LineBuffering
 unless referenceAudit exitFailure
 let Just env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 500 mempty] 0) 0 defaultTap hash0
     evaluator = J.unwrap (J.jetSubst sqrt44Ref)
     root n = fmap fromWord64 (J.fastEval evaluator env (toWord64 n))
     bounds = [0,1,2,3,4,7,8,9,10,15,16,17,99,100,101,1023,1024,1025,2^44-1]
              ++ [k*k+d | k<-[37,3001,65535,999999,2^22-1],d<-[-1,0,1]]
 unless (all (\n -> root n==Just (Ref.sqrtInteger n)) bounds && root (2^44)==Nothing) exitFailure
 putStrLn (show (length bounds)++" native sqrt values and exclusive range bound: PASS")
 case entries of
   [Entry ident _ _ _ _ _ make vs@(v:_)] -> do
     let p=make(vecWitness v); cmr=progCmr p
     putStrLn (ident++" vectors="++show(length vs)++" CMR="++show cmr)
     results<-forM (runVectors make cmr vs) $ \r -> do
       putStrLn (vrName r++" expected="++show(vrExpect r)++" actual="++vrNote r++" pass="++show(vrOk r))
       pure(vrOk r)
     unless (length vs==32 && and results) exitFailure
   _ -> exitFailure
