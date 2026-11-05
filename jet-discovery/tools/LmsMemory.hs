{-# LANGUAGE GADTs #-}
-- Compile after the current library build, then use /usr/bin/time -l and +RTS -s.
module Main where
import Control.Exception (evaluate)
import System.IO (hFlush,stdout)
import qualified JetDiscovery.Corpus.Lms as Lms
import qualified JetDiscovery.Ref.Lms as Ref
import qualified JetDiscovery.Ref.Bip340 as Bip
import JetDiscovery.Types
import JetDiscovery.Run
import JetDiscovery.Tx
import qualified Simplicity.Bitcoin.Jets as Jets
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.Ty.Word
import Simplicity.Digest (hash0)

main :: IO ()
main=do
 let env=maybe (error "env") id (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap hash0)
     input=((toWord128 (Bip.intFromBytes Ref.identifier),toWord32 17),(toWord16 2,(toWord8 5,toWord256 123)))
     expected=Bip.intFromBytes (Ref.chain 17 2 5 1 (Bip.bytesFromInt 123))
     actual=fmap fromWord256 (Jets.fastEval Lms.lmotsHashStep env input)
 print ("single-block chain kernel",actual==Just expected)
 case actual of
  Just x | x==expected -> pure ()
  _ -> error "LMOTS fixed55-byte SHA256 kernel disagrees with reference"
 e<-Lms.upstreamCertificate
 case e of
  Entry _ _ _ _ _ _ program vectors -> do
   putStrLn "computing KAT CMR and running2upstream fixture vectors";hFlush stdout
   let cmr=progCmr (program (vecWitness (head vectors)))
   mapM_ (\v -> do
      let result=runVector program cmr v
      ok<-evaluate (vrOk result)
      print (vrName result,ok,vrNote result);hFlush stdout
      if ok then pure () else error "LMS KAT failed") vectors
