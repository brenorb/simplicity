{-# LANGUAGE GADTs #-}
-- | Vector-only, sequential verification diagnostics; no full cost analysis.
module Main where
import Control.Exception (evaluate)
import Control.Monad (forM_)
import System.Environment (getArgs)
import System.IO (hFlush,stdout)
import qualified JetDiscovery.Corpus.EprintExpansion as E
import qualified JetDiscovery.Corpus.Eprint as OldE
import qualified JetDiscovery.Corpus.BN254 as BN
import qualified JetDiscovery.Corpus.Lms as Lms
import qualified JetDiscovery.Corpus.SlhDsaStandard as SlhStandard
import qualified JetDiscovery.Corpus.Xmss as Xmss
import qualified JetDiscovery.Corpus.Shrincs as Shrincs
import qualified JetDiscovery.Corpus.ShrincsStateless as Slh
import JetDiscovery.Types
import JetDiscovery.Run

main :: IO ()
main=do
 args<-getArgs
 es<-case args of
  ["eprint"] -> pure E.entries
  ["frost"] -> pure (filter ((=="eprint-frost-signature-share").entryId) E.entries)
  ["eprint-original"] -> OldE.entries
  ["bn254"] -> pure BN.entries
  ["lms-kat"] -> (:[]) <$> Lms.upstreamCertificate
  ["lms"] -> pure Lms.entries
  ["slh-standard"] -> pure SlhStandard.entries
  ["slh-standard-kat"] -> (:[]) <$> SlhStandard.upstreamCertificate
  ["xmss"] -> pure Xmss.entries
  ["shrincs-stateful"] -> pure Shrincs.entries
  ["shrincs-stateless"] -> pure Slh.entries
  _ -> error "usage: WitnessBoundVerification eprint|frost|eprint-original|bn254|lms-kat|lms|slh-standard|slh-standard-kat|xmss|shrincs-stateful|shrincs-stateless"
 forM_ es $ \(Entry i _ _ _ _ _ program vectors) -> do
  putStrLn i;hFlush stdout
  case vectors of
   [] -> error "no vectors"
   first:_ -> do
    let cmr=progCmr (program (vecWitness first))
    forM_ vectors $ \v -> do
     let r=runVector program cmr v
     ok<-evaluate (vrOk r)
     print (vrName r,ok,vrNote r);hFlush stdout
     if ok then pure () else error "vector failure or CMR changed"
