{-# LANGUAGE RankNTypes #-}
-- | Same outer CMR does not identify a disconnected signature hash mode.
module Main where

import Control.Monad (unless)
import qualified Simplicity.Bitcoin.Jets as J
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SH
import Simplicity.Digest (hash0)
import Simplicity.MerkleRoot (IdentityRoot,identityHash)
import Simplicity.Ty.Word (Word256)
import System.Exit (exitFailure)
import qualified JetDiscovery.Corpus.Baseline as Baseline
import qualified JetDiscovery.Corpus.CovenantMisc as Covenant
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

main :: IO ()
main = do
  let allMode=J.jetSubst SH.sigAllHash
      apoMode=J.jetSubst Covenant.apoMode
      allIdentity=identityHash (J.unwrap allMode :: IdentityRoot () Word256)
      apoIdentity=identityHash (J.unwrap apoMode :: IdentityRoot () Word256)
      outer=map firstCmr [head Baseline.entries,head Covenant.entries]
      env n=mkEnv (mkTx 2 [mkInput (dummyOutpoint n) 100000 mempty 0xfffffffd] [mkOutput 99000 mempty] 0) 0 defaultTap hash0
      eval term n=env n >>= \e -> J.fastEval (J.unwrap term) e ()
      allMessages=map (eval allMode) [0,1]
      apoMessages=map (eval apoMode) [0,1]
      ok=case (outer,allMessages,apoMessages) of
        ([a,b],[Just x,Just y],[Just z,Just w]) -> a==b && allIdentity/=apoIdentity && x/=y && z==w
        _ -> False
  putStrLn ("outer_CMR="++show (head outer))
  putStrLn ("sig_all_mode_identity="++show allIdentity)
  putStrLn ("apo_mode_identity="++show apoIdentity)
  putStrLn ("actual_outpoint_mutation_distinguishes_modes="++show ok)
  unless ok exitFailure
 where
  firstCmr (Entry _ _ _ _ _ _ make (v:_))=progCmr (make (vecWitness v))
  firstCmr _=error "empty signature-mode vector set"
