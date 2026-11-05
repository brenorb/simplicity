{-# LANGUAGE GADTs #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad (forM_,unless)
import Data.List (isInfixOf)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding (Vector)
import System.Environment (getArgs)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import qualified JetDiscovery.Corpus.QuadraticFunding as Q
import JetDiscovery.Lib.Bytes (w8,w16)
import qualified JetDiscovery.Ref.QuadraticFunding as R
import JetDiscovery.Run (VectorResult(..),progCmr,runVectors)
import JetDiscovery.Tx
import JetDiscovery.Types

type V = (Word8,(Word8,Word8))
type Open = (Word16,(V,V))
type Claims = (Word16,(Word16,Word16))
allocationExpr :: J.WrappedSimplicity Open Claims
allocationExpr = J.jetSubst Q.allocationT

allocation :: IO ()
allocation = do
  let Just env = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 999 mempty] 0)
                       0 defaultTap (hashFromInteger 0)
      pack (x,y,z) = (w8 x,(w8 y,w8 z))
      expected (x,y,z) = (w16 x,(w16 y,w16 z))
      cases = [(b,x,y) | b<-[1,1001,2000,65535],
                         (x,y)<-[((0,0,0),(0,0,0)),((20,20,0),(20,10,0)),
                                 ((20,0,0),(0,0,10)),((63,63,63),(63,63,63)),
                                 ((0,1,1),(63,0,0)),((63,63,63),(0,1,1))]]
  forM_ cases $ \(b,x,y) -> do
    let got = J.fastEval (J.unwrap allocationExpr) env (w16 b,(pack x,pack y))
        ok = got == Just (expected (R.allocation b x y))
    print (b,x,y,ok)
    unless ok (error "allocation reference mismatch")

native :: IO ()
native = forM_ Q.entries $ \(Entry name _ _ _ _ _ program vectors) -> do
  putStrLn name
  cmr <- evaluate (hashToInteger Q.roundCmr)
  print ("canonical round CMR",cmr)
  case vectors of
    [] -> error "no native vectors"
    first:_ -> do
      let p=program (vecWitness first); h=progCmr p
          equal = hashToInteger h==cmr && progCmr (Prog (unProg p))==h
      print ("prepared and canonical CMR match",equal)
      unless equal (error "canonical round CMR changed")
      case boundView p of
        Just (BoundView k _) -> do
          let eligible=boundEligible k
          print ("pure bound kernel eligible",eligible)
          unless eligible (error "bound kernel ineligible")
        Nothing -> error "expected one bound witness"
      forM_ (runVectors program h vectors) $ \r -> do
        ok <- evaluate (vrOk r)
        print (vrName r,ok,vrNote r)
        unless (ok && "prepared"`isInfixOf`vrNote r) (error "native result or execution path mismatch")

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  case args of
    ["reference"] -> print ("Integer CQF controls and all claim permutations",Q.referenceAudit) >>
                     unless Q.referenceAudit (error "reference controls failed")
    ["allocation"] -> allocation
    ["native"] -> native
    _ -> error "usage: QuadraticFundingProbe reference|allocation|native"
