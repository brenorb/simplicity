module Main where

import Control.Monad (forM_,unless)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Term.Core (iden,ih,oh,(>>>))
import Simplicity.Ty.Word
import System.Environment (getArgs)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import JetDiscovery.Lib.Bytes (w64)
import qualified JetDiscovery.Lib.TwoCryptoArithmetic as A
import qualified JetDiscovery.Lib.TwoCryptoMath as M
import qualified JetDiscovery.Ref.TwoCrypto as R
import JetDiscovery.Tx

env = case mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 999 mempty] 0)
                 0 defaultTap (hashFromInteger 0) of
  Just v -> v
  Nothing -> error "TwoCrypto helper fixture environment"

evaluateTerm term = J.fastEval (J.unwrap term) env

check :: Show a => a -> Bool -> IO ()
check label ok = print (label,ok) >> unless ok (error "TwoCrypto math comparison failed")

division = do
  let expr = J.jetSubst (A.divideWide oh ih) :: J.WrappedSimplicity (Word128,Word64) Word128
      cases = [(0,1),(2^128-1,1),(2^128-1,2^64-1),(2^127+73,2^63),(2^127,400),
               (1234567,123),(2^125+9,R.gamma),(2^64+1,2),(2^126+1,2^55)]
  forM_ cases $ \(n,d) -> check ("wide quotient",n,d)
    (evaluateTerm expr (toWord128 n,w64 d) == Just (toWord128 (n `div` d)))
  check ("zero divisor",0::Int) (evaluateTerm expr (toWord128 1,w64 0)==Nothing)

invariant = do
  let expr = J.jetSubst M.invariant :: J.WrappedSimplicity M.Balances Word64
      cases = [(1000000,1000000),(1010000,990000),(960000,1005000),(250000,253000),
               (3999000,4000000),(100000,100000),(4000001,4000000),(0,1000000)]
  forM_ cases $ \(a,b) -> do
    let (x,y)=(a*R.precision,b*R.precision)
    check ("newton_D",a,b) (evaluateTerm expr (w64 x,w64 y)==fmap w64 (R.invariant (x,y)))

fallback = do
  let gate = J.jetSubst M.fallbackRatio :: J.WrappedSimplicity (Word64,Word64) ()
      expr = J.jetSubst M.getY :: J.WrappedSimplicity (Word64,Word64) Word64
      d = 2*R.wad
      low = 45*d `div` 100
      high = 55*d `div` 100
  forM_ [(low-1,False),(low,True),(R.wad,True),(high,True),(high+1,False)] $ \(x,ok) ->
    check ("fallback ratio boundary",x) ((evaluateTerm gate (w64 d,w64 x)==Just ())==ok)
  forM_ [low-1,low,low+1,R.wad,high-1,high,high+1,1010000*R.precision] $ \x ->
    check ("source Newton fallback",d,x) (evaluateTerm expr (w64 d,w64 x)==fmap w64 (R.fallbackY d x))

fee = do
  let expr = J.jetSubst M.dynamicFee :: J.WrappedSimplicity M.Balances Word64
  forM_ [(R.wad,R.wad),(R.wad,95*R.wad`div`100),(95*R.wad`div`100,R.wad),
         (2*R.wad,R.wad),(R.wad,2*R.wad)] $ \(a,b) ->
    check ("ordered dynamic fee",a,b) (evaluateTerm expr (w64 a,w64 b)==Just (w64 (R.dynamicFee (a,b))))

main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  case args of
    ["reference"] -> check "Integer TwoCrypto profile" R.referenceAudit
    ["division"] -> division
    ["invariant"] -> invariant
    ["fallback"] -> fallback
    ["fee"] -> fee
    _ -> error "usage: TwoCryptoMathProbe reference|division|invariant|fallback|fee"
