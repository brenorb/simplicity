{-# OPTIONS_GHC -fsimpl-tick-factor=300 -funfolding-case-threshold=1 -funfolding-case-scaling=5 #-}
module Main where

import Control.Monad (forM_,unless)
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Programs.Bit (Bit,toBit)
import Simplicity.Ty.Word (Word64)
import System.Environment (getArgs)
import System.IO (BufferMode(LineBuffering),hSetBuffering,stdout)
import JetDiscovery.Lib.Bytes (w64)
import qualified JetDiscovery.Lib.TwoCryptoMath as M
import qualified JetDiscovery.Lib.TwoCryptoPool as P
import qualified JetDiscovery.Ref.TwoCrypto as R
import JetDiscovery.Tx

env = case mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 999 mempty] 0)
                 0 defaultTap (hashFromInteger 0) of
  Just v -> v
  Nothing -> error "TwoCrypto pool fixture environment"

eval term = J.fastEval (J.unwrap term) env

check :: Show a => a -> Bool -> IO ()
check label ok = print (label,ok) >> unless ok (error "TwoCrypto source accounting mismatch")

initial = case R.join R.empty (1000000,1000000) of
  Just (p,_,_) -> p
  Nothing -> error "TwoCrypto reference initial join"

traded = case R.swap initial 0 10000 of
  Just (p,_,_) -> p
  Nothing -> error "TwoCrypto reference trade"

coins (a,b) = (w64 a,w64 b)

joins = do
  let expr = J.jetSubst P.joinPool :: J.WrappedSimplicity (P.Pool,M.Balances) (P.Pool,Word64)
      cases = [(R.empty,(1000000,1000000)),(initial,(10000,0)),(initial,(0,10000)),
               (initial,(10000,10000)),(R.empty,(1000000,0)),(initial,(0,0))]
  forM_ cases $ \(old,amounts) ->
    check ("join",R.supply old,amounts)
      (eval expr (P.encodePool old,coins amounts)==
       fmap (\(p,m,_) -> (P.encodePool p,w64 m)) (R.join old amounts))

swaps = do
  let expr = J.jetSubst P.swapPool :: J.WrappedSimplicity (P.Pool,(Bit,Word64)) (P.Pool,Word64)
  forM_ [(0,10000),(1,10000),(0,100000),(1,100001),(0,0),(1,5000)] $ \(side,amount) ->
    check ("swap",side,amount)
      (eval expr (P.encodePool initial,(toBit (side==1),w64 amount))==
       fmap (\(p,m,_) -> (P.encodePool p,w64 m)) (R.swap initial side amount))

exits = do
  let expr = J.jetSubst P.exitPool :: J.WrappedSimplicity (P.Pool,Word64) (P.Pool,M.Balances)
  forM_ [1,R.wad `div` 10,R.supply traded,0,R.supply traded+1] $ \burned ->
    check ("exit",burned)
      (eval expr (P.encodePool traded,w64 burned)==fmap (\(p,a) -> (P.encodePool p,coins a)) (R.exit traded burned))

sweeps = do
  let expr = J.jetSubst P.sweepPool :: J.WrappedSimplicity P.Pool (P.Pool,M.Balances)
  forM_ [initial,traded] $ \old ->
    check ("admin settlement",R.profit old)
      (eval expr (P.encodePool old)==fmap (\(p,a) -> (P.encodePool p,coins a)) (R.sweep old))

main = do
  hSetBuffering stdout LineBuffering
  args <- getArgs
  case args of
    ["joins"] -> joins
    ["swaps"] -> swaps
    ["exits"] -> exits
    ["sweeps"] -> sweeps
    _ -> error "usage: TwoCryptoPoolProbe joins|swaps|exits|sweeps"
