-- An isolated attack control for the exact base guard used by NativeV3Pool.
-- Use genuine V3 state P2TR environments and execute only the common base
-- guard, so the rejection cannot be caused by changed price or fee rounding.
module Main where

import Control.Monad (unless)
import qualified Simplicity.Bitcoin.Jets as J
import qualified JetDiscovery.Corpus.NativeV3Pool as V
import qualified JetDiscovery.Lib.ClaimLedger as C
import JetDiscovery.Run (progCmr)
import JetDiscovery.Types (boundProgram)

main :: IO ()
main = do
  let initial = C.update []
        ([(0,40000000),(1,20000000),(2,20000000),(3,10000000),
          (4,10000000),(5,10000000),(6,10000000),(13,1)] ++
         V.putWide 11 78990846045029531151608375686)
      leftMint = V.lpReference initial 0 True 100000000
      actual = V.lpReference leftMint 1 True 200000000
      alternate = C.update actual [(9,100000001)]
      witness old = C.encode (C.CW 20 old actual 1 1000000 [] [])
      guardProgram = J.unwrap (J.jetSubst C.base)
      actualEnvironment state = C.environment state actual 0 Nothing 0 V.v3FixtureCmr
      test state old = actualEnvironment state >>= \e ->
        J.fastEval guardProgram e (witness old)
      matches = [test actual actual == Just (), test actual alternate == Nothing,
                 test alternate alternate == Just (), test alternate actual == Nothing]
      sameGuardCmr = progCmr (boundProgram C.base (witness actual))
                   == progCmr (boundProgram C.base (witness alternate))
  putStrLn ("Same guard CMR across liquidity witnesses: " ++ show sameGuardCmr)
  putStrLn ("Actual old state, substituted liquidity, alternate matching state, reverse substitution: "
            ++ show matches)
  unless (sameGuardCmr && and matches) (fail "V3 common state binding")
