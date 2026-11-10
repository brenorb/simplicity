-- | Memory probe: serialize one component of the pairing program on its own.
--   bn254-pairing-probe (f12mul | powu | finalexp | miller | subgroup) OUT_PREFIX
module Main where
import System.Environment (getArgs)
import Simplicity.Term.Core (witness, unit, (>>>))
import Simplicity.Ty.Word (toWord256)
import JetDiscovery.Types
import JetDiscovery.Followup.Dump (dumpProg)
import qualified JetDiscovery.Followup.Bn254PairingRef as R
import JetDiscovery.Followup.Bn254Pairing

main :: IO ()
main = do
  [which, out] <- getArgs
  let x = montyF12 (((3, 5), (7, 11), (13, 17)), ((19, 23), (29, 31), (37, 41)))
      z = (toWord256 0, toWord256 0)
      g2 = ((toWord256 1, toWord256 2), (toWord256 3, toWord256 4))
      p = case which of
        "f12mul" -> Prog (witness (x, x) >>> f12mulT >>> unit)
        "powu" -> Prog (witness x >>> powUT >>> unit)
        "finalexp" -> Prog (witness x >>> finalExpT x >>> unit)
        "miller" -> Prog (witness ((toWord256 1, toWord256 2), g2) >>> millerT (replicate 102 z) >>> unit)
        "subgroup" -> Prog (witness g2 >>> subgroupT (replicate 380 z) >>> unit)
        _ -> error "component"
  dumpProg out p
  putStrLn ("dumped " ++ which)
