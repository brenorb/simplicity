-- | Serialize a corpus program and its witness for bench/run_program.c.
--
-- The DAG is built exactly as JetDiscovery.Run.measureTerm builds it
-- (jet-substituted, existing Bitcoin jets); bits are packed MSB-first and the
-- final byte is zero-padded, as libsimplicity's bitstream expects.
module JetDiscovery.Followup.Dump (dumpProg) where

import qualified Data.ByteString as BS
import Data.Bits (setBit)
import Data.List (foldl')
import qualified Simplicity.Bitcoin.Dag as Dag
import qualified Simplicity.Bitcoin.Jets as Jets
import qualified Simplicity.Bitcoin.Serialization.BitString as Bits
import JetDiscovery.Types

pack :: [Bool] -> BS.ByteString
pack [] = BS.empty
pack bs = let (h, t) = splitAt 8 bs
              byte = foldl' (\acc (i, b) -> if b then setBit acc (7 - i) else acc) 0 (zip [0 ..] h)
          in BS.cons byte (pack t)

-- | Write PREFIX.program.bin and PREFIX.witness.bin.
dumpProg :: FilePath -> Prog -> IO ()
dumpProg prefix p = do
  let dag = Dag.jetDag (unProg p :: Dag.JetDag Jets.JetType () ())
  BS.writeFile (prefix ++ ".program.bin") (pack (Bits.putDagNoWitnessLengthCode dag))
  BS.writeFile (prefix ++ ".witness.bin") (pack (maybe (error "witness encoding") id (Bits.putWitnessData dag)))
