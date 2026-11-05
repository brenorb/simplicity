-- | Inventory only: evaluate no proof, vector, cost or Simplicity expression.
-- Prefer the built executable's identical metadata command, avoiding GHCi's
-- Backpack dep_map panic on GHC9.8.4:
-- cabal run -v0 exe:jet-discovery -- metadata > dist-newstyle/corpus-metadata.tsv
-- Move the temporary file into reports/data only after successful completion.
module Main where
import JetDiscovery.Corpus (corpus)
import JetDiscovery.Types
import Data.List (intercalate)

clean :: String -> String
clean=map (\c -> if c `elem` "\t\r\n" then ' ' else c)

main :: IO ()
main=do
 es<-corpus
 putStrLn "id\ttitle\tcategory\tspec\tvector_source\tvectors\tassumptions"
 mapM_ row es
 where
  row (Entry i title spec category src assumptions _ vs)=putStrLn (intercalate "\t" (map clean [i,title,show category,spec,show src,show (length vs),intercalate "; " assumptions]))
