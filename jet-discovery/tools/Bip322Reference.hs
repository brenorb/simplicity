module Main where
import qualified Data.ByteString as B
import JetDiscovery.Tx
import qualified JetDiscovery.Ref.BitcoinGrowth as G
import qualified JetDiscovery.Ref.Bip340 as R
import Control.Monad (unless)
import System.Exit (exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
main=do
 raw<-readFile "vendor-specs/bitcoin-growth/bip322-keypath-vectors.tsv"
 let rows=map (fields.filter(/='\r'))(drop 1(lines raw))
 results<-mapM (\[name,m,k,s,want]->do
  let message=unhex m;key=unhex k;digest=G.bip322Digest message key
      accepted=R.verify key digest(unhex s)
      ok=accepted==(want=="Accept")
  putStrLn(name++" accepted="++show accepted++" expected="++want++" pass="++show ok
    ++" to_spend_txid="++hex(B.reverse(G.sha256d(G.bip322ToSpend(G.bip322MessageHash message)key)))
    ++" to_sign_txid="++hex(B.reverse(G.sha256d(G.bip322ToSign(G.bip322MessageHash message)key)))
    ++" digest="++hex digest)
  return ok)rows
 unless(length rows==4&&and results)exitFailure
