module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import qualified JetDiscovery.Ref.CompactFilters as F
import JetDiscovery.Tx(unhex)
import System.Exit(exitFailure)
fields delimiter s=case break(==delimiter)s of(a,[])->[a];(a,_:b)->a:fields delimiter b
assert label ok=do putStrLn(label++"="++show ok);unless ok exitFailure
main=do
 rows<-map(fields '\t').drop 1.lines <$>readFile "vendor-specs/bitcoin-growth4/bip158-all-vectors.tsv"
 assert "complete official BIP158 vector inventory10"(length rows==10)
 mapM_(\row->case row of
  [index,_,display,header,previous,filterhex,expected,items,n,_]->do
   let rawHash=F.blockHashRaw(unhex header)
       serialized=unhex filterhex
       scripts=if null items then []else map unhex(fields ',' items)
       canonical=F.constructBasic rawHash scripts
   assert("row"++index++" raw digest versus display blockhash")(F.rawHashToDisplay rawHash==display&&F.displayHashToRaw display==rawHash)
   assert("row"++index++" all official basic filter bytes")(canonical==serialized)
   assert("row"++index++" all official filter header bytes")(F.filterHeaderRaw serialized(F.displayHashToRaw previous)==F.displayHashToRaw expected)
   assert("row"++index++" complete canonical GCS decoding")(case F.decodeBasic serialized of Just values->length values==read n&&F.encodeBasic values==serialized;_->False)
   assert("row"++index++" all real script queries match")(all((==Just True).F.matchBasic rawHash serialized)scripts)
   assert("row"++index++" noncanonical/truncated GCS rejected")(F.decodeBasic(serialized<>B.singleton 0)==Nothing&&F.decodeBasic(B.take(B.length serialized-1)serialized)==Nothing)
  _->fail "ten complete BIP158 inventory columns")rows
