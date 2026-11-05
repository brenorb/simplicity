-- Complete pinned ACVP SHA2-128s pure/internal reference check, no external code.
module Main where
import Control.Monad (forM_,unless)
import System.IO (hSetBuffering,stdout,BufferMode(LineBuffering))
import qualified Data.ByteString as B
import qualified JetDiscovery.Ref.SlhDsaStandard as R
import JetDiscovery.Tx (unhex)
fields s=case break(=='\t')s of (a,[])->[a];(a,_:b)->a:fields b
main=do
 hSetBuffering stdout LineBuffering
 input<-readFile "vendor-specs/slhdsa/acvp-supported.tsv"
 let rows=tail(lines input)
 unless(length rows==28)(error "expected complete28case pure/internal subset")
 forM_ rows $ \row->case fields row of
  [group,tc,pkHex,msgHex,sigHex,expected]->do
   let pk=unhex pkHex;message=unhex msgHex;raw=unhex sigHex
       actual=case R.parseSignature raw of Nothing->False;Just signature->R.verifyInternal(B.take 16 pk)(B.drop 16 pk)message signature
       ok=actual==(expected=="true")
   print (group,tc,actual,ok)
   unless ok(error "standard reference disagrees with official NIST ACVP")
  _->error "ACVP supported TSV fields"
