module Main where
import qualified Data.ByteString as B
import qualified JetDiscovery.Ref.SilentPayment as S
import qualified JetDiscovery.Ref.Bip340 as R
import JetDiscovery.Tx
import Control.Monad(unless)
import System.Exit(exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
main=do
 raw<-readFile "vendor-specs/bitcoin-growth/bip352-mixed-core-vectors.tsv"
 let rows=map(fields.filter(/='\r'))(drop 1(lines raw))
 results<-mapM(\[name,a,b,o0,o1,scan,spend,shared,out]->do
  let x=R.intFromBytes(unhex a);y=R.intFromBytes(unhex b)
      scanPt=S.decodeCompressed(unhex scan);spendPt=S.decodeCompressed(unhex spend)
      (output,actualShared,inputHash)=S.derive x y[unhex o0,unhex o1]scanPt spendPt
      pass=R.bytesFromInt output==unhex out&&actualShared==unhex shared
      sumSecret=(S.evenSecret x+y)`mod`R.n
      (c,(e,s))=S.prove374 sumSecret scanPt(B.replicate 32 0)
      aPoint=R.pointMul R.gPt sumSecret
      proofPass=S.verify374 aPoint scanPt c(e,s)(B.replicate 32 0)
       &&not(S.verify374 aPoint scanPt c(e+R.n,s)(B.replicate 32 0))
       &&not(S.verify374 aPoint scanPt c(e,s)(B.replicate 32 1))
  putStrLn(name++" core_pass="++show pass++" bip374_transcript_and_boundaries="++show proofPass
    ++" input_hash="++hex(R.bytesFromInt inputHash)++" output="++hex(R.bytesFromInt output))
  return(pass&&proofPass))rows
 unless(length rows==3&&and results)exitFailure
