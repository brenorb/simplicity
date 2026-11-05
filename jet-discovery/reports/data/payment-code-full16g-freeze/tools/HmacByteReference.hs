module Main where
import Control.Monad(unless)
import qualified Data.ByteString as B
import JetDiscovery.Tx(unhex)
import qualified JetDiscovery.Ref.HmacSha512 as R
import Data.Bits(shiftR)
import System.Exit(exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
assert name ok=do putStrLn(name++"="++show ok);unless ok exitFailure
fixed :: Int -> Integer -> B.ByteString
fixed n value=B.pack[fromInteger(value`shiftR`(8*i))|i<-[n-1,n-2..0]]
inc b=fixed(B.length b)(B.foldl'(\a x->a*256+toInteger x)0 b+1)
main=do
 sha<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth8/sha512-reference-derived.tsv"
 mapM_(\[n,msg,out]->assert("independent sha512 length"++n)(R.sha512(unhex msg)==unhex out))sha
 extra<-map fields.drop 1.lines <$>readFile "vendor-specs/bitcoin-growth8/hmac-reference-derived.tsv"
 mapM_(\[n,key,msg,out]->assert("independent general HMAC keylength"++n)(R.hmacSha512(unhex key)(unhex msg)==unhex out))extra
 rows37<-map fields.drop 1.lines <$>readFile "vendor-specs/transport-crypto/hmac-sha512-37-derived.tsv"
 mapM_(\[name,key,prefix,x,index,out]->assert("native37 equivalent "++name)(R.hmacSha512(unhex key)(B.singleton(read prefix)<>unhex x<>fixed 4(read index))==unhex out))rows37
 rows36<-map fields.drop 1.lines <$>readFile "vendor-specs/transport-crypto/hmac-sha512-36x32-vectors.tsv"
 mapM_(\[name,key,msg,out]->assert("native36 equivalent "++name)(R.hmacSha512(unhex key)(unhex msg)==unhex out))rows36
 let [_,key37,prefix,x,index,out37]=head rows37
     k37=unhex key37;p=read prefix;bx=unhex x;i=read index;expected37=unhex out37
     raw37=B.singleton p<>bx<>fixed 4 i
     [_,key36,msg36,out36]=head rows36;k36=unhex key36;b36=unhex msg36;expected36=unhex out36
 mapM_(\(name,k,msg,expected)->assert("native equivalent corruption "++name)(R.hmacSha512 k msg/=expected))
  [("37key",inc k37,raw37,expected37),("37prefix",k37,B.singleton 4<>bx<>fixed 4 i,expected37),
   ("37x",k37,B.singleton p<>inc bx<>fixed 4 i,expected37),("37index",k37,B.singleton p<>bx<>fixed 4(i+1),expected37),
   ("37digest",k37,raw37,inc expected37),("36hash",inc(B.take 32 k36)<>B.drop 32 k36,b36,expected36),
   ("36tail4",B.take 32 k36<>inc(B.drop 32 k36),b36,expected36),("36x",k36,inc b36,expected36),("36digest",k36,b36,inc expected36)]
 assert "all50native helper cases plus14independent padding/key-boundary cases"(length rows37==20&&length rows36==21&&length sha==8&&length extra==6)
