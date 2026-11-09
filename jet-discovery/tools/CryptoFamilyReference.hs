module Main where
import Control.Monad(forM_,unless)
import qualified Data.ByteString as BS
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import qualified JetDiscovery.Ref.Blake3 as B3
import qualified JetDiscovery.Ref.Shake256 as Xof
import qualified JetDiscovery.Ref.MlDsaNtt as Ntt
import qualified JetDiscovery.Ref.Poseidon2 as P2
import JetDiscovery.Tx(unhex)
splitTabs []=[[]]
splitTabs('\t':xs)=[]:splitTabs xs
splitTabs(x:xs)=case splitTabs xs of a:as->(x:a):as;_->error "split"
load path=map(map(init.tail).splitTabs).tail.lines <$> readFile path
check name ok=do print(name,ok);unless ok(error "crypto reference failure")
main=do
 hSetBuffering stdout LineBuffering
 b<-load "vendor-specs/crypto-families/blake3-unkeyed-bounded.tsv"
 forM_ b $ \[i,len,expected]->check("BLAKE3 official case"++i)(B3.hash256(B3.patternInput(read len))==Just(unhex expected))
 x<-load "vendor-specs/crypto-families/shake256-kat250.tsv"
 forM_ x $ \[source,i,msg,expected]->check("SHAKE256 complete2000bit official"++source++":"++i)(Xof.shake250(unhex msg)==Just(unhex expected))
 check "MLDSA six full polynomial directDFT/inverse versus FIPS butterflies" Ntt.selfCheck
 check "Poseidon2 complete published16field default KAT" P2.selfCheck
 check "BLAKE3 input-bound rejection"(B3.hash256(BS.replicate 2049 0)==Nothing)
 check "SHAKE input-bound rejection"(Xof.shake250(BS.replicate 512 0)==Nothing)
