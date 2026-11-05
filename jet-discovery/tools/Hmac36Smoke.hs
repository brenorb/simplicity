{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding(drop,take,and)
import qualified Prelude as P
import Control.Exception(evaluate)
import Control.Monad(forM,unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Lazy as BL
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic(eq)
import Simplicity.Ty.Word
import Simplicity.Bitcoin.Term(Simplicity)
import JetDiscovery.Lib.HmacSha512
import JetDiscovery.Lib.Bytes
import JetDiscovery.Types
import JetDiscovery.Run
import JetDiscovery.Tx
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import System.Exit(exitFailure)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
integer=B.foldl'(\a b->a*256+toInteger b)0 . unhex
kernel :: Simplicity t => t((Key36,Word256),Word512)()
kernel=((take hmac36x32)&&&ih)>>>eq>>>verify
main=do
 hSetBuffering stdout LineBuffering
 rows<-map fields.P.drop 1.lines <$>readFile "vendor-specs/transport-crypto/hmac-sha512-36x32-vectors.tsv"
 let encode[n,key,data32,expected]=(n,(((w256(integer(P.take 64 key)),w32(integer(P.drop 64 key))),w256(integer data32)),toWord word512(integer expected)))
     encode _=error "HMAC36 KAT columns"
     tx=mkTx 2[mkInput(dummyOutpoint 0)1000 BL.empty 0xffffffff][mkOutput 999(unhex "51")]0
     env c=mkEnv tx 0 defaultTap c
     make=boundProgram kernel
     good=[Vector n env w Accept|(n,w)<-map encode rows]
     (((key,index),x),expected)=vecWitness(head good)
     bad=[Vector "changed raw hash bytes"env(((w256(fromWord256 key+1),index),x),expected)Reject,
          Vector "changed raw final4bytes"env(((key,w32(fromWord32 index+1)),x),expected)Reject,
          Vector "changed ECDH x"env(((key,index),w256(fromWord256 x+1)),expected)Reject,
          Vector "changed digest"env(((key,index),x),toWord word512(fromWord word512 expected+1))Reject]
     vectors=good++bad
     cmr=progCmr(make(vecWitness(head vectors)))
 putStrLn("HMAC36x32 positives="++show(length good)++" negatives="++show(length bad)++" canonical CMR="++show cmr)
 outcomes<-forM(runVectors make cmr vectors)$ \r->do
  ok<-evaluate(vrOk r);putStrLn(vrName r++"="++show ok++" "++vrNote r);return ok
 unless(length good==21&&P.and outcomes)exitFailure
