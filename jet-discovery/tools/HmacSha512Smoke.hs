{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding(drop,take)
import qualified Prelude as P
import Control.Exception(evaluate)
import Control.Monad(forM,unless)
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
kernel :: Simplicity t => t(HmacInput,Word512)()
kernel=((take hmac37)&&&ih)>>>eq>>>verify
main=do
 hSetBuffering stdout LineBuffering
 rows<-map fields.P.drop 1.lines <$>readFile "vendor-specs/transport-crypto/hmac-sha512-37-derived.tsv"
 let encode[n,key,prefix,x,index,expected]=(n,((w256FromBytes(unhex key),(w8(read prefix),(w256FromBytes(unhex x),w32(read index)))),toWord word512(integer expected)))
     encode _=error "HMAC KAT columns"
     integer=foldl(\a b->a*256+toInteger b)0 . BL.unpack . BL.fromStrict . unhex
     tx=mkTx 2[mkInput(dummyOutpoint 0)1000 BL.empty 0xffffffff][mkOutput 999(unhex "51")]0
     make=boundProgram kernel
     good=[Vector n(\c->mkEnv tx 0 defaultTap c)w Accept|(n,w)<-map encode rows]
     (key,(prefix,(x,index)),expected)=case vecWitness(head good)of((k,(p,(x,i))),e)->(k,(p,(x,i)),e)
     env c=mkEnv tx 0 defaultTap c
     bad=[Vector "changed key"env((w256(fromWord256 key+1),(prefix,(x,index))),expected)Reject,
          Vector "changed prefix"env((key,(w8 4,(x,index))),expected)Reject,
          Vector "changed x"env((key,(prefix,(w256(fromWord256 x+1),index))),expected)Reject,
          Vector "changed index"env((key,(prefix,(x,w32(fromWord32 index+1)))),expected)Reject,
          Vector "changed digest"env((key,(prefix,(x,index))),toWord word512(fromWord word512 expected+1))Reject]
     vectors=good++bad
     cmr=progCmr(make(vecWitness(head vectors)))
 putStrLn("HMAC derived KATs="++show(length good)++" negatives="++show(length bad)++" canonical CMR="++show cmr)
 outcomes<-forM(runVectors make cmr vectors)$ \r->do
  ok<-evaluate(vrOk r);putStrLn(vrName r++"="++show ok++" "++vrNote r);return ok
 unless(length good==20&&P.and outcomes)exitFailure
