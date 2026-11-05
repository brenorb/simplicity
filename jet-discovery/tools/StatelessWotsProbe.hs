-- Fixed-block SHRINCS WOTS byte-layout regression against independent bytes.
module Main where
import Control.Monad (forM_,unless)
import System.IO (hSetBuffering,stdout,BufferMode(LineBuffering))
import qualified Data.ByteString as B
import qualified JetDiscovery.Corpus.ShrincsStateless as S
import qualified JetDiscovery.Lib.ShrincsHash as H
import qualified JetDiscovery.Ref.Shrincs as R
import JetDiscovery.Tx
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.Digest (hash0)
import Simplicity.Ty.Word

w128=B.foldl' (\a b->a*256+toInteger b) 0
{-# NOINLINE compiledChain #-}
compiledChain :: J.FastEval J.JetType H.ChainInput Word128
compiledChain=unwrap (J.jetSubst H.chainRef)
{-# NOINLINE compiledSeed #-}
compiledSeed :: J.FastEval J.JetType Word128 Word256
compiledSeed=unwrap (J.jetSubst H.seedState)
{-# NOINLINE compiledWrapper #-}
compiledWrapper :: J.FastEval J.JetType ((Word128,(Word8,Word64)),((Word32,Word32),(Word4,Word128))) Word128
compiledWrapper=unwrap (J.jetSubst S.directWotsChain)
main :: IO ()
main=do
 hSetBuffering stdout LineBuffering
 let env=maybe (error "env") id (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap hash0)
     seed=B.replicate 16 0x5e;node=B.replicate 16 0x37
 forM_ [(l,t,k,c,d,domain)|(l,t,k)<-[(0,2^35+12345,511),(2,2^20+9,17),(4,0,1)],c<-[0,34],d<-[0,7,15],domain<-[0,16]] $ \(l,t,k,c,d,domain)->do
  let input=((toWord128 (w128 seed),(toWord8 l,toWord64 t)),((toWord32 k,toWord32 c),(toWord4 (toInteger d),toWord128(w128 node))))
      expected=foldl (\v j->R.tweak seed (R.adrs (fromInteger l) t domain k c (toInteger j)) v) node [d..14]
      mid=maybe (error "seed compression") id (J.fastEval compiledSeed env (toWord128 (w128 seed)))
      chainInput=(mid,(((toWord8 l,toWord64 t),(toWord8 (toInteger domain),(toWord32 k,toWord32 c))),(toWord4 (toInteger d),toWord128 (w128 node))))
      actual=J.fastEval compiledChain env chainInput
      wrapped=J.fastEval compiledWrapper env input
      ok=actual==Just (toWord128 (w128 expected)) && (domain/=0 || wrapped==actual)
  print ((l,t,k,c,d,domain),ok)
  unless ok (error "fixed-block WOTS disagrees with independent SHA256 byte reference")
