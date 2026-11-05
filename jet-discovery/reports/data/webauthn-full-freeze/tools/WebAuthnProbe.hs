{-# LANGUAGE GADTs #-}
module Main where
import Control.Exception(evaluate)
import Control.Monad(forM_,unless)
import Data.List(isInfixOf)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC
import System.Environment(getArgs)
import System.IO(stdout,hSetBuffering,BufferMode(LineBuffering))
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word hiding(Vector)
import JetDiscovery.Corpus.WebAuthn
import qualified JetDiscovery.Ref.WebAuthn as R
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import JetDiscovery.Run

clientExpr :: J.WrappedSimplicity (Word256,Buffer127 Word8) Word256
clientExpr=J.jetSubst clientHashT
derExpr :: J.WrappedSimplicity (Word256,Word256) Word256
derExpr=J.jetSubst derHashT
authExpr :: J.WrappedSimplicity ((Word256,(Word8,Word32)),Word256) Word256
authExpr=J.jetSubst authDigestT
buf127 bs=fst(bufferFill buffer127(map(toWord8.toInteger)(BS.unpack bs)))
main=do
 hSetBuffering stdout LineBuffering
 args<-getArgs
 case args of
  ["reference"]->do print("referenceAudit",referenceAudit);unless referenceAudit(error "reference failure")
  ["hashes"]->hashes
  ["full"]->forM_ entries $ \(Entry i _ _ _ _ _ program vectors)->do
   putStrLn i
   case vectors of
    []->error "no vectors"
    first:_->do
     let p=program(vecWitness first);cmr=progCmr p
     print("canonical CMR unchanged",cmr==progCmr(Prog(unProg p)))
     unless(cmr==progCmr(Prog(unProg p)))(error "prepared composition CMR changed")
     case boundView p of Just(BoundView k _)->unless(boundEligible k)(error "kernel has internal witness/disconnect");_->error "missing bound kernel"
     forM_ (runVectors program cmr vectors) $ \r->do
      ok<-evaluate(vrOk r);print(vrName r,ok,vrNote r)
      unless("prepared"`isInfixOf`vrNote r)(error "prepared path not observed")
      unless ok(error "WebAuthn vector or CMR failure")
  _->error "usage: WebAuthnProbe reference|hashes|full"
hashes=do
 let Just env=mkEnv(mkTx 2 [mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)
     challenge=BS.pack[0..31]
     check name got expected=do
      let ok=got==Just(w256FromBytes expected)
      print(name,ok);unless ok(error "WebAuthn hash mismatch")
 forM_ [BSC.pack "}",BSC.pack ",\"futureField\":true}",BSC.pack ",\"p\":\""<>BS.replicate 119 97<>BSC.pack "\"}"] $ \tailBytes->
  check("client prefix/base64/full suffix length"++show(BS.length tailBytes))
   (J.fastEval(J.unwrap clientExpr)env(w256FromBytes challenge,buf127 tailBytes))
   (hashToBytes(sha256(R.clientData challenge tailBytes)))
 forM_ ([(0,0),(1,1),(127,128),(255,256),(2^248-1,2^248),(R.n-1,R.n-2)]++[(2^i,2^(255-i))|i<-[0,7,8,63,127,247,254,255]]) $ \rs->
  check("canonical DER"++show rs)(J.fastEval(J.unwrap derExpr)env(w256(fst rs),w256(snd rs)))
   (hashToBytes(sha256(R.encodeDer rs)))
 let json=R.clientData challenge(BSC.pack "}");ch=hashToBytes(sha256 json)
 forM_ [0,1,255,256,2^32-1] $ \c->
  check("authenticator count"++show c)
   (J.fastEval(J.unwrap authExpr)env((w256FromBytes R.rpHash,(w8 5,w32 c)),w256FromBytes ch))
   (R.assertionDigest(R.authData 5 c)json)
