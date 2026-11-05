module Main where
import qualified Data.ByteString as B
import qualified Simplicity.Bitcoin.Jets as J
import qualified JetDiscovery.Lib.SilentPayment as S
import qualified JetDiscovery.Ref.SilentPayment as R
import qualified JetDiscovery.Ref.Bip340 as EC
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes
import Control.Monad(unless)
import System.Exit(exitFailure)
import System.IO(hFlush,stdout)
fields s=case break(=='\t')s of(a,[])->[a];(a,_:b)->a:fields b
point(Just(x,y))=(w256 x,w256 y)
point Nothing=error "infinite test point"
main=do
 raw<-readFile "vendor-specs/bitcoin-growth/bip352-mixed-core-vectors.tsv"
 let rows=map(fields.filter(/='\r'))(drop 1(lines raw))
     env=case mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap(hashFromInteger 0)of Just e->e;_->error "pure kernel environment"
     proofKernel=J.unwrap(J.jetSubst S.dleq374)
 results<-mapM(\[name,a,b,o0,o1,scan,spend,_,out]->do
  putStrLn(name++" starting");hFlush stdout
  let secret=(R.evenSecret(EC.intFromBytes(unhex a))+EC.intFromBytes(unhex b))`mod`EC.n
      aggregate=EC.pointMul EC.gPt secret
      scanPoint=R.decodeCompressed(unhex scan);spendPoint=R.decodeCompressed(unhex spend)
      first=minimum[unhex o0,unhex o1]
      op=(w256FromBytes(B.take 32 first),w32(EC.intFromBytes(B.reverse(B.drop 32 first))))
      shared=EC.pointMul scanPoint secret
      argument=(point aggregate,(op,point shared))
      actual=J.fastEval(J.unwrap(J.jetSubst(S.deriveOutput(point spendPoint))))env argument
      corePass=actual==Just(w256FromBytes(unhex out))
      message=B.replicate 32 0
      (c,(e,s))=R.prove374 secret scanPoint message
      input=((point aggregate,(point scanPoint,point c)),((w256 e,w256 s),w256FromBytes message))
      wrongMessage=((point aggregate,(point scanPoint,point c)),((w256 e,w256 s),w256FromBytes(B.replicate 32 1)))
      badScalar=((point aggregate,(point scanPoint,point c)),((w256 EC.n,w256 s),w256FromBytes message))
      proofPass=J.fastEval proofKernel env input==Just()
       &&J.fastEval proofKernel env wrongMessage==Nothing&&J.fastEval proofKernel env badScalar==Nothing
  putStrLn(name++" exact_output="++show corePass++" bip374_honest_and_malicious="++show proofPass);hFlush stdout
  return(corePass&&proofPass))rows
 unless(length rows==3&&and results)exitFailure
 putStrLn "all 3 compatible upstream BIP352 cores and BIP374 transcript/scalar checks pass actual Simplicity evaluation"
