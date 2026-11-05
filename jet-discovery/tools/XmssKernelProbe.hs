-- Independent fixed-width RFC8391 SHA256 byte-layout regression.
module Main where
import Control.Monad (forM_,unless)
import qualified JetDiscovery.Corpus.Xmss as X
import qualified JetDiscovery.Ref.Xmss as R
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Bitcoin.Jets (unwrap)
import Simplicity.Digest (hash0)
main :: IO ()
main=do
 let env=maybe (error "env") id (mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap hash0)
 forM_ [(0,17,2,5),(1,17,3,6),(2,0,9,0)] $ \(typ,leaf,height,node)->do
  let ad=R.address typ leaf height node 0;a=w256FromBytes ad
      m=w256 123;l=w256 456;r=w256 789
      actualF=J.fastEval (unwrap (J.jetSubst X.fKernelRef)) env (a,m)
      expectedF=w256FromBytes (R.fHash R.publicSeed ad (w256ToBytes m))
      actualH=J.fastEval (unwrap (J.jetSubst X.hKernelRef)) env (a,(l,r))
      expectedH=w256FromBytes (R.randomHash R.publicSeed ad (w256ToBytes l) (w256ToBytes r))
  print (typ,actualF==Just expectedF,actualH==Just expectedH)
  unless (actualF==Just expectedF && actualH==Just expectedH) (error "XMSS fixed-width hash disagrees with independent reference")
