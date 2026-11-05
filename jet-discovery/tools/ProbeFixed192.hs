module Main where
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word
import JetDiscovery.Lib.Bytes
import qualified JetDiscovery.Lib.Fixed192Bounded as F
import JetDiscovery.Tx
import Control.Monad (forM_)
main=do
 let Just env=mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap (hashFromInteger 0)
 forM_ [F.one `div`2,F.one+F.one `div`3,63*F.one+F.one `div`2,192*F.one-1] $ \x->do
  let expected=F.pow2UpperInteger x
      actual=J.fastEval (J.unwrap F.powWrapped) env (toWord128 x)
  print (x,expected,fmap (fromWord word256) actual,fmap (\v->fromWord word256 v-expected) actual)
