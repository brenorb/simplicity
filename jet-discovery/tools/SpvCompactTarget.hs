module Main where
import Control.Monad(unless)
import qualified Simplicity.Bitcoin.Jets as J
import qualified JetDiscovery.Lib.SpvReceipt as S
import qualified JetDiscovery.Ref.BitcoinSpv as R
import qualified JetDiscovery.Ref.Bip340 as B
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes
import System.Exit(exitFailure)

main=do
 let cmr=hashFromInteger 0
     env=case mkEnv(mkTx 2[mkInput(dummyOutpoint 0)1000 mempty 0][mkOutput 900 mempty]0)0 defaultTap cmr of Just e->e;_->error "environment"
     kernel=J.unwrap(J.jetSubst S.compactTarget)
     cases=0:[exponent*0x1000000+mantissa|exponent<-[1..35],mantissa<-[0,1,0x7f00,0x8000,0xffff,0x10000,0x7fffff,0x800000,0xffffff]]
       ++[0x01010000,0x017f0000,0x02008000,0x027fff00,0x03008000,0x1d00ffff,0x1d010000,0x1e0000ff,0xffffffff]
 results<-mapM (\bits->do
  let expected=R.compactTarget bits
      actual=fmap(B.intFromBytes.w256ToBytes)(J.fastEval kernel env(w32 bits))
      pass=actual==expected
  putStrLn(show bits++" expected="++show expected++" actual="++show actual++" pass="++show pass)
  return pass)cases
 unless(and results)exitFailure
 putStrLn("all "++show(length cases)++" compact-target boundary cases pass")
