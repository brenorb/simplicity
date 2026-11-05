{-# LANGUAGE RankNTypes #-}
module Main where
import Prelude hiding (drop,take,not,and,or)
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import Simplicity.Ty.Word
import qualified Simplicity.Bitcoin.Jets as J
import JetDiscovery.Types
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Lib.Bytes
prog :: (Assert t,Witness t) => Integer -> Integer -> t () ()
prog x y=(((witness (w8 x) &&& konst (w8 0)) >>> eq >>> verify) &&& ((witness (w8 y) &&& konst (w8 1)) >>> eq >>> verify)) >>> unit
main=do
 let consistent=Prog(prog 0 0); split=Prog(prog 0 1)
     env=mkEnv(mkTx 2 [mkInput(dummyOutpoint 0) 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap (progCmr consistent)
 print ("same jetted CMR",progCmr consistent==progCmr split)
 case env of
  Nothing->error "env"
  Just e->do
   print ("consistent witness outcome",J.fastEval(J.unwrap(J.jetSubst(prog 0 0))) e ())
   print ("split witness outcome",J.fastEval(J.unwrap(J.jetSubst(prog 0 1))) e ())
