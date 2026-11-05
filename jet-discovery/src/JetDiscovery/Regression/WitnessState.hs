-- | Actual same-CMR split-witness regression for the state-counter bug.
-- The intentionally unsafe expression is diagnostic only, never corpus code.
module JetDiscovery.Regression.WitnessState (stateAliasChecks) where
import Prelude hiding (drop,take,not,and,or)
import qualified Data.ByteString.Lazy as BL
import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as A
import Simplicity.Bitcoin.Term (Simplicity,Primitive,primitive)
import qualified Simplicity.Bitcoin.Primitive as P
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Jets as J
import Simplicity.Ty.Word
import JetDiscovery.Corpus.StatefulApps (counter)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.State
import JetDiscovery.Run (progCmr)
import JetDiscovery.Tx
import JetDiscovery.Types

next :: Assert t => t Word256 Word256
next=oh&&&(ioh&&&updated)
 where updated=(iih&&&konst (w64 1))>>>A.add word64>>>((oh>>>not iden>>>verify)&&&ih)>>>ih

-- The same logical old state was emitted as two independent witness nodes.
-- CMR commits neither value, so an attacker can keep loaded=41 and use40 for
-- the state transition. A continuation containing41 then freezes the counter.
legacySplit :: (Simplicity t,Primitive t) => Integer -> Integer -> t () ()
legacySplit loaded computed=loadState (witness (w256 loaded))&&&store>>>unit
 where
  expected=stateScriptHash (witness (w256 computed)>>>next)
  actual=konst (w32 0)>>>primitive P.OutputScriptHash>>>verify
  store=((expected&&&actual)>>>eq>>>verify)&&&((Tx.currentValue&&&(konst (w32 0)>>>primitive P.OutputValue>>>verify))>>>eq>>>verify)>>>unit

stateAliasChecks :: [(String,Bool)]
stateAliasChecks=
 [ ("legacy split witness keeps the exact CMR",progCmr honest==progCmr attacked)
 , ("legacy consistent witness rejects frozen state",evaluate honest==Nothing)
 , ("legacy split witness accepts frozen state",evaluate attacked==Just ())
 , ("repaired counter rejects frozen state for actual old value",evaluate (Prog (counter (w256 41)))==Nothing)
 , ("repaired counter rejects forged transition old value",evaluate (Prog (counter (w256 40)))==Nothing)
 ]
 where
  honest=Prog (legacySplit 41 41)
  attacked=Prog (legacySplit 41 40)
  evaluate p=do
   let cmr=progCmr p
       old=w256ToBytes (w256 41)
       script=stateScript cmr old
       tx=mkTx 2 [mkInput (dummyOutpoint 0) 100000 (BL.fromStrict script) 0xfffffffe] [mkOutput 100000 script] 0
   e<-mkEnv tx 0 (\_->stateTap cmr old) cmr
   J.fastEval (J.unwrap (J.jetSubst (unProg p))) e ()
