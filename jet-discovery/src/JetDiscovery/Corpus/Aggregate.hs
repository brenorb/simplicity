-- | Cross-input amount semantics.  Script opcodes like BIP 443's default CCV
-- mode and BIP 345's batched triggers keep state across the inputs of a
-- transaction.  A Simplicity program runs per input with no shared state, so
-- each input re-scans all inputs: here, the sum of the values of every input
-- locked by the same script as this one. The sum checks the 16-input limit
-- before scanning.
module JetDiscovery.Corpus.Aggregate
  ( entries
  , sameScriptInputSum
  ) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL
import qualified Data.Word as DW

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes
import Simplicity.Ty.Word

import JetDiscovery.Corpus.CovenantMisc (ccvOutputKey)
import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types
import qualified JetDiscovery.Ref.Bip340 as Ref

maxIns :: Int
maxIns = 16

-- | Sum every input value with the current script hash, rejecting an
-- out-of-range input count or arithmetic overflow.
sameScriptInputSum :: (Assert term, Primitive term) => term () Word64
sameScriptInputSum =
  (Tx.numInputs &&& konst (w32 (toInteger maxIns))) >>> Arith.le word32 >>> verify
  >>> konst (w64 0) >>> foldr (\j k -> step j >>> k) iden [0 .. maxIns - 1]
 where
  step j = (iden &&& (konst (w32 (toInteger j)) >>> primitive Prim.InputScriptHash)) >>> (ih &&& oh) >>> match ih present
   where
    -- input (script hash of input j, acc)
    present = ((oh &&& (unit >>> Tx.currentScriptHash) >>> eq) &&& iden) >>> cond addIt ih
    addIt = (ih &&& (konst (w32 (toInteger j)) >>> primitive Prim.InputValue >>> verify)) >>> Arith.add word64 >>> (oh >>> not iden >>> verify) &&& ih >>> ih

-- | BIP 443 default mode across inputs: every input of this covenant sends to output 0, which must
-- carry the committed contract and at least the sum of their values.
ccvAggregate :: (Assert term, Primitive term, Witness term) => ((Word256, Word256), Word256) -> term () ()
ccvAggregate w = (scriptOk &&& amountOk) >>> unit
 where
  key = witness w >>> ccvOutputKey
  scriptHash = ((unit >>> ctx8Init) &&& konst (w16 0x5120) >>> ctx8Add2) &&& key >>> ctx8Add32 >>> ctx8Finalize
  scriptOk = scriptHash &&& (konst (w32 0) >>> primitive Prim.OutputScriptHash >>> verify) >>> eq >>> verify
  amountOk = sameScriptInputSum &&& (konst (w32 0) >>> primitive Prim.OutputValue >>> verify) >>> Arith.le word64 >>> verify

-- | BIP 345 batched recovery: all vault inputs (same script) recover into output 0, which pays the
-- recovery script and carries at least their total value.
vaultBatchRecover :: (Assert term, Primitive term) => Word256 -> term () ()
vaultBatchRecover recoverHash = (scriptOk &&& amountOk) >>> unit
 where
  scriptOk = (konst (w32 0) >>> primitive Prim.OutputScriptHash >>> verify) &&& konst recoverHash >>> eq >>> verify
  amountOk = sameScriptInputSum &&& (konst (w32 0) >>> primitive Prim.OutputValue >>> verify) >>> Arith.le word64 >>> verify

entries :: [Entry]
entries =
  [ Entry
    { entryId = "bip443-ccv-aggregate"
    , entryTitle = "CCV default mode across inputs: same-covenant inputs aggregate into one output"
    , entrySpec = "BIP 443 CCV_MODE_CHECK_OUTPUT amount semantics (output_min_amount accumulated over inputs)"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "output keys from Ref.embedData / Ref.taprootTweak; values chosen at the boundary"
    , entryAssumptions = [ "inputs of the same covenant are identified by equal script hashes and all target output 0"
                         , "at most 16 inputs (each input re-scans all of them)" ]
    , entryProgram = \(d, r) -> Prog (ccvAggregate ((w256 pk1, w256FromBytes d), w256FromBytes r))
    , entryVectors =
        [ Vector "3 covenant inputs, output carries their sum" (ccvEnv [30000, 20000, 10000] 60000) (dat, root) Accept
        , Vector "output one satoshi short" (ccvEnv [30000, 20000, 10000] 59999) (dat, root) Reject
        , Vector "an unrelated input is not counted" (ccvEnvMixed 50000) (dat, root) Accept ]
    }
  , Entry
    { entryId = "app-vault-batch-recover"
    , entryTitle = "Vault batch recovery: many vault inputs into one recovery output"
    , entrySpec = "BIP 345 batched OP_VAULT_RECOVER semantics"
    , entryCategory = BitcoinApp
    , entryVectorSource = Derived "transactions built for the test"
    , entryAssumptions = ["vault inputs are identified by equal script hashes; at most 16 inputs"]
    , entryProgram = \() -> Prog (vaultBatchRecover (w256FromBytes (hashToBytes (sha256 recScript))))
    , entryVectors =
        [ Vector "4 vault inputs recovered together" (recEnv [1000, 2000, 3000, 4000] 10000 recScript) () Accept
        , Vector "recovery output short" (recEnv [1000, 2000, 3000, 4000] 9999 recScript) () Reject
        , Vector "wrong recovery script" (recEnv [1000, 2000] 3000 (unhex "0014" <> BS.replicate 20 8)) () Reject ]
    }
  ]
 where
  sk = 0xB7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF
  pk1 = Ref.pubkeyOf sk
  dat = BS.replicate 32 0x11
  root = BS.replicate 32 0x22
  covScript = BSL.fromStrict (unhex "5120" <> BS.replicate 32 0x77)
  otherScript = BSL.fromStrict (unhex "0014" <> BS.replicate 20 0x55)
  outScript = unhex "5120" <> Ref.bytesFromInt (Ref.taprootTweak (Ref.embedData pk1 dat) root)
  ccvEnv vals out = mkEnv (mkTx 2 [ mkInput (dummyOutpoint (fromIntegral i)) v covScript 0xffffffff | (i, v) <- zip [0 :: Int ..] vals ] [mkOutput out outScript] 0) 0 defaultTap
  ccvEnvMixed out = mkEnv (mkTx 2 [mkInput (dummyOutpoint 0) 50000 covScript 0xffffffff, mkInput (dummyOutpoint 1) 70000 otherScript 0xffffffff] [mkOutput out outScript] 0) 0 defaultTap
  recScript = unhex "0014" <> BS.replicate 20 9
  recEnv vals out script = mkEnv (mkTx 2 [ mkInput (dummyOutpoint (fromIntegral i)) v covScript 0xffffffff | (i, v) <- zip [0 :: Int ..] vals ] [mkOutput out script] 0) 0 defaultTap
