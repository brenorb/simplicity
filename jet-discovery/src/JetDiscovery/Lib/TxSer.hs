-- | Re-serializing transaction data in Simplicity, for proposals (BIP 119,
-- BIP 446, BIP 346) that hash Bitcoin's own serializations rather than
-- Simplicity's per-field hashes.
--
-- Bitcoin Simplicity exposes output scripts, scriptSigs and annexes only as
-- SHA-256 hashes.  These helpers take the raw bytes as witness data, check them
-- against the hash primitives, and append the Bitcoin serialization to a
-- SHA-256 context.
module JetDiscovery.Lib.TxSer
  ( ctxWith
  , outStep, seqStep, ssStep
  , shaOutputs, shaSequences
  , maxIns, maxOuts
  ) where

import Prelude hiding (drop, take, not, and, or)

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (scribe, eq)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes

-- | Loop bounds: transactions with at most this many inputs and outputs.
maxIns, maxOuts :: Int
maxIns = 16
maxOuts = 16

-- | Thread a SHA-256 context through @t@: @ctxWith t step@ appends @t@'s output with @step@.
ctxWith :: (Core term, TyC x) => term () x -> term (Ctx8, x) Ctx8 -> term Ctx8 Ctx8
ctxWith t step = iden &&& (unit >>> t) >>> step

-- | Process output @i@ given its script bytes as witness: check the script
-- hash and append @value_le64 || ser_string(script)@.
outStep :: (Assert term, Primitive term, Witness term) => Int -> Buffer511 Word8 -> term Ctx8 Ctx8
outStep i script = (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.OutputValue) &&& iden >>> match ih present
 where
  -- input (Word64 value, Ctx8)
  present = (unit >>> witness script) &&& iden >>> checked
  -- input (Buffer511, (Word64, Ctx8))
  checked = (take sha256Buffer511 &&& (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.OutputScriptHash >>> verify) >>> eq >>> verify)
        &&& ((drop (ih &&& oh >>> ctxAddLE64)) &&& oh >>> ctxAddVarString511)
        >>> ih

-- | Process input @i@: append its LE sequence number to the sequences context.
seqStep :: (Assert term, Primitive term) => Int -> term Ctx8 Ctx8
seqStep i = (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.InputSequence) &&& iden >>> match ih (ih &&& oh >>> ctxAddLE32)

-- | Process input @i@'s scriptSig (witness bytes): check its hash, append
-- @ser_string(scriptSig)@, and record whether it is non-empty.
-- State: (any non-empty so far, context).
ssStep :: (Assert term, Primitive term, Witness term) => Int -> Buffer511 Word8 -> term (Bit, Ctx8) (Bit, Ctx8)
ssStep i ss = (unit >>> scribe (w32 (toInteger i)) >>> primitive Prim.InputScriptSigHash) &&& iden >>> match ih present
 where
  -- input (Word256 expected hash, (Bit, Ctx8))
  present = (unit >>> witness ss) &&& iden >>> checked
  -- input (Buffer511, (Word256, (Bit, Ctx8)))
  checked = (take sha256Buffer511 &&& ioh >>> eq >>> verify)
        &&& ((take nonEmpty &&& iioh >>> or oh ih) &&& (iiih &&& oh >>> ctxAddVarString511))
        >>> ih
  nonEmpty = buf511Len >>> some16
  some16 = iden &&& scribe (w16 0) >>> eq >>> not iden

-- | BIP 341 @sha_outputs@ (= BIP 119's outputs hash) from witness-supplied output scripts.
shaOutputs :: (Assert term, Primitive term, Witness term) => [Buffer511 Word8] -> term () Word256
shaOutputs scripts = ctx8Init >>> foldr (\(i, s) k -> outStep i s >>> k) iden (zip [0 ..] scripts) >>> ctx8Finalize

-- | BIP 341 @sha_sequences@ (= BIP 119's sequences hash).
shaSequences :: (Assert term, Primitive term) => term () Word256
shaSequences = ctx8Init >>> foldr (\i k -> seqStep i >>> k) iden [0 .. maxIns - 1] >>> ctx8Finalize
