-- | Cost-only what-if variants for candidates whose specification needs data
-- that Bitcoin Simplicity cannot express today.
--
-- The "bip341_hashes" candidate family would expose BIP 341's precomputed
-- transaction hashes (sha_outputs, sha_sequences, sha_annex, and a
-- scriptSig-serialization hash for BIP 119) as jets, as Bitcoin Core already
-- computes them.  Their specifications need raw output scripts, which no
-- primitive provides, so the overlay cannot match them.  Instead these
-- variants rewrite the exact BIP 119 and BIP 446 programs with *stand-in*
-- jets of the same type and an analogous precomputed-hash cost
-- (outputs_hash, input_sequences_hash, input_script_sigs_hash,
-- current_annex_hash).  The stand-ins compute different hashes, so these
-- programs are measured but never executed: their costs are ESTIMATEs of the
-- exact programs with the candidate jets.
module JetDiscovery.Candidates.Variants
  ( variants
  ) where

import Prelude hiding (drop, take, not, and, or)

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import Simplicity.Programs.Sha256.Lib
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import qualified Simplicity.Bitcoin.Programs.SigHash.Lib as SigHash
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Lib.TxSer (ctxWith)
import JetDiscovery.Types

-- | (candidate family, program it rewrites, variant program)
variants :: [(String, String, Prog)]
variants =
  [ ("bip341_hashes", "bip119-ctv-exact", Prog ctvWithBip341Jets)
  , ("bip341_hashes", "bip446-templatehash-exact", Prog templateWithBip341Jets)
  ]

hW :: (Witness term, TyC a) => term a Word256
hW = witness (toWord256 0)

ctvWithBip341Jets :: (Assert term, Primitive term, Witness term) => term () ()
ctvWithBip341Jets = template &&& hW >>> eq >>> verify
   where
    template = ctx8Init
           >>> ctxWith (primitive Prim.Version) ctxAddLE32
           >>> ctxWith (primitive Prim.LockTime) ctxAddLE32
           >>> ctxWith SigHash.inputScriptSigsHash ctx8Add32      -- stand-in for sha(scriptSigs) (always included here)
           >>> ctxWith Tx.numInputs ctxAddLE32
           >>> ctxWith SigHash.inputSequencesHash ctx8Add32       -- stand-in for bip341 sha_sequences
           >>> ctxWith Tx.numOutputs ctxAddLE32
           >>> ctxWith SigHash.outputsHash ctx8Add32              -- stand-in for bip341 sha_outputs
           >>> ctxWith (primitive Prim.CurrentIndex) ctxAddLE32
           >>> ctx8Finalize
templateWithBip341Jets :: (Assert term, Primitive term, Witness term) => term () ()
templateWithBip341Jets = template &&& hW >>> eq >>> verify
   where
    template = ctx8InitTag "TemplateHash"
           >>> ctxWith (primitive Prim.Version) ctxAddLE32
           >>> ctxWith (primitive Prim.LockTime) ctxAddLE32
           >>> ctxWith SigHash.inputSequencesHash ctx8Add32       -- stand-in for bip341 sha_sequences
           >>> ctxWith SigHash.outputsHash ctx8Add32              -- stand-in for bip341 sha_outputs
           >>> ((unit >>> Tx.currentAnnexHash) &&& iden >>> match noAnnex withAnnex)
           >>> ctx8Finalize
    addIndex = ctxWith (primitive Prim.CurrentIndex) ctxAddLE32
    noAnnex = ih >>> ctxWith (konst (w8 0)) ctx8Add1 >>> addIndex
    withAnnex = (oh &&& ih) >>> ih >>> ctxWith (konst (w8 1)) ctx8Add1 >>> addIndex
            >>> ctxWith Tx.currentAnnexHash (oh &&& drop verify >>> ctx8Add32)  -- stand-in for bip341 sha_annex
