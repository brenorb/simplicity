-- | No-number script proposals, with explicitly bounded Simplicity encodings.
-- See reports/BIP-INVENTORY.md for source revisions and scope limitations.
module JetDiscovery.Corpus.ScriptProposals (entries) where

import Prelude hiding (drop, take, not, and, or)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as BSL

import Simplicity.Term.Core
import Simplicity.Programs.Bit
import Simplicity.Programs.Generic (eq)
import qualified Simplicity.Programs.Arith as Arith
import Simplicity.Bitcoin.Term (Primitive, primitive)
import qualified Simplicity.Bitcoin.Primitive as Prim
import qualified Simplicity.Bitcoin.Programs.Transaction.Lib as Tx
import Simplicity.Bitcoin.DataTypes (Outpoint(..))
import Simplicity.Ty.Word

import JetDiscovery.Lib.Bytes
import JetDiscovery.Tx
import JetDiscovery.Types

-- | Tadge Dryja's OP_CIV: a fixed promised outpoint occurs at a witness index.
-- The nonce is fixed by this leaf's commitment, as in the proposed Tapscript.
civ :: (Assert term, Primitive term) => term Word32 ()
civ = (primitive Prim.InputPrevOutpoint >>> verify) &&& konst promisedW >>> eq >>> verify
 where
  promisedW = (w256 0x1234, w32 7)

-- | A withdrawal cap using the current-index version of OP_INOUT_AMOUNT.
-- Preserve the complete output script commitment, and forbid an amount
-- increase or a withdrawal above the fixed per-transition allowance.
amountCap :: (Assert term, Primitive term) => term () ()
amountCap = sameScript &&& amountOk >>> unit
 where
  sameScript = Tx.currentScriptHash &&& (primitive Prim.CurrentIndex >>> primitive Prim.OutputScriptHash >>> verify) >>> eq >>> verify
  amountOk = Tx.currentValue &&& (primitive Prim.CurrentIndex >>> primitive Prim.OutputValue >>> verify) >>> Arith.subtract word64
         >>> ((oh >>> not iden >>> verify) &&& (ih &&& konst (w64 5000000000) >>> Arith.le word64 >>> verify))
         >>> unit

type Signed64 = (Bit, Word64)
type Signed128 = (Bit, Word128)

-- | The arithmetic draft's signed-64 operands and widened-128 product.
-- Encoding is typed sign/magnitude here; Script's byte encoding is not priced.
signedMultiply :: Assert term => term (Signed64, Signed64) Signed128
signedMultiply = (inRange oih &&& inRange iih) &&& product >>> ih
 where
  inRange t = t &&& konst (w64 (2 ^ (63 :: Int) - 1)) >>> Arith.le word64 >>> verify
  magnitude = oih &&& iih >>> Arith.multiply word64
  -- A zero product has positive sign, including negative-zero operands.
  sign = and (not (magnitude &&& konst (toWord128 0) >>> eq)) (xor ooh ioh)
  product = sign &&& magnitude

entries :: [Entry]
entries =
  [ Entry
    { entryId = "op-civ-linked-input"
    , entryTitle = "OP_CHECKINPUTVERIFY: authorize through a committed sibling outpoint"
    , entrySpec = "Tadge Dryja, OP_CIV, 2025-11-01; vendor-specs/bip-inventory/proposals/op-civ.eml"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "matching, reordered, absent and different sibling outpoints; equality checked against transaction inputs"
    , entryAssumptions = ["promised outpoint and a privacy nonce are constants committed by this leaf; only the locating input index is witness"
                         ,"another input must authorize the joint transaction; its signature is validated when that input is executed, as in OP_CIV"]
    , entryProgram = \ix -> Prog (konst (w256 0xa12b) &&& witness (w32 ix) >>> ih >>> civ)
    , entryVectors =
        [ Vector "committed sibling at index 1" (civEnv [own, promised]) 1 Accept
        , Vector "sibling located after input reordering" (civEnv [promised, own]) 0 Accept
        , Vector "wrong input selected" (civEnv [own, promised]) 0 Reject
        , Vector "index beyond input count" (civEnv [own, promised]) 2 Reject
        , Vector "same txid, different vout" (civEnv [own, Outpoint (hashFromInteger 0x1234) 8]) 1 Reject
        , Vector "same vout, different txid" (civEnv [own, Outpoint (hashFromInteger 0x1235) 7]) 1 Reject
        ]
    }
  , Entry
    { entryId = "op-inout-amount-withdrawal-cap"
    , entryTitle = "OP_INOUT_AMOUNT application: preserve a vault script and limit the amount released"
    , entrySpec = "Chris Stewart current-index draft at 92c108136a0400b3a2fd66ea6c291ec317ee4a01; vendor-specs/bip-inventory/proposals/op-inout-amount.mediawiki"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "satoshi amounts above 32 bits, exact allowance, over-limit withdrawal, underflow and destination substitution"
    , entryAssumptions = ["matches the draft's current-input/current-output index semantics, rather than the later bitmap-sum variant"
                         ,"cap is per transaction transition; a delay/signature is required for a rate-limited production vault"]
    , entryProgram = \() -> Prog amountCap
    , entryVectors =
        [ Vector "exact 50 BTC allowance" (amountEnv 20000000000 15000000000 same) () Accept
        , Vector "no withdrawal" (amountEnv 20000000000 20000000000 same) () Accept
        , Vector "one satoshi above allowance" (amountEnv 20000000000 14999999999 same) () Reject
        , Vector "amount underflow" (amountEnv 20000000000 20000000001 same) () Reject
        , Vector "destination substitution" (amountEnv 20000000000 15000000000 (BS.replicate 34 9)) () Reject
        ]
    }
  , Entry
    { entryId = "draft64-signed-widening-multiply"
    , entryTitle = "64-bit arithmetic draft: signed operands and a widened 128-bit product"
    , entrySpec = "Chris Stewart 64-bit arithmetic, PR2073 head fd04d0a8a9d4dbb8a7ff14d8e94b1565067ecc0f (closed draft); vendor-specs/bip-inventory/proposals/64bit-arithmetic.mediawiki"
    , entryCategory = CovenantBip
    , entryVectorSource = Derived "Haskell Integer multiplication; signed operand boundaries, zero, negative result, invalid magnitude and wrong result"
    , entryAssumptions = ["typed sign/magnitude operands; this measures arithmetic and range checks, excluding Script-number byte parsing"
                         ,"operand magnitudes at most 2^63-1; product magnitude fits 128 bits"]
    , entryProgram = \(a,b,r) -> Prog (witness ((s64 a,s64 b),s128 r) >>> (take signedMultiply &&& ih) >>> eq >>> verify)
    , entryVectors =
        [ Vector ("product " ++ show a ++ " * " ++ show b) anyEnv (a,b,a*b) Accept
        | (a,b) <- [(0,-7),(7,-9),(-7,-9),(2^63-1,2^63-1),(-2^63+1,2^63-1),(2^40,2^45)] ] ++
        [ Vector "magnitude outside signed-64 operand range" anyEnv (2^63,1,2^63) Reject
        , Vector "wrong product" anyEnv (7,-9,63) Reject ]
    }
  ]
 where
  own = dummyOutpoint 0
  promised = Outpoint (hashFromInteger 0x1234) 7
  civEnv ops = mkEnv (mkTx 2 [mkInput op 1000 mempty 0 | op <- ops] [mkOutput 900 mempty] 0) 0 defaultTap
  same = unhex "5120" <> BS.replicate 32 0x55
  amountEnv inputValue outputValue script = mkEnv
    (mkTx 2 [mkInput own inputValue (fromStrict same) 0] [mkOutput outputValue script] 0) 0 defaultTap
  anyEnv = mkEnv (mkTx 2 [mkInput own 1000 mempty 0] [mkOutput 900 mempty] 0) 0 defaultTap
  s64 n = (toBit (n < 0), w64 (abs n))
  s128 n = (toBit (n < 0), toWord128 (abs n))
  fromStrict = BSL.fromStrict
