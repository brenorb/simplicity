# Outpoint byte-order mismatch and canonical boundary

The actual Bitcoin Simplicity C/Haskell API exposes an outpoint's **raw32 wire/digest bytes** as Word256, with no byte reversal. The local `JetDiscovery.Tx.parseRawTx` reversed those bytes. Several local protocol programs then reversed the primitive value again, hiding the mismatch when tested only through that local parser. Their old passes establish execution under that former harness, not native standard-wire compatibility. Relevant historical compatibility claims and affected CMRs are withdrawn pending fresh canonical runs. No upstream C/Haskell/Coq/jet source is modified.

The correct repair is to preserve raw bytes in the local parser and remove compensating opHash reversals in the local programs/references/fixtures. The base `putNoWitnessTx` serializer is correct under its raw-byte convention. An initial display-codec bridge would only repair one serialized view while leaving the C primitive wrong for the original transaction; it was rejected and deleted. It is not a replacement for the canonical boundary repair.

## Exact C/Haskell byte flow

| Step | Source | Observed operation |
| --- | --- | --- |
| Raw C API input | `C/include/simplicity/bitcoin/env.h:32` | `prevTxid` is a32-byte byte array; no display-string conversion in the environment API. |
| C environment copy | `C/bitcoin/env.c:47` | `sha256_toMidstate(..., input->prevTxid)`. |
| Byte-array conversion | `C/sha256.h:99` | Reads consecutive four-byte groups with ReadBE32. This preserves the original byte stream as eight words; it does not reverse32 bytes. |
| Primitive frame output | `C/bitcoin/bitcoinJets.c:31` | `prevOutpoint` writes the eight words through `writeHash` then writes the numeric index. `writeHash` atline22 uses `write32s`; `C/frame.h:145` preserves word order and `C/frame.c:56` writes each word's high bits first. |
| Haskell Outpoint wire serialization | `Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs:95` | `get` reads Hash256 directly then LE32 index; `put` writes that same hash directly then LE32. |
| Haskell transaction serialization | `Haskell/Bitcoin/Simplicity/Bitcoin/DataTypes.hs:294` | `putNoWitnessTx` writes `opHash` directly atline309, and `txid` atline322 double-hashes that serialization. |
| Haskell primitive | `Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs:141` | `integerHash256` becomes Word256 directly; InputPrevOutpoint atline146 uses that encoder. |
| Haskell→C FFI | `Haskell/Simplicity/Bitcoin/FFI/Env.hs:112` | Passes `encode . opHash` directly as the C `prevTxid` pointer. `Haskell/cbits/bitcoin/env.c:22` only assigns that pointer. |
| Former local parser | `src/JetDiscovery/Tx.hs:139` before repair | Reversed the32 wire bytes before `hashFromBytes`, so both Haskell and the actual C FFI saw a different outpoint from the parsed transaction. |

`tools/BitcoinOutpointByteOrder.hs` calls the **actual C input_prev_outpoint jet**, not a simulated C path. The preserved pre-fix log `data/bitcoin-outpoint-byteorder-before-fix.txt` supplies the explicit counterexample: raw wire `00 01 ... 1f` yields exactly `00 01 ... 1f` from a canonical Haskell/C environment, while the former local parser makes both yield `1f 1e ... 00`. The numeric index0x01020304 remains16909060 in both paths. Base wire roundtrip fails only for the former parsed representation. The preserved before-driver source records the rejected display-bridge diagnostic as historical evidence; current regression uses the canonical boundary and simulates the former reversal explicitly.

## Complete local inventory and repair ownership

The complete pre-fix query inventory is `data/outpoint-byteorder-inventory-before.tsv`: all58 matching source/tool lines, including unrelated reversals, with classification/action. Search covered every `.hs`/`.py` under `src/JetDiscovery` and `tools`, not only new applications.

| Local area | Effect / repair |
| --- | --- |
| `Tx.parseRawTx` / `rawToSigTx` | Root owns parser repair: raw bytes retained. Every parsed transaction now must roundtrip through the base canonical serializer and expose actual raw bytes in both C and Haskell primitives. |
| `Corpus.Bip346Txhash.prevoutItem` | Root owns removal of the compensating rev256 before hashing prevouts. List-order `reverse acc` is unrelated and retained. |
| `Lib.SilentPayment` | Remove primitive opHash reversal and host output-derivation reversal. Keep little-endian **index** byte serialization and its wire-lexicographic ordering; raw hash order is already correct. Fresh proof/DER fixtures and CMR validation required. Its legacy reference already uses the correct base serializer; do not replace it with a display codec. |
| `Lib.ReserveProof`, `Ref.ReserveProof`, reserve tool/phantom constructors | Remove primitive/manual opHash reversal and reversed phantom construction. The commitment input stores the raw single-SHA digest directly. Check every parsed reserve outpoint against its actual original field, beyond checking only the phantom index or signatures. |
| `Lib.NumericDlc`, `Ref.NumericDlc` | Remove primitive/manual opHash reversal in BIP143 preimage construction. Base full-CET serialization already writes raw bytes correctly. Fresh exact digest, parsed outpoint and actual complete-verifier checks required; old15-case root is historical. |
| Draft `Lib/Ref.ArkRefresh` and package/tools | Preserve raw opHash in actual round data, standard messages, txid-derived child outpoints and wire assertions. Restore base transaction serialization. Do not run the unfinished certificate until the boundary is canonical. |
| `Lib.TaprootTx1` | Its typed contract already explicitly requires raw wire txid bytes; no reversal in its encoder. Callers must honor that contract. |
| `ScriptProposals.civ` | Direct native outpoint comparison to a program constant, with no serialization reversal. Constant interpretation is raw bytes; root may audit metadata separately. |
| BIP322 virtual messages | Independently construct raw virtual bytes; all-zero null outpoint is byte-order invariant, and to_sign uses the raw computed to_spend digest. Display-only diagnostic reversals do not enter the program. Root independently reviews this boundary. |
| SPV receipt / header references | Reversals are little-endian numeric PoW/header decoding, not native InputPrevOutpoint compensation. Their independently reconstructed historical payment bytes are not changed. |
| Ed25519, Keccak lanes, polynomial/list sorting and ranking scripts | Unrelated little-endian encoding or list ordering. Retained. |
| BIP352 source-vector extraction / direct core diagnostic | Published `txid` strings are explorer/display form and legitimately become raw wire bytes at the external source boundary. Direct core inputs already use those raw bytes. This is not a reversal of the native primitive and is retained. |

Fresh canonical fixtures go into the new `bitcoin-growth3` packet. The previously signed `bitcoin-growth2` packet and raw RTS logs remain immutable historical artifacts. Updated provenance explicitly distinguishes withdrawn compatibility evidence from future canonical results. New CMRs are expected where program reversals are removed; unchanged historical roots are not a success criterion.

## Canonical validation results

The raw-boundary diagnostic now passes against both actual C and Haskell primitives, including an asymmetric raw outpoint and an untouched published BIP341 transaction. `data/bitcoin-outpoint-byteorder-provenance.json` records tool/log hashes and hashes of the read-only upstream files establishing this convention.

The corrected TXHASH expression passes all150 supported upstream selectors
and its derived wrong-hash negative in64.445seconds, with one canonical
jetted CMR. Exact output, frozen executable and launch-source provenance are
in `data/txhash-canonical-wire-vectors.{txt,json}`. The permanent raw wire/base
serializer/primitive regression is included in the complete41-test cohort,
which passes in907.54seconds (`data/harness-canonical-current41.{txt,json}`).

The corrected SilentPayment and reserve programs pass all16 actual Simplicity vectors with same-CMR enforcement per vector. Every environment also passes canonical base serialization, every parsed raw outpoint and actual C primitive checks; all9 Silent fixtures pass an independent DER/actual legacy ECDSA check. New CMRs and213.299-second/3G-capped run provenance are in `data/bitcoin-growth2-canonical-provenance.json`. The independent reserve reference verifies the official ALL01 digest and all raw proof outpoints. Numeric now passes all15 actual complete-verifier vectors plus15 wire/Haskell/actual-C checks, and current Bark hArk passes all14 plus14 corresponding checks. New roots, exact frozen sources and logs are recorded in `numeric-dlc-canonical-provenance.json` and `ark-refresh-canonical-provenance.json`. No affected historical CMR is reused.
