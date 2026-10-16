# Selected canonical correspondence: seven Elements hash-word jets

This source review supplements the actual compiled C-to-program proofs in
`../elements-stream/`. It is not a substitute for those proofs, recursive
kernel checking, normal registration or full acceptance.

The positive source check and all203 read-only corruption tests completed
with exit zero, recorded by `SOURCE-REVIEW.json`:

```sh
python3 -B proof-work/elements-stream-source/finish-source.py /private/tmp/jet-elements-stream.1zVQb2CU
```

The receipt binds the checked private source fingerprint, completed compile
receipt, exact review/model/tools, source hashes, command exits and logs, and
preserved main/index state. Its source-only field explicitly does not claim
to have checked the running recursive kernel result.

## Implementation-to-specification chain reviewed

Every selected catalog dispatch routes through the corresponding unpacked
`SigHash.Lib` selector to `SigHash.lib`. This selects the canonical SHA library
and assertion library, not an unspecified alternative implementation. The
Coq target is `elements_prim_words_hash_spec` over the actual Elements primitive
algebra, using the existing literal `hash_words_spec` / `hash_loop_spec` and
the same initialization, iteration, update and finalization programs.

| C suffix | Primitive | Bytes/element | Counter | C cache offset |
| --- | --- | --- | --- | --- |
| output_scripts_hash | OutputScriptHash | 32 | 32 bits | tx+88 |
| output_range_proofs_hash | OutputRangeProof | 32 | 32 bits | tx+120 |
| output_surjection_proofs_hash | OutputSurjectionProof | 32 | 32 bits | tx+152 |
| input_scripts_hash | InputScriptHash | 32 | 32 bits | tx+280 |
| input_sequences_hash | InputSequence | 4 | 32 bits | tx+344 |
| input_script_sigs_hash | InputScriptSigHash | 32 | 32 bits | tx+408 |
| tappath_hash | Tappath | 32 | 8 bits | taproot+40 |

The complete original C bodies select these cache fields and call `writeHash`.
Their checked contracts require the caches to represent hashes of those same
raw logical data, and retain the original function, linked global environment,
Unit/Word256 types, pointer/field layout, frame separation and output/cursor/
prefix/preserved-load guarantees. No final statement assumes the desired
execution or output. All seven actual C endpoints have six inherited execution
assumptions; the caller's cache representation is not silently discharged.

## Shared structure and edge cases

- `hash_words_reader_sem` generalizes the environment-dependent evaluation
  layer, not the hash algorithm or primitive signature. The formal proof
  reuses existing counter traversal, prefix absorption and SHA finalization.
  Empty arrays and both early-stop/counter-full branches remain covered.
- The word/vector depth parameters are5 for256-bit payloads and2 for32-bit
  sequences. Counter depth5 means32 bits; depth3 means8 bits. Finite-counter
  truncation is explicit in the represented value, not replaced by a sample.
- Script, scriptSig, range-proof and surjection-proof data are raw byte lists.
  Selected primitives hash those bytes before the outer stream hashes their
  encoded digests. An explicit asset/amount exposes an empty proof; a
  confidential value exposes its proof bytes. The existing reviewed proof-view
  source/closed-bridge infrastructure is reused for this boundary.
- These jets do not serialize a confidential point or field coordinate.
  No arbitrary-word-as-valid-field/point assertion is used to excuse a carrier
  mismatch. That boundary for other, unselected jets is not established here.
- Sequence values use the native unsigned32-bit interpretation, including
  high-bit values; raw hash words reuse the checked four-limb unsigned decoder
  and the literal Simplicity word traversal. Tappath indexing uses Word8, with
  the existing logical environment's at-most128 path bound unchanged. Empty
  paths are allowed; these getters do not load an element through a path pointer.
- The Haskell lens/bytestring/crypto runtime is not formally verified by these
  checks. The Coq proofs target the project's primitives; this review checks
  the selected source correspondence and leaves host-library boundaries
  explicit. It does not accept every clause of the general Elements port.

The fixed runtime model is `.py`, not an unfingerprinted JSON input. Deployment
under `Coq` will therefore bind it in the normal audit fingerprint. The new
comparison preserves whitespace inside string literals so a changed primitive
namespace cannot be hidden by stripping spaces. The corruption suite tests
names/types/dispatches, SHA/program helpers, proof views, byte widths, cached
fields, and complete public contracts, including vacuous added premises.

Next: independently bind the recursive kernel terminal result and complete
proof evidence, then prepare a normal admission delta over the checked436
successor. Neither this source checkpoint nor its snapshots add coverage or
establish that the actual C environment constructors populate all caches.
