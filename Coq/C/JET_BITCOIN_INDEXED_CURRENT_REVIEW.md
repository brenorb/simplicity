# Per-contract review: inherited Bitcoin indexed and current getters

This reviews eight existing registered local contracts at published proof tree
`ad851dd955e4735895e67d1f4977e756154c6aad`. It changes no proof, production C,
canonical program, acceptance input or coverage registration. The global review
remains partial. No discrepancy was found in these local chains under their
explicit initial frame/environment representations. Constructor establishment
and general memory-contract admissibility are separate, still-open boundaries.

## Canonical binding and actual public contracts

C names have prefix `simplicity_bitcoin_`; public theorem names have prefix
`bitcoin_` and suffix `_local_spec`. The table lists the actual registered
modules and the exact canonical primitive/composition, not an integer-model
substitute. All calls execute in the actual `bitcoin_ge`.

| C suffix | Canonical catalog/program | Public module | Initial representation and output | Derived execution |
| --- | --- | --- | --- | --- |
| input_value | InputValue, primitive Prim.InputValue | jet_bitcoin_input_value_local | input count/array; amount at input+104; Some Right Word64 or Some Left Unit, 65 cells | bitcoin_input_value_mid derives read32, bounds bit, actual field load/write64 or skipBits64; wrapper derives entry/copy/free |
| input_sequence | InputSequence, primitive Prim.InputSequence | jet_bitcoin_indexed_scalar_jets | indexed_scalar_rep, input stride 160/field 144, tx array+0/count+448; 33 cells | bitcoin_indexed_scalar_local specialized with actual body, field expression, writer and canonical semantic bridge |
| output_value | OutputValue, primitive Prim.OutputValue | jet_bitcoin_indexed_scalar_jets | indexed_scalar_rep, output stride 40/field 0, tx array+8/count+456; 65 cells | Same generic execution proof, actual output shape and write64 specialization |
| current_value | CurrentValue, CurrentIndex >>> assert(InputValue) | jet_bitcoin_current_jets | current_scalar_rep, ix at env+48, input amount+104; Word64, 64 cells | bitcoin_current_value_sem derives a present input and current_scalar_local derives actual precheck, load and write64 |
| current_sequence | CurrentSequence, CurrentIndex >>> assert(InputSequence) | jet_bitcoin_current_jets | current_scalar_rep, ix at env+48, input sequence+144; Word32, 32 cells | Corresponding canonical current-sequence bridge and actual write32 specialization |
| input_prev_outpoint | InputPrevOutpoint, primitive Prim.InputPrevOutpoint | jet_bitcoin_indexed_ptr_jets | indexed_ptr_rep/outpoint_rep, input+64; eight hash words then index at outpoint+32; 289 cells | Actual indexed bounds branches; present branch derives prevOutpoint/writeHash/write32; absent branch derives skipBits288 |
| output_script_hash | OutputScriptHash, primitive Prim.OutputScriptHash | jet_bitcoin_indexed_ptr_jets | indexed_ptr_rep, output+8; cache equals byteStringHash(txoScript), 257 cells | Actual indexed branches; derived writeHash/write32s8 or skipBits256 |
| current_prev_outpoint | CurrentPrevOutpoint, CurrentIndex >>> assert(InputPrevOutpoint) | jet_bitcoin_current_ptr_jets | current_ptr_rep/outpoint_rep, input+64; Word256 * Word32, 288 cells | Canonical current-index bridge, actual precheck and derived payload helper; no assumed helper execution |

Canonical bindings inspected: `Haskell/Simplicity/Bitcoin/Jets.hs:203–219`;
primitive semantics: `Haskell/Bitcoin/Simplicity/Bitcoin/Primitive.hs:123–151`;
current compositions: `Haskell/Simplicity/Bitcoin/Programs/Transaction.hs:88–100`.
`Programs/Bit.hs:49–50` supplies the literal assert construction used in
`bitcoin_assert_spec`: pair with unit, then assertr with fail0 commitment and
take iden. `bitcoin_comp_sem`/`bitcoin_assert_sem` derive that composition's
semantics; the canonical current program is not replaced by a direct primitive.

The real C bodies are in `C/bitcoin/bitcoinJets.c:83–124,153–171,214–237,246–251`.
`writeHash` and `prevOutpoint` are the actual static functions at lines 20–34.
Body/parameter/local/temporary/return checks specialize the generic wrappers
to those directly generated functions. The accepted target's four ASTs match
independently regenerated artifacts; no function body is overwritten here.

## Expanded conclusions, lookup absence and domains

All eight public propositions are the complete `application_jet_local_spec`
or `application_jet_local_spec_sep`. Their conclusions establish a final memory,
the canonical result, actual `Clight2.eval_funcall`, E0, true C return, exact
encoded output, preserved write prefix, exact destination cursor decrement and
unchanged loads outside the destination cursor/output footprint on initially
valid blocks. They assume no execution, desired output, final memory or final
Freeable permission. There is no extra libc/helper/global premise in these
eight public types; their inherited Coq/CompCert assumptions remain explicit.

Indexed lookup absence is **not assertion failure**. Canonical `atInput`/
`atOutput` return Some Left Unit; the real C writes a false presence bit,
skips the payload cells and returns true. Present lookup returns Some Right.
The execution proofs derive both branches from the unsigned bounds comparison
and nth_error. `encode` uses None padding on the absent alternative, not zeroed
payload bits or an invented hash/value. Payload sizes 32/64/256/288 give total
sum sizes 33/65/257/289. All Word32 lookup indices, including UINT32_MAX, remain
allowed; empty output arrays return the absent alternative even at index zero.

For current getters, `envIxBounded` and the uint32 input-count bound prove that
CurrentIndex's Word32 encoding loses no bits. The canonical composed assertion
therefore succeeds, and the real C's `numInputs <= ix` false-return branch is
unreachable in a represented valid canonical environment. A jet-specific
success/index-validity premise is not used. Behavior of physically invalid
environments is outside these local contracts, as it is outside canonical
Haskell `primEnv` (`Primitive.hs:99–106`).

`word64_signed_unsigned` and `decode_wide64_value` are universal bridges for
every Int64. The use of signed representatives for InputValue/OutputValue
does not exclude high-bit amounts. The current-value initial load uses the
unsigned representative and the proof applies `Int64.repr_unsigned` to the
same full-word bridge. Sequence and outpoint index preserve all Word32 values;
`decode_wide32_unsigned`'s range is derived from Int.unsigned_range. No monetary
bound, positive-fee premise or overflow exclusion occurs in these contracts.

Logical vector/script lengths retain the bounds of the original raw C API:
numInputs/numOutputs and raw buffer lengths are uint32_t; logical outputs may
be empty. Current-index validity implies nonempty inputs. No stricter numerical
payload bound is introduced by this review.

## Execution hypotheses are discharged at the public boundary

Generic adapters have semantic, expression and helper-call hypotheses. The
public specializations prove them rather than exporting them as assumptions:

- Scalar Hspec follows from the universal encoding bridges; Hval follows from
  actual sizeof/field-offset facts and the initial Mint64 load; Hsem unfolds
  the actual canonical primitive and matches nth_error on all indices.
- `bitcoin_read_wide_step` derives actual read32 from the initial encoded input
  in the fresh source-frame local. The initial source is copied by the real
  By_copy entry rule. Original loads and permissions survive allocation,
  copying and the local reader's cursor update.
- `bitcoin_writeBit_step`, `bitcoin_write_wide_step` and `bitcoin_skipBits_step`
  derive calls from writable output capacity. Indexed execution first reads
  count, writes the bounds bit, and either preserves/reloads the array pointer
  and selected field or follows the actual skip branch. `write_effect_seq` and
  `write_effect_lift` compose output, prefix, cursor and load preservation.
- Pointer Hpay is instantiated with `eval_bitcoin_writeHash_layout` or
  `eval_bitcoin_prevOutpoint_layout`. writeHash derives the linked write32s8
  loop and writers from the eight original Mint32 loads. prevOutpoint first
  writes those words, derives preservation of the Mint64 index load, then
  calls the real write32. Hash words precede the index in canonical encoding.
- Pointer Hpres derives preservation of the original payload representation
  across the presence-bit write. Hptr evaluates the actual address expression
  using stride, field offset and nonwrap bounds. Hsem derives exact canonical
  encoding in both indexed alternatives or the valid current composition.
- Current adapters derive the present input from the canonical environment;
  initial count/index loads prove the actual bounds comparison. The scalar
  current jets read all environment fields before their single output write.
- `bitcoin_wrapper_layout` derives function entry, fresh 16-byte allocation,
  source-frame assignment, actual body/return and Mem.free_list. Preserved
  Freeable permission proves cleanup. None of these are final-contract premises.

The core-helper transport was also inspected: `bitcoin_core_helpers` lists
the actual function pairs; checked symbol/find_funct facts and fundef_okb
validate the closure. `transport_main` inducts over actual execution, using
expression, binary-operation/layout, assignment, allocation and free-list
transport. Calls are resolved to checked internal functions, not assumed new
Bitcoin executions. The constant-branch exception has `const_cond_sound`.
External calls/builtins/indirect calls are rejected by this internal-helper
transport; it does not discharge memcpy_model or arbitrary global-state facts.

## Hash semantics and initial-memory boundaries

Outpoint hashes are logical primitive data, not computed by these jets.
Canonical integerHash256 reads big-endian bytes; Coq from_hash256 and the
eight-word writer preserve that order. The stored outpoint index represents
the full unsigned logical Word32 even though uint_fast32_t is 64 bits in the
pinned ABI.

OutputScriptHash computes the logical SHA from script bytes independently of
the physical cache. The initial uint32_array_at relation uses
`script_hash_words = hash256_reg (byteStringHash (txoScript txo))`; it neither
defines the abstract answer from arbitrary cache words nor assumes jet output.

The canonical hash implementation is local: `Digest.hs:120–121` calls
padSHA1, sha256Incremental and ivHash from `Digest/Pure/SHA.hs`. Its source was
compared with the actual VST SHA model used by Coq byteStringHash: big-endian
input words/output registers; 0x80 padding to 56 modulo 64 bytes followed by
the big-endian 64-bit bit length; the eight IV registers; all 64 round constants
and ordered steps; schedule offsets t-2,t-7,t-15,t-16; rotate/shift constants;
Ch, Maj, register rotation and feed-forward addition modulo 2^32. Haskell's
OR form of Maj and Coq's XOR form implement the same bit majority operation.
VST `generate_and_pad'_eq` relates its optimized padding to generate_and_pad.
The script-length uint32 bound avoids overflow of Haskell's Int length*8 in
the pinned 64-bit comparison. A source comparison is not a compiled theorem
about Haskell execution; its scope is explicit in the supplementary receipt.

Initial representations require valid field loads, logical correspondence,
address/nonwrap bounds and writable output capacity. Indexed footprints
separate environment/array pointers and the array from output writes because
the pointers/payload are read after the presence bit. Current outpoint needs
array separation because its payload helper reads while writing. These are
conservative local memory contracts; establishing their general admissibility
for legitimate allocations/aliasing remains in the shared-contract review.

`C/bitcoin/env.c:19–49` hashes script bytes in hashBuffer/copyOutput and copies
outpoints, amounts and sequences in copyInput. This source inspection explains
the representation; no Clight constructor-correctness theorem is claimed.

## Verification evidence and remaining classification

The diagnostic file outside repository load paths is
`/Users/brenorb/.codex/jet-proof-scratch/original-c/review_inherited_bitcoin_indexed.v`.
It contains 18 closed boundary examples and one general singleton/max-index
lemma: full-word high-bit/max amounts and sequences, missing/max indices,
empty outputs, current compositions, asymmetric outpoint hash/index order,
the empty-script SHA digest and absent-alternative padding. It Check/Print
Assumptions the eight actual public contracts. All retain the same six
inherited Coq/CompCert assumptions and no added libc/helper premise.

Compilation succeeded after correcting a Nat2Z iff direction/reduced comparison
and explicit imports. The failed tactic states were inspected with Show;
no unfinished/admitted theorem was compiled. Complete diagnostics supplement,
and do not replace, the source/definition/hypothesis/conclusion review above.

Verification evidence:

- Complete-file compilation: `/tmp/jet-inherited-bitcoin-indexed-review-compile.log`,
  exit 0 (session 78335 terminal).
- Separate kernel check: `/tmp/jet-inherited-bitcoin-indexed-review-kernel.log`,
  exit 0 (session 6266 terminal), with no unsafe kernel options.
- `/tmp/jet-inherited-bitcoin-indexed-source-review.json` records source hashes,
  equality with the compiled review worktree and the diagnostic source hash.
- `/tmp/jet-inherited-bitcoin-indexed-sha-source-review.json` checks all 64
  constants/round steps, 48 schedule recurrences and eight IV values against
  the actual canonical/VST sources. This supplements the algorithm review.

No new coverage is claimed. The eight rows concern existing contracts; they
do not certify all declarations in their support modules or every initial
memory placement. The stopped experimental declaration inventory has no path
overlap with these newly reviewed modules and is not reduced by this review.
The matrix now has 26 reviewed local contracts, 36 prior family reviews, one
prior complete chain, 284 registered rows requiring further evidence and 186
missing final registrations. These are review statuses under explicit local
contracts, not exhaustive recertification of the 347/533 registered inventory.
