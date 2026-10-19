# Scoped SHA ready-contract review

These are unregistered candidates, not an acceptance receipt or an exhaustive
memory/process-history review. They reuse the original-C SHA proofs and their
frozen canonical definitions on `cafb9b31`; no C or canonical source is changed.

## What the new contracts derive

`jet_sha_partial_ready` supplies twelve concrete adapters: add 1, 2, 4, 8, 16,
32, 64, 128, 256 and 512 bytes, add Buffer511, and finalize. The shared lemma
retains the actual Clight function call, empty trace, canonical option-dependent
return, success output/prefix/cursor, and unconditional outside-memory framing.
It additionally derives the persistent global-state conclusion on both success
and failure. No execution, intermediate output, or permission-preservation
premise is introduced in a concrete adapter.

The caller provides operational `sha_ready_memory` provenance and the ordinary
initial input/output frame representations. The ready predicate is a sequence
of actual AST initialization, CompCert allocations and successful stores or
byte stores into freshly allocated private blocks. Its constructors do not
assume SHA global values. Their preservation theorem derives those values and
maximum-permission bounds. Empty byte stores are allowed. A frame-construction
theorem derives existence of both pointer/cursor stores from allocation rights
and preserves observations on initially valid unrelated blocks.

The persistent contract uses maximum rather than only current permissions,
because external calls may change current permissions. The shared Clight2
execution theorem derives maximum-permission monotonicity from the actual
entry/body/free and external-call semantics. Its external-call property axioms
already occur in the repository allowlist; their per-result use must still be
included in snapshot review before integration.

## Canonical program wiring inspected

The catalog in `Haskell/Core/Simplicity/CoreJets.hs:782-793` binds Add1 directly
to `ctx8Add1`, Add2 through Add512 to vectors of depth 1 through 9, Buffer511 to
`ctx8AddBuffer buffer511`, and finalize to `ctx8Finalize`. The adapters retain
exactly those depths, concrete C functions and existing polymorphic Coq ports;
none switches to a byte-list or arithmetic model as its final specification.

The inspected `Programs/Sha256.hs:181-210` structure matches the existing ports:

- Add1: buffer snoc; full-block buffer reset, checked counter increment and
  `hashBlock`; then `verifyNumCompression` before returning the context.
- Addn: SingleV is Add1; DoubleV applies the recursively selected program to
  each half in order. Coq `ctx8_addn_spec` has that same recursion.
- Buffer: SingleB distinguishes absent/present byte and still verifies the
  count when empty; DoubleB processes its vector then recursively processes
  the remainder. Coq `ctx8_add_buffer_spec` preserves those branches.
- Finalize: verify and clear the counter, append the `2^63` padding word using
  Add8, zero-pad the residual buffer, construct the shifted/modular length,
  project the final block and invoke `hashBlock`. The existing clear-count,
  pad, bit-length and final-block ports are retained.

This records inspected wiring and structure, not a replacement for formal
proofs or a complete transitive SHA source-correspondence gate. The separate
`check-ready-boundary.py.source` checks twelve catalog-to-adapter bindings,
their exact concrete theorem statements, the complete partial-state contract
and operational setup constructors. Its companion test rejects 22 mutations,
including impossible premises, weakened output/framing, wrong functions or
depths, assumed startup facts and comment spoofing. The boundary gate does not
compare the count assertion, buffer/padding/projection ports against their
canonical implementations. That comparison is preserved separately in
`ready-ports-review.json`: 26 typed Coq declarations and four primary Haskell
implementation/type regions, including the actual `mkLibAssert` definition,
not the earlier library mapping. `check-ready-ports.py.source` checks this
reviewed text; its companion test rejects 44 targeted mutations in all Coq
ports and selected canonical guards, constants, depths, projections and types.
This is source-level correspondence evidence, not formal Haskell translation.
Underlying `hashBlock`, word arithmetic, assertion commitment identity and
type/notation definitions remain separate inherited review obligations.

## Verification and remaining boundaries

All ten archived modules compile freshly with Coq 8.17.1/OCaml 4.14.4. The
startup and shared Clight memory modules independently pass `coqchk`. The new
setup-to-block whole-chain check also passes with exit 0, with no unsafe,
type-in-type or assumed-positivity flags. Independent whole-chain checking of
the twelve adapters now also passes with exit 0; its log is
`/tmp/jet-sha-startup-review.8YYJeG/partial-ready-kernel.log`. Its 15 library axiom
names match the existing allowlist with no unsafe flags. Snapshot review and
full integration acceptance remain pending.

`jet_sha_setup_frames` adds five compiled results. It derives owned-block
validity and constructs fresh frame records with unchanged prior loads and
permissions. Its frame-pair theorem derives both metadata structures, their
distinctness and cursor write access. The represented-frame theorem preserves
existing input cells and derives `write_frame_at` from initial backing-buffer
permissions/loads and cursor bounds, without assuming zero output contents.
Finally `sha_256_block_from_represented_buffers` derives the complete actual
block call, canonical output, prefix/cursor, outside-memory loads and persistent
state after constructing both metadata records. Independent whole-chain kernel
checking passes with exit 0, logged in
`/tmp/jet-sha-startup-review.8YYJeG/setup-frames-kernel.log`; all 15 library axiom
names are allowlisted and no unsafe/type-in-type/assumed-positivity flags occur.
Backing-buffer allocation/initialization and connection to the actual evaluator
remain open; this does not certify unrestricted process-history coverage.

`jet_sha_setup_words` adds six compiled results, with successful assumption
printing. Actual `Mem.store` sequences retain private-setup provenance and
derive loads/permission preservation. A general aligned word-buffer allocation
and a 256-bit output witness initialize real storage with an arbitrary seed.
`sha_private_setup_block_frames` constructs both metadata records over that
fresh output while preserving the existing input. The final
`sha_256_block_with_fresh_output` retains actual C execution, canonical output,
prefix/cursor, outside-memory framing and persistent globals. It requires only
the represented input, its validity/cursor bounds and initial setup provenance;
output storage and metadata are not assumed. The uniform seed is a construction
witness, not a restriction on the general public contract. Whole-chain kernel
checking completed with exit 0 (session 95701) in
`/tmp/jet-sha-startup-review.8YYJeG/setup-words-kernel.log`. Input initialization,
general evaluator admissibility and integration acceptance remain open.

`jet_sha_setup_input` adds eight compiled results with successful assumption
printing. Its width-polymorphic word-list lemma decomposes canonical encodings;
an aligned-load lemma bridges 64-bit stored words to input cells. Actual private
stores in reversed physical slot order construct the complete logical input
stream. For every block-jet `(Word256, Word512)` value, its twelve 64-bit words
are initialized in 96 bytes of real allocated storage.
`sha_256_block_from_constructed_storage` now constructs input/output storage and
both metadata records and concludes the actual canonical block call, output,
prefix/cursor, outside-memory loads and persistent global state. Its sole
memory premise is operational startup/setup provenance, not an assumed frame,
execution or result. This is a fresh-setup existence result; it does not replace
the general public contract with that particular layout. Independent whole-chain
kernel checking of this newest consumer completed with exit 0 (session 5190) alongside
the invariant-based adapters, logged in `input-running-kernel.log` in the same
scratch directory. General evaluator/process-history admissibility, partial
context-input initialization and integration acceptance remain open.

`jet_sha_partial_running` adds fourteen compiled results. Twelve adapters
replace fresh setup provenance with `sha_persistent_global_state`, while
retaining the exact C function/type/canonical port and explicit `memcpy_model`.
The complete underlying partial-state contract is unchanged: actual call,
canonical return, success output/prefix/cursor, unconditional framing and
persistent state on both outcomes. A verified predecessor's persistent
post-state can now supply the next call's global invariant, without asserting
that its resulting memory still came solely from allocation/store setup.
The ordinary frame representations remain required; this alone does not prove
that arbitrary evaluator transitions preserve or construct those frames.
The new boundary gate rejects 21 mutations and also freezes the exact global
value/maximum-permission invariant. Independent whole-chain checking completed
with exit 0 (session 5190); 15 allowlisted library axioms, no unsafe flags.
Per-result assumption printing passes with exit 0, recorded
in `partial-running-assumptions.log`; actual snapshot comparison/integration
review remains pending.

Every context adapter explicitly retains `memcpy_model`: actual libc code is
not proved by these changes. Ready provenance covers fresh-private setup, not
all possible process histories. Complete backing-buffer constructors, linkage
to the actual evaluator setup, and inherited shared-frame admissibility remain
open. The registry stays at 349/533; no candidate here adds accepted coverage.
