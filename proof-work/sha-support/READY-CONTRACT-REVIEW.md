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

## Verification and remaining boundaries

Every context adapter explicitly retains `memcpy_model`: actual libc code is
not proved by these changes. Ready provenance covers fresh-private setup, not
all possible process histories. Complete backing-buffer constructors, linkage
to the actual evaluator setup, and inherited shared-frame admissibility remain
open. The registry stays at 349/533; no candidate here adds accepted coverage.
