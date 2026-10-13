# Extend the borrowed-rhs body through the real lambda caller

Last verified declaration:
`BorrowC.jet_secp_scalar_mul_borrowed_body.exec_scalar_mul_borrowed_body`.
The four modules / 14 results are freshly compiled and independently kernel-
checked. There is no failing Coq goal or partial declaration. Do not redo the
product, machine-value bridge, reduction or rhs-preservation proofs here.

The initial archive review exposed an unrelated historical collector bug:
the old multiply assembler included `BorrowC` in its excluded-module catalog.
Only that list drifted; selected modules and all candidate inputs were identical.
The collector now restricts both record formats to its four supported
namespaces, with `test-provenance.py` regression coverage. Exact parent and
borrowed reviews pass after that fix; do not weaken evidence comparisons.

## Next proof obligations

1. Derive `scalar_mul`'s actual allocation from input layout `[a,b]` where a
   is owned (32 bytes) and b is readable/non-owned. Reuse valid-block, fresh
   stack-cell and reindexing lemmas from `C.jet_secp_scalar_mul_caller_alloc`,
   but adapt its two-owned-input rotate/allocates contract to the mixed flags.
   The private 64-byte array remains uninitialized; no initialized output
   premise. Both valid input blocks are separate from the fresh allocation.
2. Reuse the unchanged actual `scalar_mul` function entry and temp bindings
   (`r=a`, rhs=b). Apply this checked body, derive the private-array Freeable
   permission from reduction output, perform its actual free and preserve both
   the output scalar and borrowed rhs through that free. Do not free b or
   assert ownership of it. `region_ok_lframe` is reusable for the preservation.
3. Observe four actual post-free output limbs and relate them to the existing
   scalar writer representation. Reuse the original arithmetic/literal product
   bridges; do not replace the eventual public target by a modulo function.
4. Establish the real global: `C.jets_secp.v_secp256k1_const_lambda` has a
   32-byte struct, four `Init_int64` values, `gvar_readonly=true`, nonvolatile.
   Match its actual symbol/loads and literal value from initialized program
   memory and prove the relevant preservation through callers. A reference
   initializer or unchecked equality comment is not initialization evidence.
   No need to prove that lambda is mathematically a cube root; the task is
   correspondence of the literal C data and the literal Simplicity term.
5. The Haskell public target is
   `(unit >>> scalar_lambda) &&& iden >>> scalar_multiply` in
   `Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:588`. C multiplies a by
   lambda in the other operand order; discharge that value bridge formally,
   retaining the literal term/parametric adapter. Normalize/read one actual
   scalar, call the helper with the global pointer, write literal output and
   derive the wrapper's two-local lifecycle/true return/cursors/framing.

The eventual public result may not assume the actual call, output, post-state,
allocation/free or cache establishment being proved. Keep any genuine program
initialization/global representation conditions explicit and discharge them
through actual program/caller theorems; do not silently assume the static global
is a private stack block or claim a global lemma closes the entire public root.

All this archive's verification handles are terminal exit 0: **41278** rebuild,
**72818** assumptions, contracts terminal chunk **514f97**, **79149** whole-
dependency kernel. Do not poll/restart them. Reproduce the exact commands and
read-only review/tests from `README.md`.

## Other live work

Square full acceptance **41316** is still live at the last actual poll. Its
937-module kernel passed; the assumption gate is running. Poll that same
handle; never restart on a quiet log/observation timeout. Log:
`/tmp/jet-scalar-square-integration.MAhL2g/full-acceptance.log`.
Keep its audited sources/metadata/C/Haskell immutable. On terminal success
follow `../scalar-square-integration/CONTINUATION.md` for exact receipt, post-run
review and preservation-safe main reconciliation (current staged patch hash
is recorded there). Square 361/533 remains provisional until all gates pass.

No overlap with Claude's shared/Elements reservation. Keep the full all-533
goal active and incomplete. Frequent signed atomic local commits; no push.
