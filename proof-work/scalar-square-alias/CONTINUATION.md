# Continue square through the real function and public boundary

## Verified function boundary supersedes the earlier next-step list

`../scalar-square-function` now independently kernel-checks the complete
original `scalar_mul(a,a,a)` function: real allocation, entry, both calls,
void return, free and four actual post-free scalar loads. Its three modules /
nine results passed fresh compilation and exact contract/dependency review.
Do not redo items 1-4 of the historical list below. Continue with the public
single-reader/writer square wrapper using that archive's `CONTINUATION.md`.
No public square equivalence or new jet coverage is claimed yet.

Last verified declaration:
`SqrC.jet_secp_scalar_square_body.exec_scalar_square_body_inplace`.
The five modules / 22 results and full reports are independently kernel-checked.
There is no failing proof goal or incomplete declaration in this archive.
Do not redo its shared-pointer product, denotation or reduction proofs.

## Immediate live audit

Poll existing full multiply acceptance **38093**, never restart on observation
timeout. Log `/tmp/jet-scalar-multiply-integration.yIS07H/full-acceptance.log`.
The last observed phase passed the **922-module** kernel and entered the
assumption gate. All candidate sources, scripts, registries, C/Haskell and
snapshots remain frozen. On terminal success, follow
`../scalar-multiply-integration/CONTINUATION.md` for receipt/post-run review and
preserving dirty main work. Do not count square as covered from this archive.

## Next proof step

1. Start new, disjoint scratch modules importing this frozen `SqrC` closure.
   Derive the actual `scalar_mul` allocation from **one** owned scalar region.
   Existing `C.jet_secp_scalar_mul_caller_alloc` has reusable fresh 64-byte
   cell validity/reindexing lemmas, but its rotate/validity/allocates theorems
   explicitly expect two inputs and cannot be applied directly.
2. Prove a one-input rotation of the appended allocation into `[l,a]`, using
   allocation freshness and `region_u64_transport`. Its eight product cells
   stay uninitialized (`None`); do not assume initial output values.
3. Adapt `C.jet_secp_scalar_mul_caller_function`'s actual entry/temp bindings
   so `_r`, `_a` and `_b` all denote the same scalar. Apply the checked body
   here, obtain the real product-array Freeable permission from the reduction
   output, then derive its actual `Mem.free_list`. Keep the post-free scalar
   representation and outside-input framing. An expression layout may repeat
   a pointer; an owned `rep` may not repeat that region.
4. Observe the four output limbs in the actual post-free memory, reusing
   `scalar_mul_output_layout_indep` and the existing reducer numeric/kind
   lemmas. The numeric environment is `product_reduce_rho (square512_rho rho)`.
5. Close the public square wrapper with **one** real scalar reader and the
   actual two locals (`src`, `a`), source struct copy, writer/cursors, true
   return and all local frees. Reuse reader/writer support, not the multiply
   wrapper's two-input or three-local preconditions.
6. The literal Haskell target at
   `Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:584` is
   `iden &&& iden >>> scalar_multiply`. Introduce/check its corresponding
   canonical Coq term and parametric adapter, not just a square/modulo function.
   Existing literal multiplication numeric bridges may be instantiated at
   equal **values** (without asserting duplicate memory ownership).

After a complete public root: independently check its changed closure, exact
types/definitions/per-result dependencies and source identity, then integrate
only the selected square jet through reviewed full acceptance. Keep the public
contract general within the intended valid-frame scope, with no assumed call,
result, post-memory representation, allocation or free premises.

## Checked commands and state

The complete pinned compiler/namespace reproduction is in `README.md` and
the manifest. All square verification handles are terminal: **63195** build,
**32921** assumptions, **21157** kernel (all exit 0); contracts returned
terminal exit 0 directly. Do not poll or restart those completed runs.
Both archive reviewers are read-only and reject source/compiled/report drift.
They require the recorded scratch artifacts, not merely this durable source.

Main remains separate (351/533 at last plan); the multiply candidate's predicted
360/533 is not accepted until its complete gate terminates successfully.
Keep the all-533 goal active. Preserve unrelated main staging and Claude's
Elements/memcmp/transaction-builder scope. Signed local commits, no push.
