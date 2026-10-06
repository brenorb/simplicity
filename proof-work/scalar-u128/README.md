# Scalar and uint128 helper sources

These 22 complete source files and one literal-source checker are preserved
verbatim. The `.source` suffix keeps them outside all accepted Coq load paths.
Materialize them into an external scratch directory for further proof work.
They use the `OriginalC` namespace; their accepted dependencies are pinned by
`dependency_base_commit`. Preserve that namespace and resolve its dependencies
before compilation. The historical checker contains local paths requiring
adaptation; it is retained as source, not installed as an acceptance gate.

Eighteen helper modules have matching historical compiled/kernel receipts.
That evidence concerns the helper statements, not full public scalar jets or
acceptance on the current branch. Four further complete source files need fresh
verification; `jet_secp_scalar_overflow_flags` has a known previous compilation
failure. A final `Qed` alone is not compilation or fidelity evidence.

The manifest distinguishes these groups and lists the remaining canonical,
helper-call and public lifecycle obligations. Nothing here increases coverage.
