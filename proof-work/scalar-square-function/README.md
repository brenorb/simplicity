# Complete original multiplication function with square's pointer alias

This archive proves the **actual original** internal C
`secp256k1_scalar_mul(a,a,a)` function call. It extends the checked body in
`../scalar-square-alias` through function entry, a real fresh uninitialized
64-byte product-array allocation, both actual calls, void return and the real
array free. Only one initialized owned scalar region is required. It derives
the final output ownership, all four actual post-free limb loads, the square
modulo the canonical group order and framing outside that scalar's footprint.

It is not yet the public `simplicity_scalar_square` jet's implementation-to-
literal-Simplicity equivalence. The wrapper's source struct copy, single
reader, writer, cursor/frame preservation, two-local lifecycle and canonical
term remain to be closed. The modular value is an internal bridge, not a
replacement target specification. No jet coverage, production C, registry or
accepted snapshot is changed. Scope remains LP64 / RECKLESS.

The original multiplication allocation, transport and output-observation
lemmas are reused. Their two-input ownership contract is not instantiated with
duplicated pointers: new one-input rotation/validity lemmas establish `[l,a]`
from the real allocation. The function's `_r`, `_a` and `_b` bindings all point
to the same scalar, while each local block is freed exactly once.

## Verified evidence

There are **nine results** and **five definitions**. Four results are closed;
three representation/allocation results retain the inherited four classical/
extensionality dependencies. Two execution roots retain those plus CompCert's
external and inline-assembly semantic parameters. The independent kernel
context matches the inherited 15-axiom allowlist and all three unsafe categories
are empty. No new axiom was added. The complete untruncated contract report is
11,285 bytes; 19 negative fixtures reject corrupted evidence in memory.

Engineering note: bare `apply scalar_mul_caller_word_count` timed out in the
word-count adapter. An isolated `Show`/`Check` experiment established the exact
specialization; `exact (scalar_mul_caller_word_count (square512_rho rho))`
compiled promptly. The final chain was rebuilt afterward; earlier failed
build **22561** is not success evidence. Keep that explicit argument.

Signed atomic local commits only; never push. The complete all-533 goal stays
active. Claude's shared/Elements work and unrelated main staging are untouched.
