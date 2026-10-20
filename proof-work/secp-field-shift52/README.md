# Original C uint128 shift support for field multiplication

The unchanged field multiplication routine in `C/secp256k1/field_5x52_int128_impl.h`
uses `secp256k1_u128_rshift` at both 52 and 64 bits. Existing reusable support
covered 64 only. These four proof modules add the actual **52-bit C call**,
its two current output loads, exact unsigned 128-bit division by `2^52`,
permission preservation and outside-accumulator memory framing. The integer
bridge holds for every pair of `int64` limbs, including maximal values.

`Rep` and `Oracle` reuse that execution proof to summarize the helper inside
larger symbolic executions. The oracle is a proved internal-call summary,
not an external-library assumption. Its two stores and final representation
are derived, not hypotheses substituted for the required call.

## Exact boundary

- Actual fixed `C.jets_secp.f_secp256k1_u128_rshift` and `secp_ge`; existing
  RECKLESS generation configuration unchanged. This is not a new proof of
  the separate assertion-enabled AST in `jets_secp256k1.v`.
- A readable/writable 16-byte accumulator at block offset zero; symbolic
  summaries require its existing owned-region contract. This covers the
  caller's allocated accumulator structs, not arbitrary pointer layouts.
- Constant shift count 52. Existing 64-bit support remains unchanged.
- No new public jet, registry entry, coverage increment, field-product
  arithmetic theorem or complete `fe_multiply`/`fe_square` equivalence yet.
- Production C, specifications, API, main proof sources and user staging
  are unchanged. Sources here have `.source` suffixes and are unregistered.

## Verification and continuation

Next: compose the proven 52/64-bit shift summaries and execute the actual
`fe_mul_inner`, including the intended output/input alias. Then prove its
five-limb value/range bridge from the actual machine expressions, discharge
its input bounds from `read_fe`, and compose the original public jet with
its literal Simplicity specification. Do not claim that an abstract field
identity, raw symbolic run or pure helper alone proves that jet.

The original symbolic executor cannot fold the computed C shift count
`64 - 52` into the syntactically constant form its shift evaluator accepts.
Its initial exploratory `None` was an executor limitation, not a C mismatch.
The direct Clight proof evaluates the original expression without rewriting
the AST, extends the existing field-layout lemmas, and explicitly derives
that the first store preserves the high limb read by the second store.
