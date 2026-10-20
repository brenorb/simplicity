# Scalar multiplication: checked original-C helper closure

The final freshly compiled theorem is
`MulC.jet_secp_u128_mul_exec.eval_u128_mul_owned_product`.
It proves the actual `jets_secp.f_secp256k1_u128_mul` call, return `Vundef`,
current loads of **both** product limbs, preserved owned representation and
outside-region memory framing. The underlying actual
`f_secp256k1_umul128` call returns the low limb and stores the high limb.
The input values are arbitrary int64s; initial output values are unrelated.
Storage contracts are owned 8-/16-byte regions, not arbitrary valid pointers.

The numeric bridge reuses the existing, checked
`C.jet_umul128_value.umul128_machine_observation` (already used for core
arithmetic jets). Small definitional equalities identify the new symbolic
execution's exact machine expressions with those existing observations.
No mathematical replacement of a public Simplicity specification was made.
The wrapper executes the real internal helper through a one-function table
whose actual symbol binding is proved; no oracle or call premise is assumed.

## Reproduce / continue

Compile from the dependency Coq directory, with the pinned compiler and
`ulimit -S -s 65520`:

The actual `u128_accum_mul` allocation/call/cleanup and full modulo-128-bit
value observation are now checked in `../scalar-mul-accum` (11 further
results, nine closed); this archive and its 17-result evidence stay unchanged.
Next: original `scalar_mul_512` column/carry execution and product value;
then `scalar_reduce_512`. Reuse existing reader, generic Word256 writer,
owned public lifecycle, core product observations and literal-program
bridges. Prove exact helper summaries before using them to limit symbolic
expression growth; do not introduce assumed correct arithmetic, execution,
output, permissions or frees.

Keep the end-to-end roots in view: original public `scalar_multiply` and
`scalar_square` against their **literal canonical Simplicity programs**.
Neither is proved by this helper closure. No current failing Coq goal remains.
The initial helper compilation failed only because `repeat split` expanded
already-established representation/framing; `coqtop Show` exposed the
mismatch and explicit conjunction packaging fixed it, without new premises.
