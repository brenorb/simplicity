# Original field multiplier: through the third output store

`exec_original_fifth_integer_checkpoint` executes the first 97 original
statement heads of `f_secp256k1_fe_mul_inner`, through `r[2]` and the following
52-bit `c` shift. Its slice boundary was inspected in the normalized Clight
statement tree; source-splitting equalities are checked against the unchanged
function body. The preceding `d` shift is by **64**, not 52 bits.

Entry comes from the actual post-`r[1]` checkpoint. The new current-memory
output load is established alongside preservation of `r[0]` and `r[1]`.
The proof returns an updated reusable checkpoint, preserving original cached
input limbs, live temporaries and framing outside the original footprint.
It does not assume a fresh array or reuse old loads after stores.

The arithmetic bridge reuses bounded accumulation for the three low-column
and two high-column products. `pair_low_mod64` connects the current low word
to the unbounded value modulo `2^64`; the existing 64-bit shift theorem
establishes its quotient. Intermediate sums fit in 128 bits under the
implementation limb bounds. The shifted `c` is below `2^63`, shifted `d`
below `2^50`, and stored `r[2]` below `2^52`. Exact values and bounds are
derived, not extra execution premises.

## Evidence and scope

This remains partial helper execution, not complete jet equivalence; coverage
added is zero. Remaining final reduction/output stores, field-product bridge,
function entry and public reader/writer/lifecycle composition remain open.
The caller must still establish the implementation limb bounds. No production
C, original specification, API, generation setting, main proof source or
registry is changed.

Next: use the returned checkpoint for the final original slice, beginning at
head 97. The inspected spine has 107 heads, followed by `mul_last`. Its
remaining operations include `c += (R << 12) * low(d)`, `c += t3`, the `r[3]`
store and shift, and the final `r[4]` addition. Prove that word accumulation
and last addition fit their carriers; do not silently identify machine sums
with unbounded sums. Compose with `after_fifth`, retaining all earlier output
loads and the real function's local-allocation/free obligations.
