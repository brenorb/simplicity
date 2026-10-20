# Original field multiplication wrapper

`eval_original_field_mul_wrapper_product` proves the actual unchanged
`secp256k1_fe_mul` function call on the two owned input fields, with the real
in-place arguments `r = a`. Its body is exactly the original `Scall` of
`secp256k1_fe_mul_inner`, not a replacement body or model implementation.

The proof checks the generated field composite and its `_n` array offset,
evaluates the actual struct-field arguments, and resolves the real inner
function through `secp_ge`. No hardcoded symbol block number is used. It then
instantiates the previously proved inner-call theorem and reusable void-call
lifecycle lemma. The final theorem has **no inner-execution premise**:
execution, current output loads, limb bounds, product modulo the field prime
and outside-input-array framing are all proved.

The model remains the starting revision's assertion-disabled configuration.
No production C, original specification, API, generation setting, main proof
source or registry is changed. This is an internal field helper result, not
the public `simplicity_fe_multiply` jet's literal Simplicity equivalence.
Coverage added: zero. The implementation limb bounds remain explicit until
the public reader establishes them for every legitimate input.

## Verification

Next: compose the real public readers, this wrapper, and the original
normalization/serialization writer. `read_fe` reduces an out-of-range
256-bit input by calling `secp256k1_fe_normalize_var`; it does not reject that
input. `write_fe` also normalizes before encoding. Keep that full input
domain and establish the internal limb bounds from the readers rather than
assuming a new public-input restriction. The original public jet calls
`secp256k1_fe_mul(&a, &a, &b)`, exactly the layout proved here.
