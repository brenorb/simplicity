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

Two sources, 12 results and three definitions. The expected exact profile is
seven closed results, one expression lemma with four inherited classical
dependencies, and four execution results with the six inherited Coq/CompCert
dependencies. `RUN.json` records fresh compilation and full contracts and
assumption reports; `CHECKED.json` additionally records completed recursive
kernel verification. A launch file alone is not success.

Audit tree `/private/tmp/jet-field-checkpoint-audit.Zeze9g`; sources in
`wrapper/` under namespace `FieldWrapper`. The checked parent binds 95
previously forcibly rebuilt local sources and 44 checked extension modules.
The wrapper loads 43 of those extensions: `FieldCall.Product`'s separate
endpoint is not imported here. All loaded non-standard modules require exact
source/object provenance.

```sh
python3 -B proof-work/secp-field-wrapper/verify.py compile \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
python3 -B proof-work/secp-field-wrapper/verify.py kernel \
  /private/tmp/jet-field-checkpoint-audit.Zeze9g
```

Next: compose the real public readers, this wrapper, and the original
normalization/serialization writer. `read_fe` reduces an out-of-range
256-bit input by calling `secp256k1_fe_normalize_var`; it does not reject that
input. `write_fe` also normalizes before encoding. Keep that full input
domain and establish the internal limb bounds from the readers rather than
assuming a new public-input restriction. The original public jet calls
`secp256k1_fe_mul(&a, &a, &b)`, exactly the layout proved here.
