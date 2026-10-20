# Original field multiplier: complete body and product modulo the field prime

`exec_original_field_body_product` executes the **complete unchanged body**
of `f_secp256k1_fe_mul_inner`. It composes the checked first 97 statement
heads with every remaining original statement, including both last output
stores and `mul_last`. It establishes all five current-memory output loads,
an updated checkpoint representation and outside-original-footprint framing.

The final word accumulation is related to multiplication by one, reusing the
existing proved 128-bit accumulation rather than assuming a new arithmetic
model. Derived bounds prove that neither that accumulation nor the last
64-bit addition wraps. The first four output limbs are below `2^52`; the
last is below `2^49`. The cached original inputs remain distinct from the
overwritten output array throughout the actual execution.

`Product.v.source` connects those **actual C output words** to the checked
integer carry/reduction conservation theorem. The input convolution is
proved to be the product of the two radix-`2^52` inputs. Consequently the
five stored words represent that product modulo `2^256 - 4294968273`.
Intermediate values, no-overflow facts and this congruence are derived from
the implementation limb bounds, not assumed as execution premises.

## Boundary: not yet a public jet equivalence

This result starts with the existing `prefix_initial` representation of the
input arrays **and already-allocated local c/d objects**, plus its live
temporary and local-environment relations. It is a complete **body** theorem,
not yet a complete `eval_funcall` theorem. Actual function entry/local
allocation and final local freeing still need composition. The public
jet's reader, normalization, writer/lifecycle and literal Simplicity
specification bridge also remain open, including establishing these limb
bounds from every legitimate public input. Coverage added: zero.

No production C, original specification, API, generation setting, main proof
source or registry is changed. The exact in-place internal layout `r = a`
is inherited from the earlier original-C execution packets.

## Verification

The product bridge keeps intermediate algebraic models named and uses
explicit rewrite instances. Unfolding all stages at once caused a bounded
conversion timeout; factoring `fifth_d_model`/`first_t3_model` and rewriting
through the named checkpoints closed it without increasing the budget.

Next: compose real function entry/allocation and local freeing around this
body theorem, retaining the five final output loads and product congruence.
Then transport it through the actual field wrapper and public jet call chain,
using the original normalization/serialization specification. Do not replace
the caller's input domain or require its output/product correctness as a
premise. The previous full symbolic function-call proof in `secp-field-mul-exec`
is useful execution infrastructure, but its large output expressions do not
by themselves discharge these new value/representation obligations.
