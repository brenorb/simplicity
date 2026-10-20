# Original field multiplier: real function call and output product

`eval_original_field_mul_inner_product` proves an actual
`Clight2.eval_funcall` of the unchanged `f_secp256k1_fe_mul_inner`. It starts
with only the two owned 40-byte input arrays, the implementation limb bounds
and the existing in-place argument layout `r = a`; **no preallocated local
objects, entry relation, body execution or freeing premise** is required.

The proof establishes real parameter binding, C local allocation, the
previously proved complete body, and the real final local freeing. Its final
caller-owned representation and all five output loads hold **after freeing**.
The five output limbs represent the input product modulo
`2^256 - 4294968273`, with the first four limbs below `2^52` and the last
below `2^49`. Framing outside the two caller-owned arrays is retained.

## Reusable lifecycle lemma

`owned_void_call` factors the executor's existing allocation/entry/freeing
argument around a supplied normal void-body contract. The concrete multiplier
instance discharges that contract using `exec_original_field_body`; it is
not an assumed C implementation or extra premise of the final theorem.
The proof retains the initial-memory validity guard while composing frames:
fresh stack blocks may change and be freed, but old caller blocks must not
be treated as fresh. The returned representation drops the freed local
regions, then derives the five current-memory output loads.

## Verification and remaining scope

This completes the internal in-place **function-call** product theorem, not a
public jet's literal Simplicity equivalence. Public reader/input-bound
establishment, field wrapper/normalization, writer and jet lifecycle/specification
composition remain open. No production C, original specification, API,
generation setting, main proof source or registry is changed. Coverage added:
zero.

Next: transport the call through the actual `secp256k1_fe_mul` wrapper, retain
the exact wide-limb representation and prove its normalization/serialization
bridge to the original field-jet specification. Reuse the new lifecycle lemma
for other void helpers once their own body contracts are genuinely proved.
Do not infer a new public-input restriction from these internal limb bounds;
establish them from the real readers for every legitimate public input.
