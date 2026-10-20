# Actual scalar multiplication body with a borrowed right-hand operand

This archive advances the real public `simplicity_scalar_multiply_lambda`
proof. That jet calls `scalar_mul(&a,&a,&secp256k1_const_lambda)`; the generated
global has `gvar_readonly = true`. The previous two-owned-scalar contract cannot
be instantiated by asserting the static global Writable/Freeable. These four
modules require only a readable, initialized, non-owned second operand.

`eval_scalar_mul512_borrowed_product` derives the original C product call, all
eight actual output loads and the existing full 512-bit product value, from a
fresh uninitialized product buffer, one owned first operand and one readable
second operand. The symbolic run/output equalities and actual execution are
proved; neither old input ownership nor helper execution is assumed.

The actual product memory is transported into the already checked reduction
contract. `exec_scalar_mul_borrowed_body` derives the unchanged original
in-place `scalar_mul` body, exact product modulo group order, output ownership,
preserved second-operand region and outside-footprint framing. The reusable
`region_ok_lframe` lemma transfers initialized cells, permissions, valid-block
facts and ownership (when present) through an actual load/permission frame
contract. No arithmetic development or target specification is replaced.

This is an **internal product/reduction/body milestone**, not the whole
`scalar_mul` function or public lambda jet equivalence. Actual allocation,
entry/return/free, global initialization/value and the literal lambda term/
wrapper must still be proved. No registered jet, C source, accepted snapshot
or main index is changed. Scope remains LP64 / RECKLESS.

## Verification

There are **14 results** and **four definitions**: six results are closed;
four representation/preservation lemmas retain the inherited four classical/
extensionality dependencies; four execution results retain those plus the two
CompCert semantic parameters. No new axiom is added. The dependency-wide
kernel context has the inherited 15-axiom allowlist and all three unsafe
categories are empty. The untruncated type/definition report is 14,962 bytes.
Nineteen in-memory corruption fixtures pass.
