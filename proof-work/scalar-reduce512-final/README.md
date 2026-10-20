# Complete original scalar_reduce_512 helper

This is checked internal-helper progress, **not public jet acceptance**.
The eight archived sources prove the unchanged LP64 RECKLESS Clight
`f_secp256k1_scalar_reduce_512` helper computes its original eight-limb
input modulo the canonical group order.

The root `eval_reduce512_numeric_owned_loads` has only the original owned
input/output representation as a premise. It proves actual function entry,
argument binding, all 15 original local allocations, the whole original body,
return and freeing locals, representation after cleanup, current-memory
output loads, the numeric output identity and preservation outside caller
regions. No execution, store, free or output premise is assumed.

## Checked boundary

42 results and 26 definitions in eight modules. 34 results are closed.
Four representation results inherit the existing four classical/extensionality
dependencies; four execution results also inherit CompCert external-function
and inline-assembly semantics (six dependencies total). No new axiom was added.
The independent kernel check reports the inherited 15-axiom library context
with no unsafe type-in-type, fixpoint or positivity categories.

The reviewer recursively checks earlier prerequisites, including the dependency
fingerprint. Ten in-memory negative fixtures reject nonterminal checks, false
coverage, source/contract/dependency/unsafe-kernel and classification drift.

## Reproduce

Rebuild the archived modules in manifest order before consumers after any
source edit; these commands alone do not regenerate prerequisites.

## Scope still open

This helper is not the public scalar multiplication or square jet. Compose the
actual product/reduction caller, then public frame readers, normalization,
writers and cleanup with the **literal canonical Simplicity program**.
Broader evaluator-frame and other jet proofs remain required.
