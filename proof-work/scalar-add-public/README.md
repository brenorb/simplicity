# Original scalar-add public equivalence checkpoint

The actual unchanged `f_simplicity_scalar_add` now has a compiled,
independently kernel-checked local contract against the literal canonical
Simplicity program:

```coq
secp_jet_local_spec f_simplicity_scalar_add
  (Ty.Prod (Word 8) (Word 8)) (Word 8)
  (@canonical_scalar_add Alg.CoreFunSem)
```

This closes the public boundary left by the three earlier scalar-add archives.
It derives actual 16-byte source / two 32-byte scalar allocations, the
by-value source copy, both original readers, in-place original scalar addition
(with its discarded int result), original serialization, the true public
return, and all three actual frees. Exact output, destination prefix/cursor
updates and permitted external-memory framing follow from the existing
transparent local contract. No intermediate calls, output, storage or
successful freeing are assumed by the public theorem.

## Checked evidence

Exact per-result dependencies: seven closed, one with four inherited
classical dependencies, eleven with those plus CompCert external/inline
assembly semantics. The inherited 15-axiom library context is unchanged;
all unsafe kernel categories are empty. No new axiom, admission or unchecked
tactic was introduced. This is not an axiom-free-Coq claim.

The literal gate rechecks the Haskell ScalarAdd dispatch/type/program and
the recursively reused add/carry/padding/scalar-modulo ports. It pins the
original AST, global linkage, local predicate and lifecycle adapters.
Five public-boundary and ten existing literal-wiring mutations are rejected;
ten independent evidence mutations test the source/driver/type/dependency/
kernel guard. These checks supplement the kernel, not a formal Haskell
compiler equivalence.

## Scope and status

Scope remains inherited local frames / LP64 / RECKLESS (assertions disabled),
not all evaluator frames or assertion-enabled execution. The all-533 goal is
active and unfinished. Claude owns Elements/shared obligations; no overlap,
no registry changes here, no production C/Haskell changes, no remote pushes.

## Reproduce

From the main checkout:
