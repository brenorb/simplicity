# Original scalar-add helper checkpoint

Seven modules / 37 results prove actual execution of the unchanged in-place
`f_secp256k1_scalar_add`, including its uint128 allocation/free, exact return
flag, four output limbs, both caller-owned 32-byte scalars and outside-memory
load/permission preservation. The carry and original reduction expressions
give the sum modulo the group order when the input sum is in `[0, 2*N)`.

This is **internal helper support**, not a public scalar-add equivalence,
coverage registration or full acceptance. The two actual scalar readers must
establish that sum bound, and their outputs must be connected to the literal
Simplicity add/carry-expansion/normalize512 program. The public caller's
entry/source-copy, writer, return and freeing remain to be proved.

All seven final sources compiled. Independent kernel recheck **65848** ended
with exit **0**. All 37 types and 29 non-tree definitions are untruncated;
exact per-result dependencies are 34 closed, one storage result with four
inherited classical dependencies, and two execution results with those plus
CompCert external/inline-assembly semantics. The 15-axiom kernel context is
exactly the accepted baseline context; all three unsafe categories are empty.
No new axioms, execution/output/free premises, admissions or unchecked proof
tactics are introduced. Scope remains original LP64 RECKLESS/assertion-disabled.

The helper execution tree contains an original assertion-disabled conditional
whose two branches have identical states. `scalar_add_selected` formally
covers both branches; do not replace the original control flow or assume its
condition. The tree itself is diagnostic, backed by exact run/shape proofs.

Read-only review from the repository root:

The negative fixtures mutate evidence only in memory. Main shared registries,
other authors' changes, production C/Haskell and Claude's Elements reservation
remain untouched. Signed local commits only; no pushes.
