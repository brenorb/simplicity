# hash_to_curve: open infinity-path equivalence question

Status: **source-review question, not a demonstrated public mismatch**.
No concrete 32-byte key, native wrong-result reproduction, or whole-public
Coq counterexample is available. Do not count this as a divergence proof.
Production code, specifications, APIs and generated ASTs remain unchanged.

## Exact sources inspected

Revision: `868c91b53ab2ddc5b03bf170a6cd7608168a4e00`, with the frozen
production/specification/generation inputs unchanged.

- `C/jets-secp256k1.c:705--715`: the public function reads the key, rejects
  only a false generator-generate result, then loads/writes the generator
  and returns true. `write_ge` at lines 77--80 writes X and Y only.
- `C/secp256k1/generator_impl.h:205--253`: with NULL blinding, `ret` starts
  at 1 and is ANDed with the two `fe_set_b32` results. After the second SWU
  call the code adds the points, converts to affine, saves the generator and
  returns `ret`, without separately rejecting an infinity sum.
- The same file, lines 50--55: `generator_save` has a `VERIFY_CHECK` against
  infinity, followed by coordinate normalization and byte serialization.
  In the frozen `Coq/C/jets_secp.v` function
  `f_secp256k1_generator_save` (line 199885), that check is a loop evaluating
  `ge_is_infinity` once and then breaking, not a rejection branch.
- `C/secp256k1/group_impl.h:97--109,187--191`: the affine conversion's
  infinity branch calls `ge_set_infinity`, setting the flag and clearing X/Y.
- `Haskell/Core/Simplicity/Programs/LibSecp256k1.hs:729--742,836--837`:
  `hash_to_curve_core` checks both digests against p, adds their SWU points
  and then uses `gej_normalize`; `hash_to_curve` asserts that result.
  `gej_normalize` at lines 554--555 returns the failure alternative for Z=0.

## Is versus required equivalence

The specification's accepted-digest path still has a final possible failure
at normalization of an infinity sum. C's explicit success flag depends only
on digest representability, not on a separate infinity test of the sum.

To prove the public implementations equivalent, establish either that this
state is unreachable for the actual two SHA computations on every key, or
that the apparent discrepancy is resolved by another proved property of the
actual caller. Neither obligation is discharged by the current loader proof.

If both digests are below p and their mapped points sum to infinity, the
source-level C path would clear the affine coordinates, serialize/load them,
write the zero coordinate pair and return true, while the specification
would fail. That entire conditional path is **not yet a composed formal
execution theorem**, and its reachability from an actual public key is not
established. The verified loader/write theorem alone cannot establish it.

## Evidence and reproduction limits

The later theorem
`C.jet_secp_generator_affine_roundtrip.eval_generator_infinite_affine_roundtrip`
formally composes the actual affine conversion, generator save, generator load
and affine writer calls from an owned projective object with a nonzero infinity
flag. It derives the encoded coordinate pair; the closed lemma
`generator_infinite_output_zero` identifies both coordinates as zero.
No CTZ or libc behavior is assumed for this branch. Build
`JET_TARGETS=C/jet_secp_generator_affine_roundtrip.vo bash Coq/build-jets.sh -j1`
and recursively kernel-check
`bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_generator_affine_roundtrip`.
This closes the conversion/serialization call sequence, not the preceding
hashes, point addition, actual generator/public return statements or common-key
reachability. The whole-public conditional path and a public counterexample
remain unproved; the status above is unchanged.

Reproduce the source inspection, without modifying or mocking SHA:

```sh
sed -n '697,715p' C/jets-secp256k1.c
sed -n '40,56p;205,259p' C/secp256k1/generator_impl.h
sed -n '97,109p;187,191p' C/secp256k1/group_impl.h
sed -n '199885,199916p' Coq/C/jets_secp.v
sed -n '550,556p;729,742p;833,837p' Haskell/Core/Simplicity/Programs/LibSecp256k1.hs
python3 Coq/check-jet-source-target.py
```

Arbitrary opposite intermediate points are not a public input witness.
Replacing SHA, choosing independent digest outputs, or assuming that such
outputs have a common-key preimage would not reproduce the frozen public
jet. No such substitution, reachability axiom or narrowed input domain has
been added to a proof. No C fix or specification fix is proposed/applied here.

Worst case **if reachable**: the public jet could report success with a
coordinate pair where its Simplicity specification fails. No exploit,
transaction effect, likelihood or consensus impact has been established.
Keep `simplicity_hash_to_curve` unresolved while proving independent stages.
