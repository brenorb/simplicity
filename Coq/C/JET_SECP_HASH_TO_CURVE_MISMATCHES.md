# hash_to_curve: open infinity-path equivalence question

**Current status (2026-11-01, latest):** **reported predicate mismatch**
(not corrected) and **conditional coverage**. C does not reject a key whose
two SWU points sum to infinity; the specification fails there. The jet is
counted as proved *conditional on* the open SHA-256-dependent property
`hash_to_curve_accepted_finite`, a visible premise of its public theorem
(never an axiom), with user approval on 2026-11-01. Coverage 533/533. See
"Mismatch report and conditional coverage" at the end.

Earlier on 2026-11-01: checked exact reduction in
`C.jet_secp_hash_to_curve_reduction` (see the dated section at the end). The
jet meets its frozen specification iff `hash_to_curve_accepted_finite`; that
property is open, so the jet was not counted then (coverage 530/533). The record
below is unchanged.

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

`C.jet_secp_generator_generate_body.exec_generator_generate_body` now composes
the entire original internal generator body from the represented key and owned
local storage, retaining the existing explicit memcpy and CTZ premises. It
derives the conjunction of the two digest acceptance flags as the actual return
value, identifies their canonical mapped point sum when both accept, relates
the actual sum infinity flag to the decoded Z zero test, and exposes the exact
saved bytes for either affine branch. The infinite branch exposes cleared
coordinate words. This closes the generator body, including its return; it
does not establish entry/free, the outer public execution, or common-key
reachability of an infinity sum. No public divergence is claimed. Build
`C/jet_secp_generator_generate_body.vo` and recursively kernel-check
`C.jet_secp_generator_generate_body` with the existing `build-jets.sh` tools.

`C.jet_secp_hashgen_outer.eval_hashgen_generate` now wraps that body in both
original generator functions: actual internal entry, all eleven allocations
and frees, return conversion, both outer pointer-check loops, NULL-blinding
call and outer return. Its audited `hashgen_result` retains the computed sum,
infinity flag and both affine/serialization branches; key and outside memory
are preserved. The existing explicit memcpy/CTZ premises remain. This closes
the generator-call lifecycle, not the public frame read/write/failure/free
composition or an actual key witnessing the suspected mismatch. Build
`C/jet_secp_hashgen_outer.vo` and recursively kernel-check
`C.jet_secp_hashgen_outer`; no new public divergence is claimed.

`C.jet_secp_hash_public_generate.hash_public_begin` additionally derives the
public entry with all four allocations, its actual by-value source-frame copy,
the raw 32-byte read and the original generator call. The represented input
is every Word256 key, without field normalization, alignment of the bit cursor,
or a digest-acceptance premise. It preserves caller memory and startup and
derives the computed return flag and `hashgen_result`. A separate free-list
lemma covers the four public locals. The public failure/success branch,
load/write/return and freeing still need composition; no whole-public mismatch
or new coverage is claimed. Reproduce with the normal build and recursive
kernel check of `C.jet_secp_hash_public_generate`, and the existing focused
assumption/contract audits of the three `jet_secp_hash_public_*` modules.

`C.jet_secp_hash_public_call.eval_hash_public_original` now closes the complete
original public C execution, including both return branches, original
generator load/affine write, result conversion and all four public frees.
It derives the digest-acceptance return value, output cells/cursor/prefix and
caller-memory frame. Its pure `hash_public_value` retains the canonical mapped
sum on accepted digests, actual sum infinity flag and finite/infinite affine
formulas after freeing local storage. No key, digest or infinity input is
excluded, and no input/output-disjointness premise is added. The established
memcpy/CTZ premises remain explicit. Reproduce with the normal build and
recursive kernel check of `C.jet_secp_hash_public_call` and the focused audits
of `jet_secp_hash_public_finish` and `jet_secp_hash_public_call`. The final
canonical assertion equivalence/common-key infinity reachability obligation
remains unresolved; this theorem adds neither public coverage nor a public
counterexample.

The generator-to-public result contracts now retain the numeric X/Y equalities
already derived by the original affine execution, without adding a premise
or dropping an earlier conclusion. In `jet_secp_hash_public_literal`,
`hash_public_finite_literal` identifies the finite output with the literal
normalization term, and `hash_public_core_result` gives the exact core
specification result for every computed public value: rejected digests yield
the failure tag; accepted finite sums yield the actual coordinate pair;
accepted infinite sums yield the failure tag. The checked composition
`literal_hash_to_curve_core` follows Haskell lines 729--742 and reuses the
existing verified components. This makes the outstanding assertion/infinity
boundary precise; it supplies neither a common-key infinity witness nor an
all-key proof that such a sum is impossible. The memcpy/CTZ premises of the
C execution remain explicit, and coverage is unchanged. Reproduce with the
normal build/kernel check of `C.jet_secp_hash_public_literal` and focused
audits of the strengthened generator/public modules and their consumers.

The outer assertion is now included in
`jet_secp_hash_to_curve_spec.literal_hash_to_curve`, with the original
Programs.Bit.assert structure and canonical pruned-branch commitment.
`jet_secp_hash_to_curve_compare.eval_hash_to_curve_compared` compares that
specification with the complete original public C call and its output/frame
observations on every represented key, retaining explicit memcpy/CTZ
premises. `hash_public_return_agreement_iff` gives an exact criterion: the
returns agree when the digests reject or the computed sum flag is zero; an
accepted infinite sum yields C success and specification failure. It does
not supply or assume a key producing that state. This is an all-case
comparison, not an exhibited public divergence or a proof excluding the
suspected case. No coverage is added. Reproduce using the normal build and
recursive kernel check of `C.jet_secp_hash_to_curve_compare` and focused
assumption/contract audits of the two `jet_secp_hash_to_curve_*` modules.

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

## Exact reduction in the standard public contract (2026-11-01)

`C/jet_secp_hash_to_curve_reduction.v` builds on
`eval_hash_to_curve_compared`, with the existing explicit `memcpy_model` and
`ctz_model` premises and no other premise beyond the six inherited
assumptions:

- `hash_ready` collects the startup state the call needs (SHA globals, SWU
  constants, both generator SHA prefix states, 8-byte dispatch-cell extent);
  `hash_ready_initial` proves it holds in the frozen program's initial memory,
  and `hash_to_curve_public_compared` proves it is preserved by the call.
- `hash_to_curve_public_compared`: for every represented 256-bit key, the
  original public call returns `cmov_int (hash_accepted key)` (both digests
  are field elements), and that return equals the specification's partial
  return **iff** `hash_accepted key = true ->
  literal_hash_to_curve key <> None`. On success the output cells are the
  specification's value; all other memory is framed.
- `hash_to_curve_initialized_local_spec_if_finite`: the standard
  `secp_jet_initialized_partial_local_spec` contract against
  `literal_hash_to_curve`, with `hash_to_curve_accepted_finite`
  (`forall key, hash_accepted key = true -> literal_hash_to_curve key <> None`)
  as an explicit hypothesis, not an axiom.
- `hash_to_curve_differs_if_infinite`: at any key with accepted digests and
  failing specification, the proved original call returns success (`1`) while
  the specification's partial return is failure (`0`).

`hash_to_curve_accepted_finite` says that no 256-bit key has two field-element
digests whose SWU points sum to infinity. That depends on the two SHA-256
digests of each key and is neither proved nor refuted here, so this is not an
equivalence or a divergence proof. `jet-coverage.py` lists it as an open
property reduction that does not count. The recursive kernel check of
`C.jet_secp_hash_to_curve_reduction` passed on the commit that added it.

## Mismatch report and conditional coverage (2026-11-01)

**Affected jet:** `simplicity_hash_to_curve` (secp256k1). Production C, the
Haskell specification, the Coq specification and generation settings are
unchanged; no correction is made here.

**Expected (specification):** `hash_to_curve = assert hash_to_curve_core`
(LibSecp256k1.hs:729--742,836--837) fails when either digest is not a field
element **or** the sum of the two SWU points is infinity (`gej_normalize`
returns the failure alternative for Z = 0).

**Implemented (C):** `generator_generate` (generator_impl.h:205--253) returns
the conjunction of the two digest acceptance flags only; an infinity sum is
converted, saved and written as the zero coordinate pair, and the public jet
returns success.

**Consequence, formally proved:**
`C.jet_secp_hash_to_curve_reduction.hash_to_curve_differs_if_infinite` shows
that at any key with two accepted digests and a failing specification, the
original public call returns success while the specification's return is
failure. `hash_return_agreement_iff` gives pointwise agreement exactly off
such keys. No such key is known: it requires the two SHA-256-derived points
to cancel, an event of probability about 2^-254 per key under a random-oracle
heuristic. There is **no native observation** of a divergence, and none is
claimed.

**Counted theorem** (`C/jet_secp_hash_to_curve_conditional.v`), stating every
premise in its type:

- `C.jet_secp_hash_to_curve_conditional.hash_to_curve_conditional_local_spec`:
  `memcpy_model -> ctz_model -> hash_to_curve_accepted_finite ->
  secp_jet_initialized_partial_local_spec hash_ready f_simplicity_hash_to_curve
  ... literal_hash_to_curve`, with `hash_ready_initial` deriving the startup
  state from `Genv.init_mem`.

The premise is specific: it is not collision resistance of SHA-256, but the
statement that no key with two accepted digests maps to cancelling points.
`jet-coverage.py` counts the entry as conditional on an open SHA-256 property,
separately from the library models, and requires the divergence theorem above
and this report. Resolving the mismatch (an infinity rejection in C, or
dropping the failure in the specification) is a target change that needs
separate approval.

Verification limits: the property is neither proved nor refuted; receipts are
valid only for the exact checked inputs. Reproduce from `Coq/`:

```sh
bash build-jets.sh --coqc C/jet_secp_hash_to_curve_conditional.v
ulimit -S -s 65520
bash build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_secp_hash_to_curve_conditional
python3 jet-coverage.py
```
