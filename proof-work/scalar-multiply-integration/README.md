# Normal scalar-multiply integration candidate

The checked public scalar-multiply proof and its selected dependency closure
now build in the normal `C` namespace. Candidate:
`/tmp/jet-scalar-multiply-integration.yIS07H/Coq`.
Parent: immutable accepted scalar-add candidate
`/tmp/jet-scalar-add-integration.RxsuOy/Coq` (359/533).
Main's unrelated dirty files and registries are untouched.

`ASSEMBLY.json` pins 69 new modules, 359 results and 279 definitions. Only
one public jet is selected; the helpers do not count as jets. Namespace
transport is exact, with shared readers/writer reused from the parent rather
than duplicated. An inherited two-reader audit footer is retained in its
existing normal module; it changes no proof declaration.

Fresh normal build and independent root/dependency kernel checking passed.
The kernel has the inherited 15-axiom context, with all unsafe categories
empty. Every new theorem's dependency set matches its checked scratch
counterpart (292 closed results). The complete non-tree deep contract report
is untruncated (676,351 bytes). The 6,596 inherited contract records are
byte-identical, as are all inherited proof sources; 4,408 inherited assumption
records are retained unchanged. `NORMAL-REVIEW.json` records exact comparisons
and supplements compact printer ellipses with the deep report. Three large
execution-tree prints are diagnostic only; their source/shape/soundness proofs
and kernel checking, not abbreviated Print output, establish execution.

Seven new internal u128 definition names coincide with old core definitions.
The contract driver loads `C.jet_secp_umul128_exec` without opening it, while
checking/printing all its qualified names. This preserves inherited printing
context and omits no checks. Coq also prints the entire parent declaration
for constructors `wcolumn`, `Wmul` and `Wsum`. The snapshot parser handles
exactly these three checked cases, preserving ordered duplicate records and
requiring the constructor in the parent print. It does not relax arbitrary
declaration mismatches. Eleven in-memory corruption fixtures test the parser;
five more reject weakened/wrong public boundary contracts.

The candidate's provisional coverage is **360/533**, not accepted coverage.
Full `check-jets.sh --accept` is running as session **38093**, with build and
static gates passed and whole-registry kernel checking underway at the last
verified observation. `AUDIT-RUN.json` is a launch record, not success.
No candidate source, registry, script, specification or expected snapshot may
be edited while it runs. Do not restart a live job on an observation timeout.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-multiply-integration/review-normal.py --assembly proof-work/scalar-multiply-integration/ASSEMBLY.json
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-multiply-integration/test-review.py proof-work/scalar-multiply-integration/ASSEMBLY.json
PYTHONDONTWRITEBYTECODE=1 python3 proof-work/scalar-multiply-integration/test-multiply-public.py /Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity /tmp/jet-scalar-multiply-integration.yIS07H/Coq
```

These are read-only preparation checks. Only the separate complete acceptance
run can accept the reviewed snapshots and four regenerated ASTs. The earlier
`--update` contract-generation operation prepared a candidate snapshot;
it was not acceptance. Assumptions were prepared by exact checked extension,
and the full acceptance command uses no update/no-build flags.

Source proof scope remains public local frames / LP64 / RECKLESS, against the
literal canonical Simplicity term. Evaluator/all-frame integration and other
assertion configurations are not newly claimed. See `CONTINUATION.md`.
`MAIN-RECONCILIATION.md` and the read-only `plan-main.py` record the current
main overlap checks without installing or accepting anything; recompute before
application. The planner reuses the exact constructor-aware snapshot parser.
Signed atomic local commits only; never push.
