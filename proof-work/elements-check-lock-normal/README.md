# Five Elements timelock/assertion contracts under final C names

This combines the checked finality, lock-height/time and check-lock-height/time
proofs under their intended normal `C` namespaces. It supersedes the smaller
final-name preparation in `../elements-timelock-normal/` for the next admission
batch; that receipt remains a valid historical prerequisite.

Checked actual-C roots cover:

- `simplicity_tx_is_final`
- `simplicity_tx_lock_height`
- `simplicity_tx_lock_time`
- `simplicity_check_lock_height`
- `simplicity_check_lock_time`

Every target is its canonical Simplicity primitive/combinator program. The
check-lock contracts retain failure returns and memory framing on both
success and failure, not a success-only interpretation. None substitutes a
numeric predicate for a required C execution proof.

## Preparation evidence

Private tree: `/private/tmp/jet-elements-check-lock-normal.hoKRuj`.
The inherited Coq tree is an unchanged copy of the immutable checked
check-lock tree. No live audit-tree compiler outputs are copied. Two files
are added: `C/jet_application_partial_transport.v` and
`C/jet_elements_check_lock_literal.v`. The only textual edit to their checked
sources is the latter's helper import from `CheckLockReview` to `C`.

All twelve unregistered dependency/root modules were freshly compiled in
dependency order. Complete reports cover 77 helper/final result types and
40 definitions, without elision or unresolved placeholders. Assumption
reports additionally include the existing contract-transport reference.
All three pure source-program bridges remain axiom-free; every result retains
the same dependency set as its earlier checked source after namespace rebasing.
The generic partial-contract transport retains the six inherited dependencies
of its CompCert contract type, matching the previously checked transport; it
is not falsely classified as a closed pure theorem.

Recursive kernel checking of all three roots passed, with the unchanged
library context and no unsafe fixpoint/assumed-positivity categories. Exact
production Elements AST regeneration passed. The combined canonical-source
guard passed under final names, as did 25 assertion/failure tests, 31 finality
tests and 32 lock/constant tests (88 source mutations). The evidence reviewer
also rejects 23 in-memory scope/source/bridge/context/command/kernel/AST
corruptions. Invalid proof text is never compiled.

The review verifies all 1,580 inherited source/metadata/registry/guard files
are byte-identical, with exactly the two new proof sources added. Normal
manifests, coverage and snapshots retain the source baseline's content.
`PREPARATION.json` binds source and object identities, base receipts, command
lines, terminal statuses, reports, tools and the preserved original staging.
The two source archives and full contract/assumption/kernel/AST logs are
retained here. This is evidence for the actual dirty/staged source base, not
clean-HEAD reproducibility.

```sh
python3 -B proof-work/elements-check-lock-normal/review.py
python3 -B proof-work/elements-check-lock-normal/test-review.py
```

## Normal admission still required

Coverage added here is **zero**. Main's actual full sequence audit passed at
368/533. The independent direct-getter candidate proposes 371/533 and remains
subject to its own full acceptance; keep main unchanged for its terminal
source validation. Do not restart completed or live audits.

After that predecessor succeeds and is installed, assemble one reviewed
normal candidate for this five-jet family, reusing its twelve shared modules
and generic partial-contract transport. Register 77 results and 40 definitions
but add jet coverage only for the five actual-C canonical endpoints. Install
the finality, lock and check-lock source guards and negative suites as mandatory
checks. Preserve exact function, logical/linked environment, word widths,
representation, whole-contract shapes and absence of vacuous extra premises.

Use a scoped explicit-parameter printer rule for the newly registered modules;
do not change inherited records to absorb name-resolution drift. In particular,
consider loading the generic `C.jet_application_partial_transport` without
opening it, as is already done for the Elements modules. Review complete new
types/definitions, axiom sets and all inherited record preservation before
running full `check-jets.sh --accept` without update/skip flags. Only terminal
full acceptance and a guarded source-only installation can establish normal
admission. Preserve unrelated staged work and never copy compiler objects.

The original frame, cursor, output, prefix, environment and memory contracts
and LP64/RECKLESS build scope are unchanged. This preparation does not prove
environment-builder/evaluator composition or C assertion-enabled builds.
All other jets and the outstanding shared conditional-library/caller
obligations remain in the unchanged all-jet goal.
