# Consolidated proof candidates

All useful work identified during the 2026-10-06 consolidation is now versioned
on `feat/jet-equivalence`. Accepted Coq sources remain in `Coq/`; pending changes
and complete helper/review sources are preserved here, outside its build and
load paths. This archive does not increase the accepted inventory or complete
the inherited fidelity review.

| Work | Preserved form | Status |
| --- | --- | --- |
| Frame range correction | 20 original commit patches; 19 unintegrated corrections and one already accepted endpoint fix | Consumer build and full acceptance remain open |
| Field odd/zero predicates | Exact candidate patch, 18 modules, two source checkers, pending registration/snapshots | Candidate acceptance and inherited-review priorities remain open |
| Scalar/uint128 | 22 complete helper sources and one historical literal-source checker | Public canonical and lifecycle chains incomplete; four sources need fresh verification |
| SHA initialization/preservation | One complete source with 16 results | Kernel/contract review and consuming public chains remain open |
| Review witnesses | 19 exact sources | Scoped diagnostic/review evidence; some require earlier contract revisions |

Each group has a manifest with source hashes, revision dependencies and remaining
obligations. The `.source` extension prevents accidental compilation or coverage
registration. The manifests distinguish historical checks from fresh acceptance.
The old candidate histories are also retained in the fork as
`codex/frame-range-contract` and `codex/secp-field-predicates`.

Run the archive integrity and exact patch replay check from the repository root:

```sh
python3 proof-work/manage.py
```

It checks source hashes and reconstructs every range commit and the field
predicate candidate in a temporary Git index. The resulting tree IDs must match
the recorded commits. It does not compile or accept those proofs, change the
active sources, or apply candidate snapshot changes to the active build.

To recover exact helper sources for further work outside the repository:

```sh
python3 proof-work/manage.py --extract scalar-u128 --output /tmp/simplicity-scalar-candidate
```

The output must be new and outside this repository. Resolve the manifest's
namespace and revision dependencies before compilation. Range and field patches
can be applied, in recorded order, to an external checkout of their respective
`base_commit`; all bases remain reachable from the fork's main topic branch.

`scratch-inventory.json` accounts for all 84 former scratch sources: 16 are
already integrated, 18 are in the field predicate patch, 42 are exact archived
helper/review sources, and eight are superseded incomplete goal diagnostics
retained locally. The latter have no new closed-prefix declaration names beyond
the integrated/archived sources. Generated artifacts, caches and raw logs remain
local. The inherited fidelity review remains **partial**; consult
`Coq/C/JET_INHERITED_REVIEW.md` for its separate obligations.
