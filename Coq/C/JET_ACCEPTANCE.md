# Latest repository consolidation acceptance

The scoped endpoint correction is accepted with exit 0, observed
2026-10-06 18:58:55 UTC.
The inherited fidelity review remains **partially complete**. No new jet is
registered. Build, 583 kernel modules, 3,534 assumption records, reviewed
contracts, negative tests and four AST comparisons pass.

Audited and integrated input SHA-256: `c92e9fba3f64de4713a8fcb317f9982f07f85afd162ee892af7e740d5679280c`.
See `JET_CONSOLIDATION_2026-10-06.md` and its JSON for the precise source
comparison, retained local artifacts and deferred range/secp candidates.
The prior acceptance record below is historical. Its old temporary original
consolidation log is unavailable; published Git receipts preserve that history.

# Prior consolidation acceptance record

Verification status: **accepted**, observed 2026-10-06 01:00:50 UTC.
Inherited-work fidelity review: **partially complete**. See
`JET_INHERITED_REVIEW.md` for the eight-criterion assessment. This receipt does
not certify an exhaustive individual canonical review of every registered jet.
`check-jets.sh --accept` completes with **exit 0**, without snapshot updates.
Build, all 583 kernel modules, all 3,534 assumption records, reviewed public
contracts/definitions, negative tests and all four AST regenerations pass.

Final audited input SHA-256:
`5d01956807ea2f325ca099e65818f5e23d521e31ac994863c1f5fd09deeb6eae`.

This supersedes the published receipt at `5c2958d5` (346 entries), whose
acceptance hash was `a566e6bfc17b188b9377c0993284b555f6364e56f8c17801833d4b0e203572b6`.
The original consolidation and subsequent continuation evidence below is
preserved as historical review; the current coverage includes the field jet
accepted in this round.

## Scope

The common base is `ebf1749340f623be7e0e43a1a6b3a7cccf560e2e`. The experimental
branch tip is `76923ec0`, contributing 101 commits and 126 added files. The
integration preserves that history and the original `feat/jet-equivalence`
branch. Publication is scoped to `brenorb/simplicity:feat/jet-equivalence`.

The production C/canonical Haskell target is
`e3b670103101108faa238df012676ff5d8b77cf9`; generation remains the pinned
x86-64/Linux LP64 configuration in `JET_TARGET.md`. The implementation change
introduced in `b058d5a6` is reversed. No replacement helper or external-call
substitution is used.

## Original-target correction review

- All 2,016 surviving old public assumption records are unchanged.
- Four obsolete `copyWords` execution/linkage records are removed; byte-copy
  memory support is preserved.
- 1,315 newly registered public results bring the inventory to 3,331; 1,683
  are closed under the global context. No new axiom name is introduced.
- Changed existing theorem/lemma statements comprise 92 restored final libc
  premises, 12 helper premises and five genuine external-call adaptations.
  Their output and memory conclusions are preserved.
- Bitcoin record/value semantics now permit the full Word64 domain, modular
  totals, positive fees and zero outputs. LockTime uses canonical `lockTime`.
- Raw input data, serialization and independently computed hashes are related
  to the cached C representations. Seven existing coverage rows use these raw
  contracts. The C constructor's supplied txid is an explicit representation
  boundary; no verified serializer in that constructor is claimed.

The candidate full audit, with a 65,520 KiB native stack, passes with exit 0:
`/tmp/jet-bitcoin-raw-candidate-stack64-audit.log`. The default macOS stack caused
a recorded earlier failure; the script now raises the soft limit without
disabling kernel checks. The final run uses `check-jets.sh --accept`, with no
snapshot update flags. Its original consolidation log is `/tmp/jet-consolidation-final-accept.log`.

## Previously accepted canonical continuation

The continuation preserves all 3,331 existing assumption records and every
existing printed type/definition byte-for-byte. Three annex results and five
newly frozen definitions bring the inventory to 3,334 (1,683 closed), without
a new axiom name or library-level axiom. The raw annex semantics retain the
nested missing-input/absent-annex distinction.

Source review justifies 27 additional final registrations: twelve original-C
64-bit full shifts, conditional on libc, and fifteen Bitcoin contracts (raw
tappath/annex, modular totals/fee and TimeLock). The full_shift catalog dispatcher
and recursive literal programs match the concrete Coq specializations; a new
negative-tested gate checks all 36 bindings. The four TimeLock assertions retain
the entire success/failure/output/framing contract over the precise linked
program and logical environment. No execution/output premise is added.

The candidate run `/tmp/jet-next-canonical-candidate.log` passes with exit 0.
Its snapshot-excluding input hash is
`fe314944ebc695177ae320275b540ba5b8611b06092f9ce50e8528c78903488c`.
After actual snapshot review, the separate final run
`/tmp/jet-next-canonical-final-accept.log` passes `--accept` with exit 0.
Its hash `a566e6bfc17b188b9377c0993284b555f6364e56f8c17801833d4b0e203572b6`
includes the reviewed snapshots; both hashes describe unchanged inputs within
their respective modes. Build, kernel, assumptions, contract
comparisons, negative fixtures and all four original-source AST checks pass.

## Original fe_normalize accepted against its canonical program

The 16 new proof modules contribute 200 audited results: 199 support results
and the complete `fe_normalize_local_spec` jet contract. All 3,334 previous
assumption records and every previous printed type/definition are unchanged.
There are 151 new closed results, bringing the total to 1,834. The remaining
new results retain only inherited Coq/CompCert assumptions; no axiom name or
library-level axiom is added.

The canonical port preserves the pinned Haskell subtraction, projections and
conditional at the complete Word256 domain. The real C reader derives the
big-endian bytes, limb values and normalization branches from the input frame;
the writer derives its real calls and the encoded canonical output. The public
proof derives local allocation, the actual by-value source-frame copy, helper
execution, return and freeing from the initial memory contract. Its output,
prefix, cursor and outside-memory conclusions are the complete common jet
contract, with the original secp linked environment as the sole change. It does
not assume a helper execution, output, or final freeing fact, and has no extra
`memcpy_model` premise.

The source correspondence gate rejects 11 mutations. The metadata gate rejects
added impossible premises, weaker conclusions and unrelated secp functions.
Actual definition/type/axiom snapshot diffs were reviewed after the candidate
run `/tmp/jet-secp-normalize-candidate-audit.log` (exit 0, snapshot-excluding
hash `cfa390055b3d83d986af7ed5541003219351a873d84acc4225a6fcd449fe4176`).
The separate final run `/tmp/jet-secp-normalize-final-accept.log` completes with
exit 0 without update flags, using the snapshot-inclusive hash above. All four
ASTs are independently regenerated from the unchanged original C inputs.

## Conservative coverage and limits

| Surface | Without an extra libc premise | Conditional on libc | Unregistered | Declared |
| --- | ---: | ---: | ---: | ---: |
| Core | 207 | 104 | 59 | 370 |
| Bitcoin | 36 | 0 | 24 | 60 |
| Elements | 0 | 0 | 103 | 103 |
| Total | 243 | 104 | 186 | 533 |

The denominator is the public header surface; it includes two secp declarations
without primitive jet-node registrations. The 104 conditional proofs leave the
actual linked libc implementation outside the proof. The 243 other entries
still have their stated initial frame/environment representation contracts and
inherited Coq/CompCert assumptions.

Symbolic execution, interval analysis and byte/limb conversion remain support.
Only the complete canonical `fe_normalize` contract adds a jet equivalence in
this round; individual normalizer or conversion lemmas add no coverage.
Experimental SHA/Bitcoin contracts needing startup-global preservation or canonical raw-data
bridges remain outside this coverage registry. The full every-jet goal remains
unfinished; the specific obligations are in `JET_FIDELITY_REVIEW.md`.

Native C correctness tests pass: 96 successes, zero failures
(`/tmp/jet-original-c-native-tests.log`). This native macOS run is additional
regression evidence, not a test of every x86-64/Linux build configuration.
The two modified Nix expressions parse successfully; a Nix build and remote CI
have not been run as part of this local acceptance.

Further SHA startup preservation and two complete canonical field predicate
proofs (`fe_is_odd` and `fe_is_zero`) are developed in an isolated scratch
directory. The two predicates have compilation, kernel and statement/assumption
review receipts, but are outside this acceptance and add no registered coverage.
Scalar canonical and helper proofs are likewise isolated support. Their actual
remaining links are recorded in `JET_PROGRESS.md`.
