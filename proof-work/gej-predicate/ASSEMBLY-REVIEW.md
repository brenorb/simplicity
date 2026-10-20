# Combined isolated point-jet assembly

## Current verification (supersedes historical live-session notes below)

Pinned combined build 86191 exited 0. Generated full standard snapshots are
now reviewed by `review-combined-snapshots.py`: removing exactly the 133 added
type and 43 definition records recovers the inherited contracts byte-for-byte.
All 3733 inherited assumption records are identical. Every added assumption
record matches its earlier per-result report. Preliminary contract comparisons
cover all 176 added records with explicit printed-global qualification
normalization; two computed infinity writer definitions additionally use deep
ellipsis supplements. These diagnostics are not equality certificates for
omitted terms. Exact archived source and kernel evidence remain required.
The receipt stores the two generated snapshot hashes and says full acceptance
is false. Generation's vanished process handle is not an exit-status receipt.

Source recheck: all 46 added proof/checker files match exact archives and all
847 inherited Coq source modules match the accepted field-add baseline.
An initial recheck guessed checker files at the Coq root and failed before
finishing; resolving their actual `infinity-review`/`predicate-review` paths
passed the complete check. This was a path-check issue, not altered inputs.

Completed checks (terminal exit 0 unless explicitly described otherwise):

- Baseline fingerprint recomputes exactly as its accepted receipt:
  `c4e91d0d6bbfb9d88fd63c40a802b5e052ecb8df2d54e51ec9b8a49e074b607d`.
- All 46 newly materialized proof/checker sources match their archive hashes.
  Every inherited `.v` source is byte-identical to the accepted baseline.
- Public-result, definition and coverage inventories preserve the entire
  baseline text/rows. New rows are unique and disjoint from old rows.
  Counts: 3733 -> 3866 results, 1878 -> 1921 definition rows, 351 -> 353
  coverage entries. Two duplicate definition rows already present in the
  baseline are preserved, not silently removed or newly introduced.
- Production/canonical source/configuration gate passes on 240 files; static
  proof scanner passes. Both source correspondence gates pass, with all 38
  infinity and 37 predicate mutations rejected.
- Coverage inventory reports all 533 declarations, 353 candidate entries,
  249 without an extra library premise and 104 conditional on `memcpy_model`.
  This is provisional metadata, not accepted proof coverage.
- Coverage tests **67158 pass**, including eight added point-contract
  rejections: helper/wrong original function, wrong contract kind and false
  premise for each jet. Initial run exposed a test-local variable collision
  with the saved coverage manifest; the point loop now uses `point_original`.
  The correction was made only in the isolated test, with no proof weakening.

Current assembly fingerprint (before snapshot generation):
`84ff4885f14275ca23384e16996688260d9fa8cfd773c1e4e65afb0dbcafac2d`.
Do not confuse this with a full acceptance fingerprint.

Next, after the live checkout run 86431 reaches a terminal state:

1. Build the new candidate sources using the pinned Coq 8.17.1 toolchain,
   normal project load paths and original tactic limits. No scratch overlay
   should supply the final isolated modules.
2. Generate full standard contract/assumption snapshots in this isolated
   candidate. Review exact unchanged field-add baseline records plus both
   new theorem/definition groups. Use actual per-result reports, the existing
   infinity snapshot receipt and predicate deep supplements; do not paste
   standalone prints into a full snapshot and call that generation.
3. Run `JOBS=1 bash check-jets.sh --accept` without update/no-build flags,
   including both source gates/tests and all inherited gates/four AST checks.
4. Reconcile with the actual checkout using exact-source/metadata guards.
   Do not overwrite newer dirty/staged work or install old infinity metadata
   wholesale. Actual checkout proof registration remains unchanged at 351.

The checkout's ongoing acceptance inputs remain untouched. No new whole
build was launched concurrently, and neither point jet is counted as accepted
from this assembly. Kernel-checked candidate proofs and preliminary reports
remain evidence of progress, not completion of the every-jet goal.
