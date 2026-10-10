# Combined isolated point-jet assembly

Update: checkout acceptance **86431 exited 0** on unchanged fingerprint
`16594c779a885f405041d02315d3cbaec414f439dc78c3d219dde3a8b425f631`.
The candidate's first build **2296 exited 2** because the shell selected Rocq
9.3 against Coq 8.17 dependencies; its diagnostic log is retained at
`/tmp/jet-predicate-accept.EX7adj/combined-build.log`. This is not a proof failure
or a reason to alter proofs/toolchain. A pinned Coq 8.17.1 serial build was
then launched with stack limit 65520 KiB; its handle is recorded in the latest
gej-negate continuation and its log is `combined-build-coq817.log` at the
candidate root. Poll that handle, not a replacement build. Standard snapshots
and full acceptance below remain pending, and coverage is still provisional.

Candidate `/tmp/jet-predicate-accept.EX7adj` is based on the accepted field-add
candidate `/tmp/jet-add-accept.qwqWy1`, not the older infinity assembly. This
preserves newer field-add support and all its reviewed proof/metadata records.
It includes the 20 infinity and 22 predicate modules, their four supplemental
source gate/test scripts, 133 additional audited results and 43 additional
transparent definitions. No production C/Haskell source changes are made.

`ASSEMBLY.json` records exact source/archive hashes and baseline/candidate
hashes for all eight edited metadata/infrastructure files. The archived
`assembly-infrastructure.patch` reproduces these edits; reverse application
check against the candidate passes. Existing expected contract/assumption
snapshots are deliberately still the accepted field-add baseline. They must
be generated and reviewed for the combined candidate before acceptance.

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
