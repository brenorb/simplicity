# Consolidation acceptance record

Status: **accepted**, observed 2026-10-05 21:05:19 UTC.
`check-jets.sh --accept` completes with **exit 0**, without snapshot updates.
Build, all 567 kernel modules, all 3,334 assumption records, reviewed public
contracts/definitions, negative tests and all four AST regenerations pass.

Final audited input SHA-256:
`a566e6bfc17b188b9377c0993284b555f6364e56f8c17801833d4b0e203572b6`.

This supersedes the published receipt at `61de9183` (319 entries), whose
acceptance hash was `6ab077ecd6bb173899701f63bfb966ee811e09618bc06df3879d8bc6ca4ee47f`.

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

## Reviewed continuation and final acceptance

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
Its hash above includes the reviewed snapshots; both hashes describe unchanged
inputs within their respective modes. Build, kernel, assumptions, contract
comparisons, negative fixtures and all four original-source AST checks pass.

## Conservative coverage and limits

| Surface | Without an extra libc premise | Conditional on libc | Unregistered | Declared |
| --- | ---: | ---: | ---: | ---: |
| Core | 206 | 104 | 60 | 370 |
| Bitcoin | 36 | 0 | 24 | 60 |
| Elements | 0 | 0 | 103 | 103 |
| Total | 242 | 104 | 187 | 533 |

The denominator is the public header surface; it includes two secp declarations
without primitive jet-node registrations. The 104 conditional proofs leave the
actual linked libc implementation outside the proof. The 242 other entries
still have their stated initial frame/environment representation contracts and
inherited Coq/CompCert assumptions.

Symbolic execution, interval analysis, byte/limb conversion and field
normalization are checked support, not additional jet equivalences. Experimental
SHA/Bitcoin contracts needing startup-global preservation or canonical raw-data
bridges remain outside this coverage registry. The full every-jet goal remains
unfinished; the specific obligations are in `JET_FIDELITY_REVIEW.md`.

Native C correctness tests pass: 96 successes, zero failures
(`/tmp/jet-original-c-native-tests.log`). This native macOS run is additional
regression evidence, not a test of every x86-64/Linux build configuration.
The two modified Nix expressions parse successfully; a Nix build and remote CI
have not been run as part of this local acceptance.

Further SHA startup preservation, canonical field normalization, byte/limb and
read_fe/write_fe execution proofs are developed in an isolated scratch
directory. Their compiled results are documented in `JET_PROGRESS.md`, but
are outside this acceptance round and do not add registered jet coverage.
