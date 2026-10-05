# Consolidation acceptance record

Status: **accepted**, observed 2026-10-05 19:33:58 UTC.
`check-jets.sh --accept` completes with **exit 0**, without snapshot updates.
Build, all 567 kernel modules, all 3,331 assumption records, reviewed public
contracts/definitions, negative tests and all four AST regenerations pass.

Final audited input SHA-256:
`6ab077ecd6bb173899701f63bfb966ee811e09618bc06df3879d8bc6ca4ee47f`.

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

## Reviewed snapshot differences

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
snapshot update flags. Its log is `/tmp/jet-consolidation-final-accept.log`.

## Conservative coverage and limits

| Surface | Without an extra libc premise | Conditional on libc | Unregistered | Declared |
| --- | ---: | ---: | ---: | ---: |
| Core | 206 | 92 | 72 | 370 |
| Bitcoin | 21 | 0 | 39 | 60 |
| Elements | 0 | 0 | 103 | 103 |
| Total | 227 | 92 | 214 | 533 |

The denominator is the public header surface; it includes two secp declarations
without primitive jet-node registrations. The 92 conditional proofs leave the
actual linked libc implementation outside the proof. The 227 other entries
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
