# Integration and pending-jet reconciliation

The history cleanup preserves the implementation and canonical specification.
Mismatches belong in `JET_*_MISMATCHES.md` for the Simplicity developers.
The accepted local-contract registry contains 430/533 jets (319 without an extra libc
premise; 111 conditional on `memcpy_model`). Full acceptance passed.

Reproduce acceptance from the repository root:

```sh
bash Coq/check-jets.sh --accept
```

The commit and this command are the evidence. Logs stay outside the repository.

## Candidate reconciliation

Claude’s approximate pending list contained three partial-name search hits.
The 33 actual jets plus the overlooked entropy and beta endpoints are accounted
for below. Twenty-five were already in the separately verified 420-jet integration;
ten are newly accepted registrations.

| Jet | Registration |
| --- | --- |
| `asset_amount_hash` | New accepted local contract |
| `broken_do_not_use_check_lock_distance` | Existing verified integration |
| `broken_do_not_use_check_lock_duration` | Existing verified integration |
| `calculate_asset` | New accepted local contract |
| `calculate_confidential_token` | New accepted local contract |
| `calculate_explicit_token` | New accepted local contract |
| `check_lock_height` | Existing verified integration |
| `check_lock_time` | Existing verified integration |
| `current_sequence` | Existing verified integration |
| `fe_add` | Existing verified integration |
| `fe_is_odd` | Existing verified integration |
| `fe_is_zero` | Existing verified integration |
| `fe_multiply` | New accepted local contract |
| `fe_negate` | Existing verified integration |
| `fe_normalize` | Existing verified integration |
| `fe_square` | New accepted local contract |
| `ge_negate` | Existing verified integration |
| `gej_infinity` | Existing verified integration |
| `gej_is_infinity` | Existing verified integration |
| `gej_negate` | Existing verified integration |
| `input_sequence` | Existing verified integration |
| `nonce_hash` | New accepted local contract |
| `num_inputs` | Existing verified integration |
| `num_outputs` | Existing verified integration |
| `outpoint_hash` | New accepted local contract |
| `scalar_add` | Existing verified integration |
| `scalar_is_zero` | Existing verified integration |
| `scalar_multiply` | Existing verified integration |
| `scalar_negate` | Existing verified integration |
| `scalar_normalize` | Existing verified integration |
| `scalar_square` | Existing verified integration |
| `tx_is_final` | Existing verified integration |
| `version` | Existing verified integration |
| `calculate_issuance_entropy` | New accepted local contract |
| `fe_multiply_beta` | New accepted local contract |

## Scope and remaining obligations

- Every entry is a local Clight implementation-to-canonical-program contract,
  with its declared frame/environment preconditions. The target is LP64 Linux.
- The seven new Elements results retain `memcpy_model` and concrete initialized
  SHA dispatch/counter facts. They do not prove the linked libc implementation
  or general caller startup. Beta multiplication retains `beta_initialized`.
- The main multiply and square proofs are promoted. The independently checked
  parallel proofs remain an alternative archive, as requested.
- The Elements SHA proof copies name the actual Elements AST explicitly. They
  do not identify the ordinary SHA translation unit with the Elements program.
- Shared frame/evaluator admissibility and exhaustive inherited canonical
  fidelity review remain open; see `JET_INHERITED_REVIEW.md`.
- The remaining 103 header declarations have no registered final contract.
  Cached Bitcoin hashes and SHA startup helpers are support until their raw-data
  and operational boundaries meet the public coverage requirements.

## Recovered canonical boundaries

The calculation ports retain the literal hash-block programs: issuance entropy
uses the double-SHA outpoint digest plus the contract word; asset and token
calculations use the entropy word and the original zero/explicit/confidential
suffix block. The existing typed byte/word bridges preserve the index ordering,
SHA padding and word widths.

`asset_amount_hash` preserves the Haskell asset/amount branch order, prefixes
0x0a/0x0b and 0x08/0x09, explicit prefix 0x01, and the distinct 32/8-byte payloads.
`nonce_hash` retains absence/explicit/even/odd prefixes 0/1/2/3. `outpoint_hash`
retains the optional parent-chain hash followed by the 32-byte hash and four-byte
index. Each is a complete context-update success/failure contract over the
original C body; the literal ports and framing/global predicates are included
in the reviewed definition snapshots. These are scoped source/contract reviews,
not a verified Haskell compiler or a claim of completing inherited fidelity.

## Module and history accounting

All jet modules, including the twenty former regression-only modules, enter the
jet build and recursive kernel check. Incomplete derived trees and the five
failing support modules are explicitly archived in `proof-work/derived-trees`
and `proof-work/unbuilt-support`. The original upstream secp/modinv verification
sources retain their original paths and separate full-Coq build; they are not
additional jet registrations (see `../JET_BUILD.md`).

The rewritten integration history removes 2,028 log/receipt/duplicate files
and 1,116,250 lines. Original branch and WIP histories remain under backup refs.
Pushing, upstream filing, and deleting branches/worktrees/backups require user
approval and are not part of local acceptance.

## Completed verification

Full `bash Coq/check-jets.sh --accept` passed on proof-source commit
`d866ef20cc668c91251ad8b1f77a030f4a46c338` with frozen inputs: 1550 built C modules recursively kernel-checked,
1,305 module assumption snapshots and 1,367 module contract/definition snapshots
matched, all source/mutation and negative gate checks passed, and all five pinned
ASTs regenerated identically. The 7,223 public result profiles retain the inherited
library assumptions; the 5,850 original profiles are unchanged. No kernel axiom
was added to the fifteen-entry allowlist.

Focused `--accept --jets=simplicity_verify` also passed in a separate checkout
of `23adcc78`, with the same checker and byte-identical selected closure,
containing an additional listed proof module whose unknown tactic independently
fails compilation. This verifies that an unrelated broken proof does not block
the selected dependency closure; it makes no additional jet coverage claim.

Source archives, alternate proofs and original WIP histories are preserved.
Acceptance establishes the stated local contracts with the trust and fidelity
limits above; it does not close the remaining 103 declarations or shared
evaluator/startup obligations.
