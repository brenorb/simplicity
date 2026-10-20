# Integration and pending-jet reconciliation

The history cleanup preserves the implementation and canonical specification.
Mismatches belong in `JET_*_MISMATCHES.md` for the Simplicity developers.
The current candidate registry contains 430/533 jets (319 without an extra libc
premise; 111 conditional on `memcpy_model`). Final acceptance is pending.

Reproduce acceptance from the repository root:

```sh
bash Coq/check-jets.sh --accept
```

The commit and this command are the evidence. Logs stay outside the repository.

## Candidate reconciliation

Claude’s approximate pending list contained three partial-name search hits.
The 33 actual jets plus the overlooked entropy and beta endpoints are accounted
for below. Twenty-five were already in the separately verified 420-jet integration;
ten are new registrations awaiting final acceptance.

| Jet | Registration |
| --- | --- |
| `asset_amount_hash` | New candidate registration |
| `broken_do_not_use_check_lock_distance` | Existing verified integration |
| `broken_do_not_use_check_lock_duration` | Existing verified integration |
| `calculate_asset` | New candidate registration |
| `calculate_confidential_token` | New candidate registration |
| `calculate_explicit_token` | New candidate registration |
| `check_lock_height` | Existing verified integration |
| `check_lock_time` | Existing verified integration |
| `current_sequence` | Existing verified integration |
| `fe_add` | Existing verified integration |
| `fe_is_odd` | Existing verified integration |
| `fe_is_zero` | Existing verified integration |
| `fe_multiply` | New candidate registration |
| `fe_negate` | Existing verified integration |
| `fe_normalize` | Existing verified integration |
| `fe_square` | New candidate registration |
| `ge_negate` | Existing verified integration |
| `gej_infinity` | Existing verified integration |
| `gej_is_infinity` | Existing verified integration |
| `gej_negate` | Existing verified integration |
| `input_sequence` | Existing verified integration |
| `nonce_hash` | New candidate registration |
| `num_inputs` | Existing verified integration |
| `num_outputs` | Existing verified integration |
| `outpoint_hash` | New candidate registration |
| `scalar_add` | Existing verified integration |
| `scalar_is_zero` | Existing verified integration |
| `scalar_multiply` | Existing verified integration |
| `scalar_negate` | Existing verified integration |
| `scalar_normalize` | Existing verified integration |
| `scalar_square` | Existing verified integration |
| `tx_is_final` | Existing verified integration |
| `version` | Existing verified integration |
| `calculate_issuance_entropy` | New candidate registration |
| `fe_multiply_beta` | New candidate registration |

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
