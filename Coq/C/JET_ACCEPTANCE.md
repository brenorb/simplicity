# Integration and pending-jet reconciliation

The history cleanup preserves the implementation and canonical specification.
Mismatches belong in `JET_*_MISMATCHES.md` for the Simplicity developers.
The local-contract registry contains 432/533 jets (321 without an extra libc
premise; 111 conditional on `memcpy_model`). The earlier 430-entry baseline passed
full acceptance; the additional `gej_rescale` and `sha_256_block` endpoints
passed scoped acceptance.

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
- The remaining 101 header declarations have no registered final contract.
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

## Proof preservation and verification

Every jet module, including the former regression-only modules, is built and
recursively kernel-checked. Derived trees and known failing support experiments
remain archived outside the active build. Original upstream secp/modinv sources
retain their separate full-Coq build; they are not additional registrations.

The cleanup removes the fixed recursive source-reference gate, receipt metadata,
archive integrity machinery, obsolete run journals and byte-identical source
copies. Every active proof, reviewed snapshot and registration is unchanged;
every distinct archived Coq source and historical patch remains available.
The remaining literal correspondence checks and production source pins still
run. Removing the fixed reference loses its supplementary textual-drift check;
it does not prove any additional correspondence.

Full `bash Coq/check-jets.sh --accept` passed on cleanup source revision
`e7170ff9a83e3ccd0efd060e57854faa7944be4b`: 1,550 C modules built and
recursively kernel-checked, 1,305 assumption snapshots and 1,367 contract/definition
snapshots matched, negative fixtures passed, and all five pinned ASTs regenerated
identically. The 7,223 public result profiles and fifteen-entry inherited kernel
axiom allowlist are unchanged. No unsafe kernel category was enabled.

Both archived parallel multiplication/square endpoints also compiled in a fresh
external tree and passed recursive kernel checking with the same inherited
axiom allowlist. Reproduce that check with:

```sh
bash proof-work/fe-multiply-parallel/verify.sh /tmp/parallel-field-check
```

The Nix source filters now retain the review helper directories, snapshots,
project variants and required source/configuration inputs. Reconstructing their
filtered payloads preserved the complete audit fingerprint, and all source and
mutation checks passed against those isolated payloads. A full Nix derivation
was not run locally because Nix was unavailable.

The earlier focused `--accept --jets=simplicity_verify` test at `23adcc78`
verified that an unrelated listed, failing module does not block the selected
closure. Cleanup does not change closure selection or any selected proof.

Git preserves the original candidates and recovery history; see
`../../proof-work/README.md`. Current acceptance uses the commit and reproducible
commands, with run output outside the repository. Acceptance establishes the
local contracts and conditions above; the remaining 101 declarations and shared
evaluator/startup and inherited-fidelity obligations remain open.

## Subsequent completion: `gej_rescale`

`C.jet_secp_rescale_local.gej_rescale_literal_local_spec` proves the original
public C jet against the literal Haskell rescale/cube/zinv program for all four
Word256 inputs, including zero scale and arbitrary coordinates. It derives
the actual allocation, source-frame copy, readers, helper, writer, return and
frees under the existing `secp_jet_local_spec`; no curve/nonzero, startup or
libc-model premise is added. Its six assumptions are inherited Coq/CompCert
assumptions, with no new axioms. The selected multiply/square registrations
are unchanged.

Reproduce its acceptance with the declared Coq 8.17.1 toolchain:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_rescale
```

This checks the 291-module dependency closure, reviewed assumptions/contracts,
global source/mutation checks (including the new literal correspondence check)
and all five regenerated C ASTs. It passed without updating expectations or
changing production C, the frozen specifications, API contracts or generation
settings. This scoped result does not close the repository-wide obligations
listed above.

## SHA block boundary

`C.jet_sha_block_literal_local.sha_256_block_literal_local_spec` executes the
original SHA-unit jet for every Word256 state and Word512 block, against the
literal canonical block tree. The word-wiring bridges are closed equalities
in every Core algebra; the literal-add semantic bridge reuses the checked
adder adapter. The source gate compares the Core trees, 64 round constants
and word/bit dependencies, with 86 rejected mutations.

The local contract retains `sha_dispatch_ok`, requiring the initialized
portable compression function. Supporting startup and caller-lifecycle
theorems establish and preserve that state from the program's actual initial
memory through owned memory operations and verified jet calls. They do not
cover arbitrary externally installed dispatch callbacks, nor discharge the
general evaluator/caller obligations above. No libc model is required.

Reproduce scoped acceptance with the declared Coq 8.17.1 toolchain:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_block
```

This passed the 264-module kernel closure, reviewed assumption/contract
comparisons, global source/mutation checks, negative tests and all five AST
regenerations, with unchanged audited inputs and no expectation updates.

The six local and eight startup/lifecycle assumptions are inherited; there
are no new project axioms. The selected field multiply/square endpoints remain
unchanged. This new registration does not assert a fresh full 432-entry audit.
