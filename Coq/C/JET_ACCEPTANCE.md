# Integration and pending-jet reconciliation

## Scoped linear-verification acceptance

`C.jet_secp_linear_verify_local.linear_verify_initialized_local_spec` passed
full scoped acceptance on the exact inputs of `f3658dbf`. It proves the entire
original `linear_verify_1` wrapper against its literal Simplicity assertion
term for all six input words and general valid frames/cursors, including both
success and failure. The proof composes the actual readers, curve guards,
arithmetic calls, return conversion and seven local frees. The table
denominator condition follows from the curve guard; the only extra library
premise is the approved `memset_model`. No output capacity is required.

```sh
JOBS=12 bash Coq/check-jets.sh --accept --jets=simplicity_linear_verify_1
```

The run exited successfully after recursive kernel checking on 1,035 modules,
matching assumption records on 966 modules and contract records on 984 modules,
gate negative tests and all five AST regeneration comparisons. Its input
fingerprint remained unchanged throughout the run. The existing source gate
checks the canonical assertion tree, named Haskell term, CoreJets dispatch and
FFI entry, rejecting fourteen targeted mutations.

Accepted proof coverage is now 525/533: 375 equivalences without an extra
library premise, 149 conditional equivalences (138 memcpy, 5 CTZ, 6 memset),
and one whole-public divergence. Eight jets remain unresolved. This scoped
result applies to its exact inputs, not later proof changes.

## Scoped checked linear-combination acceptance

`C.jet_secp_checked_linear_local.checked_linear_initialized_local_spec` is
passed full scoped acceptance on the exact inputs of `6491c8b6`. It derives the original `linear_combination_1`
wrapper for all scalar/coordinate words and general valid frames/cursors,
including both assertion success and failure. It reuses the accepted general
ecmult, initialized constants, frame readers, writer and local frees; the sole
extra library premise is the approved `memset_model`. Ordinary compilation
and scoped reviewed statement/assumption comparisons pass. The existing
source gate binds the CoreJets constructor, Haskell assertion tree, FFI entry
and complete initialized partial contract, rejecting 17 new mutations.

```sh
JOBS=12 bash Coq/check-jets.sh --accept --jets=simplicity_linear_combination_1
```

The run exited successfully after recursive kernel checking on 1,013 modules,
matching assumption records on 943 modules and contract records on 962 modules,
negative tests and all five AST regeneration comparisons. Its input fingerprint
stayed fixed and matched the committed inputs afterwards.

That accepted milestone covered 524/533: 375 equivalences without an extra
library premise, 148 conditional equivalences (138 memcpy, 5 CTZ, 5 memset),
and one whole-public divergence. Nine jets remained unresolved. This scoped
result applies to its exact inputs, not later proof changes.

## Scoped off-curve linear-combination acceptance

`C.jet_secp_linear_local.off_curve_linear_initialized_local_spec` passed full
scoped acceptance on the exact inputs of `938cf401`. It proves the entire original public C
wrapper against `literal_off_curve_linear_combination_1` for all five input
words and general valid frames/cursors, with only the approved `memset_model`
extra library premise. Actual program initialization establishes its split
constants, beta and generator tables; actual calls preserve startup state.
The existing source gate binds the named Haskell library term and FFI
comparison, reuses the 75 Strauss ports, checks the generator leaves and
rejects 20 added targeted mutations. This helper has no CoreJets constructor.

```sh
JOBS=12 bash Coq/check-jets.sh --accept --jets=simplicity_off_curve_linear_combination_1
```

The run passed recursive kernel checking on 989 modules, assumption
comparisons on 919 modules, contract comparisons on 938 modules, gate negative
tests and all five AST regeneration comparisons. The audit input fingerprint
was unchanged throughout and matched the committed inputs afterwards.

That accepted milestone covered 523/533: 375 equivalences without an extra
library premise, 147 conditional equivalences (138 memcpy, 5 CTZ, 4 memset),
and one whole-public divergence. Ten jets remained unresolved. This result
applies to its exact inputs, not later proof changes.

## Scoped checked scale and shared helper acceptance

`C.jet_secp_checked_scale_local.checked_scale_initialized_local_spec` passed
joint scoped acceptance on the exact inputs of `18d941d3`, together with
`off_curve_scale` and `gej_is_on_curve`, whose shared helpers were strengthened.
It proves the original C scale wrapper against the literal assertion-bearing
Simplicity term for every scalar/coordinate input word and general valid
frames/cursors. Both successful output and assertion failure are covered.
Startup for the original `_ng__1` global is established from real program
initialization and preserved by execution. The only extra library premise
is the approved `memset_model`.

```sh
JOBS=12 bash Coq/check-jets.sh --accept --jets=simplicity_off_curve_scale,simplicity_scale,simplicity_gej_is_on_curve
```

The run passed recursive kernel checking on 999 modules, assumption comparisons
on 929 modules, contract comparisons on 948 modules, negative tests and all
five AST regeneration comparisons. The audit fingerprint remained unchanged
and matched the committed inputs afterwards. The source binding reuses the
75 off-curve ports and checks Scale's catalog, assertion, FFI entry and complete
initialized success/failure contract, rejecting 21 added targeted mutations.

Accepted coverage is 522/533: 375 equivalences without an extra library
premise, 146 conditional equivalences (138 memcpy, 5 CTZ, 3 memset), and one
whole-public divergence. Eleven jets remain unresolved; the goal is active.
This receipt applies to its exact inputs, not future proof changes.

## Earlier scoped off-curve scale acceptance

`C.jet_secp_scale_local.off_curve_scale_initialized_local_spec` passed
scoped acceptance on the exact proof inputs of `5e87dacb`. It derives the
entire original C wrapper against the literal `off_curve_scale` Simplicity
term, for unrestricted scalar and coordinate words and general valid frames
and cursors. Startup is established from the original program's initialized
memory. The only extra library premise is the approved `memset_model`.

The source binding checks the named Haskell library term, its FFI comparison,
75 literal ports, the complete initialized contract and 38 targeted mutations.
This exported C helper has no `CoreJets` constructor; no commitment identity is
invented. Existing field, scalar and word source gates remain in use.

Reproduce with the pinned toolchain and dependencies from `Coq/JET_BUILD.md`:

```sh
JOBS=12 bash Coq/check-jets.sh --accept --jets=simplicity_off_curve_scale
```

The run passed recursive kernel checking on 968 modules, matching assumption
records for 898 modules and contract records for 917 modules, negative tests,
and all five AST regeneration comparisons. Its audit-input fingerprint was
unchanged throughout and matched the registration commit's inputs afterwards.
The kernel reported no unsafe features or new library axioms.

That earlier acceptance brought proof coverage to 521/533: 375 equivalences without an extra library
premise, 145 conditional equivalences (138 memcpy, 5 CTZ, 2 memset), and one
whole-public divergence. Twelve declarations lacked an accepted outcome at
that point. Later source changes require their own verification.

## Current whole-project acceptance and writable-word integration

The exact proof inputs at `6a227e8b` passed ordinary whole-project acceptance
with Coq 8.17.1: all 2,109 C modules were recursively kernel-checked, 1,861
assumption-module and 1,924 contract-module records matched, negative tests
passed, and all five regenerated ASTs matched. All 104 global source/mutation
checks passed, and the audit input fingerprint was unchanged throughout.
Reproduce with the pinned dependencies from `Coq/JET_BUILD.md`:

```sh
JOBS=12 bash Coq/check-jets.sh --accept
```

That candidate is integrated by signed merge `58f36fe9`. It generalizes only
the proof-side exclusive end of writable words to `max_unsigned + 1`, retains
all public execution/output/framing conclusions, transports the corresponding
writer/copy contracts, and adds complete low/high executions on a constructed
last-word memory. This is an abstract CompCert-memory witness, not a claim of
allocator or evaluator reachability. The C, original specifications, API
contracts and generation configuration are unchanged.

Proof coverage is 514/533: 513 equivalence contracts (375 without an extra
library premise, 138 conditional on `memcpy_model`) and one checked whole-public
divergence for `gej_ge_add_ex`. The divergence and equivalence classifications
remain separate; the restricted positive ratio theorem alone does not count.
Nineteen jets still lack either outcome, and shared conditional/domain/caller
qualifications remain. The goal is not complete.

The full acceptance statement above applies to `6a227e8b`, not automatically
to later additions. The null-overlap counterexample and field-normalization
modules added afterwards passed separate focused validation on unchanged
`58f36fe9` inputs: normal compilation of the two roots below and their complete
dependencies, recursive kernel checking with the unchanged library allowlist
and no unsafe features, and matching no-update assumption/contract records
across all seven added modules. The post-merge coverage regression tests and
240-file frozen-target check also passed. This is combined phase validation,
not a new whole-project `--accept` run at the merged tip. Reproduce the added
proof closure with:

```sh
JET_TARGETS="C/jet_elements_null_overlap_counterexample.vo C/jet_secp_modinv_normalize62_numeric.vo" bash Coq/build-jets.sh -j2
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o C.jet_elements_null_overlap_counterexample C.jet_secp_modinv_normalize62_numeric
```

The normalizer is an internal inversion dependency, not an additional jet;
the aliasing counterexample does not refute an accepted separated-frame contract.

## Earlier integration history

The history cleanup preserves the implementation and canonical specification.
Mismatches belong in `JET_*_MISMATCHES.md` for the Simplicity developers.
The local-contract registry contains 513/533 jets (375 without an extra libc
premise; 138 conditional on `memcpy_model`). Accepted local-contract coverage is
513/533, including the computing issuance hash, affine/projective curve,
projective X-equivalence, doubling, mixed-addition, square-root and mixed
equivalence and decompression endpoints. On `f1309893`, `JOBS=2 bash Coq/check-jets.sh --accept
--jets=simplicity_gej_ge_equiv` passed: 442 kernel-checked modules, 381 assumption
records, 396 contract records, all source/negative checks and all five ASTs.
This is scoped acceptance, not a new whole-repository acceptance claim.
The six Bitcoin value-array/composite/indexed hash registrations passed ordinary
scoped acceptance on `b42762b6`'s proof inputs (identical audited inputs in
the documentation-only descendant `191617fd`): 351 recursively kernel-checked
modules, 222 assumption records, 245 contract records, all source/negative
checks and all five regenerated ASTs, with unchanged audit inputs. Four add
no libc premise; the indexed pair retains `memcpy_model`. None change the
frozen environment domain or establish the caches through their callers.
Accepted local-contract coverage is 511/533: 373 without an extra libc premise
and 138 conditional on `memcpy_model`; 22 declarations remain unresolved.
The all-jet goal and shared conditional obligations are not complete.
Reproduce on `b42762b6`:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_output_values_hash,simplicity_bitcoin_input_values_hash,simplicity_bitcoin_outputs_hash,simplicity_bitcoin_input_utxos_hash,simplicity_bitcoin_output_hash,simplicity_bitcoin_input_utxo_hash
```

The transaction/signature-hash pair in `jet_bitcoin_tx_sig_hash_literal` passed
ordinary scoped acceptance on `f59d2305`: 294 recursively kernel-checked modules,
165 assumption records, 188 contract records, all source/negative checks and all
five regenerated ASTs, with unchanged audit inputs. Both add no libc premise
and preserve the existing environment contracts, frozen Bitcoin domain and
documented LockTime identity discrepancy. The source gate rejects 22 targeted
mutations. Accepted local-contract coverage is 513/533: 375 without an extra
libc premise and 138 conditional on `memcpy_model`, with 20 declarations still
unresolved. The full goal, including shared conditional obligations, is not
complete. Reproduce in a checkout of `f59d2305`:

```sh
JOBS=12 bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_tx_hash,simplicity_bitcoin_sig_all_hash
```

On `e32e7638`, the complete decompression endpoint passed ordinary scoped
acceptance: 416 kernel modules, 355 assumption records, 370 contract records,
all source and negative checks, and all five regenerated ASTs. Audit inputs
were unchanged. It adds no libc premise; its canonical-source/full-contract
gate rejects 15 targeted mutations. Accepted local-contract coverage is now
503/533 (367 without an extra libc premise, 136 conditional on `memcpy_model`),
with 30 header declarations still lacking a registered final proof. Reproduce
on that commit:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_decompress
```

The projective-addition public theorem
`C.jet_secp_gej_add_local.gej_add_literal_local_spec` is now registered, bringing
the registry to 504/533 (29 declarations without a registered final proof).
It proves the original full public C call against `literal_gej_add`, with no
extra libc premise or input restriction. Its public modules passed normal
compilation and reviewed no-update focused snapshots; the canonical catalog,
literal and whole-contract gate rejects ten targeted mutations and inventory
regressions pass. On `ba6b19e8`, scoped acceptance passed: 450 kernel-checked
modules, 389 assumption records, 404 contract records, all source and negative
checks, and all five regenerated ASTs. The audit input fingerprint was unchanged.
Accepted local-contract coverage is 504/533 (368 without an extra libc premise;
136 conditional on `memcpy_model`), with 29 declarations without a registered
final proof. This receipt applies to that exact commit, not subsequent proof
changes. Reproduce on `ba6b19e8`:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_gej_add
```

The projective-equivalence theorem
`C.jet_secp_gej_equiv_local.gej_equiv_literal_local_spec` is registered,
bringing the registry to 505/533 (28 declarations without a registered final
proof). It covers the original full public C call over two unrestricted GEJ
inputs and a one-bit output, against `literal_gej_equiv`. The proof composes
the actual negation, generic addition and infinity-test calls, including all
allocation/free and frame obligations; it adds no libc premise. Normal build,
recursive kernel checking and reviewed no-update focused snapshots passed.
The canonical catalog/literal/full-contract gate rejects 13 targeted mutations.
On `0cb928b9`, scoped acceptance passed: 472 kernel-checked modules, 411
assumption records, 426 contract records, all source and negative checks, and
all five regenerated ASTs. Audit inputs were unchanged. Accepted local-contract
coverage is 505/533 (369 without an extra libc premise, 136 conditional on
`memcpy_model`), with 28 declarations without a registered final proof. This
receipt applies to that exact commit, not subsequent proof changes. Reproduce
on `0cb928b9`:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_gej_equiv
```

After the definitions-only safegcd dependency and arithmetic inversion helpers
were integrated, the same command also passed on `c704be90`: 472 kernel
modules, 411 assumption records, 426 contract records, negative tests and all
five regenerated ASTs, with unchanged audit inputs. This is a scoped
integration check on that exact commit; it does not register inversion or
establish a new public jet proof.

The earlier 430-entry baseline passed
full acceptance; the additional `gej_rescale` and `sha_256_block` endpoints
and ten context-add endpoints passed scoped acceptance, followed by buffer-add
and finalization. TapData then passed the fourteen-jet scoped acceptance below.
The four Bitcoin SHA registrations then passed the scoped acceptance below.
Tappath hash then passed the expanded consumer acceptance below.
The four array-hash registrations then passed ordinary scoped acceptance below.
The five array/tappath rows now select accepted raw-interpretation variants,
without a change to the coverage count; their scoped acceptance is recorded below.
The two tapleaf/tap-environment registrations then passed scoped acceptance below.
The three input outpoint/annex/combined-hash registrations then passed ordinary
scoped acceptance below.
The single-input Bitcoin hash and seven Elements array-hash registrations then
passed ordinary scoped acceptance below.
The five further Elements input/taproot hash registrations then passed ordinary
scoped acceptance below.
The four Elements issuance-proof/nonce/amount-hash registrations then passed
ordinary scoped acceptance below.

Three Elements composite/blinding-hash registrations and issuance status then
passed ordinary scoped acceptance below.
The three computed issuance getters and annex context jet then passed ordinary
scoped acceptance together (338 kernel modules, 237 assumption modules and
251 contract modules, gate negative tests and five regenerated ASTs).
The two Elements taproot builders then passed ordinary scoped acceptance below.
The two issuance amount-array getters and composite issuances hash then passed
ordinary scoped acceptance below.
The Elements transaction and signature hash entries then passed ordinary scoped
acceptance below.
The computing input UTXO hash entry then passed ordinary scoped acceptance
below, bringing accepted local-contract coverage to 492/533.
The computing output hash entry then passed ordinary scoped acceptance below,
bringing accepted local-contract coverage to 493/533.
The computing input hash entry then passed ordinary scoped acceptance below,
bringing accepted local-contract coverage to 494/533.

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
- The remaining 34 header declarations have no registered final contract.
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
local contracts and conditions above; the remaining 89 declarations and shared
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

## SHA context-add family

The ten `sha_256_ctx_8_add_{1,2,4,8,16,32,64,128,256,512}` entries select the
complete `sha_jet_partial_local_spec` theorems in `jet_sha_ctx8_literal_local.v`.
They prove execution of the actual SHA-unit public C functions against the
literal canonical assertion programs: successful results, false returns for
assertion failures, and the declared memory/frame properties. No input counter,
buffer length or failure case is excluded. All retain `memcpy_model` and
`sha_globals_ok`; they do not prove the linked libc implementation.

One shared program equality handles every byte-vector depth. The block
bridge is lifted to option semantics rather than repeating compression
proofs. The existing startup adapter gives ten stronger state-preserving
contracts, starting from the actual initialized program through the covered
caller lifecycle; arbitrary external dispatch replacements remain unproved.
The local theorems inherit six assumptions, startup variants eight, with no
new axioms. The source gate checks the canonical trees, buffer/increment/count
and assertion dependencies, recursion, all ten catalog/type/contract mappings,
and twenty context mutations (in addition to the block tests).

Reproduce family-scoped acceptance under the declared Coq 8.17.1 baseline:

```sh
sha_ctx_jets=$(printf 'simplicity_sha_256_ctx_8_add_%s,' 1 2 4 8 16 32 64 128 256 512)
bash Coq/check-jets.sh --accept --jets="${sha_ctx_jets%,}"
```

This passed the 265-module recursive kernel check, reviewed assumption and
contract comparisons, global source/mutation checks, negative tests and all
five AST regenerations. Audited inputs stayed unchanged and no expectations
were updated during acceptance.

These are ten conditional local-contract registrations, not a fresh full
442-entry acceptance audit or completion of the shared obligations above.

## SHA buffer-add and finalization

The selected complete local contracts are in `jet_sha_buffer_literal_local.v`
and `jet_sha_finalize_literal_local.v`. They execute the original public C
functions against the literal canonical assertion programs, including every
counter, buffer length, and assertion-failure case. They retain `memcpy_model`
and `sha_globals_ok`; they do not prove the linked libc implementation or
arbitrary externally installed dispatch callbacks. Startup variants reuse the
existing invariant and its preservation through the covered caller lifecycle.

The buffer bridge retains the empty-buffer count assertion and reuses the
one-byte/vector bridges. Finalization checks then clears the counter for
padding, assembles the padded block and original bit length, and calls the
literal block program. Constant shift/add wiring, padding stages and buffer
flags have closed program-equality proofs; option-semantic bridges reuse the
existing block bridge. The source gate compares the actual canonical trees
and their dependencies, with 24 additional rejected mutations.

The two local theorems inherit six assumptions and startup variants eight,
with no new project axioms. Reproduce acceptance under Coq 8.17.1:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_ctx_8_add_buffer_511,simplicity_sha_256_ctx_8_finalize
```

This passed the 276-module recursive kernel check, reviewed assumptions and
contracts, global source/mutation checks, negative tests and all five AST
regenerations. Audited inputs stayed unchanged and no expectations were
updated during acceptance.

These are conditional local-contract registrations, not a fresh full
444-entry audit or closure of the shared evaluator/libc/fidelity obligations.

## TapData initializer and closed SHA program bridges

`jet_tapdata_literal_local.v` composes the original public C initializer with
the canonical `tapdataInit` program. Its local contract retains `memcpy_model`
and both `sha_globals_ok` and `sha_tag_ok`. Its startup variant reuses the
existing initialized portable-dispatch lifecycle; arbitrary externally
installed callbacks are not covered. The local theorem inherits six library
assumptions and the startup variant eight; neither adds a project axiom.

The scribed prefix is derived by `jet_tapdata_host_recipe.v`, a port of the
fixed two-block recipe in the vendored `Digest/Pure/SHA.hs`. Closed Coq
computations establish its tag bytes, padding, block lengths, digest and
prefix. The source check covers encoding, schedule, round constants and
complete public contracts, rejecting 131 additional mutations. This is
source-reviewed correspondence for the fixed host computation, not a formal
interpreter or general correctness theorem for Haskell's binary decoders.

The shared positive-depth adder bridge is now a reflexive equality in every
Core algebra. Consequently the SHA block, option, context-add, buffer-add and
finalizer program bridges no longer need functional extensionality. Existing
public C theorem types and programs are unchanged.

Scoped acceptance passed for TapData and all thirteen affected SHA jets:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_block,simplicity_sha_256_ctx_8_add_1,simplicity_sha_256_ctx_8_add_2,simplicity_sha_256_ctx_8_add_4,simplicity_sha_256_ctx_8_add_8,simplicity_sha_256_ctx_8_add_16,simplicity_sha_256_ctx_8_add_32,simplicity_sha_256_ctx_8_add_64,simplicity_sha_256_ctx_8_add_128,simplicity_sha_256_ctx_8_add_256,simplicity_sha_256_ctx_8_add_512,simplicity_sha_256_ctx_8_add_buffer_511,simplicity_sha_256_ctx_8_finalize,simplicity_tapdata_init
```

The run passed the default recursive kernel check on 281 modules, assumption
comparisons for 176 modules, contract comparisons for 189 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
No audited inputs changed during the run and no expectations were updated.

This does not assert a fresh full 445-entry audit or closure of the remaining
shared evaluator, libc and fidelity obligations.

## Bitcoin pure builders and context hashes

The registry selects the complete original-C local contracts in
`jet_bitcoin_taproot_literal_local.v` for `build_tapleaf_simplicity` and
`build_tapbranch`, and `jet_bitcoin_ctx_hash_literal_local.v` for
`outpoint_hash` and `annex_hash`. All four retain `memcpy_model` and initialized
SHA state; the builders also require their original static tag state. Startup
variants reuse the actual initialized portable-dispatch lifecycle and preserve
its invariant. Arbitrarily installed compression callbacks are not covered.
These four contracts add no logical transaction-environment or cached-hash
premise. They are not proofs of the linked libc or general evaluator/caller.

The tag prefixes reuse the fixed host SHA port and the general formal
`haskell_hash_word256` decoding bridge. Closed computations establish block
lengths, serialization and both fixed prefixes. Closed Core-algebra equalities
connect the builders to their earlier C-proof targets; closed option-semantic
equalities connect the context hashes, covering every counter and optional
input, including assertion failure. This does not claim a general Haskell
binary-decoder/cryptographic-library correctness theorem.

The shared source gate follows actual library projections and compares the
complete canonical shift/order/padding and context-assertion trees. It rejects
27 new builder mutations and 14 context-hash mutations. All twelve new bridge
lemmas are closed; each local C theorem inherits six library assumptions and
each startup theorem eight, with no new project axioms.

Ordinary scoped acceptance passed:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_build_tapleaf_simplicity,simplicity_bitcoin_build_tapbranch,simplicity_bitcoin_outpoint_hash,simplicity_bitcoin_annex_hash
```

This passed the default recursive kernel check on 292 modules, assumption
comparisons for 186 modules, contract comparisons for 200 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
The audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 449-entry audit or discharge of the remaining
shared evaluator, libc, startup/caller and inherited fidelity obligations.

## Primitive-bearing SHA and Bitcoin tappath hash

The context-add, buffer-add and finalizer bridges now also hold in every
assertion algebra. Their existing option interfaces, program definitions and
public C theorem types are unchanged. `jet_sha_hash_words_literal.v` composes
these closed equalities into the canonical initializer, early-stopping loop
and array-hash program. `jet_bitcoin_tappath_hash_literal.v` instantiates the
program with the existing Tappath primitive and composes the original complete
C getter proof. All ten new program bridges are closed; the C theorem inherits
six library assumptions and adds no libc-model premise.

The exact environment/cache relation is still
`hash_getter_rep (fun e => words_hash_of 5 3 (tappath_of e)) 8 40 176`, with
the existing separation and frame contract. This proves the cached getter,
not the caller's cache construction. It retains the formal environment and
its path bound of 128 entries, matching the real C taproot builder's
well-formedness guard. It does not assert equivalence on arbitrary fabricated
overlong environments, nor resolve the inherited Bitcoin-domain discrepancies
in `JET_BITCOIN_MODEL_MISMATCHES.md`.

The existing source checker follows actual library projections, initialization,
loop termination/counter width, primitive selection and interpretation, and
the complete final C contract, rejecting 25 additional mutations. Host
interpreter correspondence is source-reviewed, not a general Haskell
interpreter correctness theorem.

Ordinary scoped acceptance passed for tappath hash and the fourteen affected
context-add/buffer/finalizer and Bitcoin context-hash consumers:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_sha_256_ctx_8_add_1,simplicity_sha_256_ctx_8_add_2,simplicity_sha_256_ctx_8_add_4,simplicity_sha_256_ctx_8_add_8,simplicity_sha_256_ctx_8_add_16,simplicity_sha_256_ctx_8_add_32,simplicity_sha_256_ctx_8_add_64,simplicity_sha_256_ctx_8_add_128,simplicity_sha_256_ctx_8_add_256,simplicity_sha_256_ctx_8_add_512,simplicity_sha_256_ctx_8_add_buffer_511,simplicity_sha_256_ctx_8_finalize,simplicity_bitcoin_outpoint_hash,simplicity_bitcoin_annex_hash,simplicity_bitcoin_tappath_hash
```

This passed the default recursive kernel check on 315 modules, assumption
comparisons for 194 modules, contract comparisons for 211 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
The audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 450-entry audit or discharge of the remaining
shared evaluator, libc, startup/caller and inherited fidelity obligations.

## Bitcoin script and sequence array hashes

`jet_bitcoin_array_hash_literal.v` connects the canonical output-scripts,
input-scripts, input-sequences and input-scriptSigs hash programs to the original
complete C getter proofs. Its shared equality holds for every indexed primitive
and primitive algebra. The specializations retain 32-bit indices, 32-byte hash
elements or 4-byte sequence elements, initialization, early termination and
finalization. No prior execution theorem or program definition is changed.

The exact `application_jet_local_spec_sep` framing and `hash_getter_rep`
relations are retained, at transaction offsets 48, 176, 240 and 304. Each C
endpoint inherits six library assumptions and adds no libc premise. The shared
program equality is closed. Normal compilation, recursive kernel checking with
supported VM conversion and reviewed snapshot comparisons passed. The source
checker validates the four full canonical programs and selected primitive
projections, rejecting 34 additional mutations; this is not a general Haskell
interpreter theorem.

These are cached-getter contracts, not proofs of caller cache construction or
full Haskell-to-Coq environment-domain agreement. The frozen-domain differences
in `JET_BITCOIN_MODEL_MISMATCHES.md` remain unresolved. The extended input-script
and scriptSig hash lists remain abstract logical fields; this batch does not
establish them from raw caller scripts.

Ordinary scoped acceptance passed:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_output_scripts_hash,simplicity_bitcoin_input_scripts_hash,simplicity_bitcoin_input_sequences_hash,simplicity_bitcoin_input_script_sigs_hash
```

This passed the default recursive kernel check on 241 modules, assumption
comparisons for 126 modules, contract comparisons for 143 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
The audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 454-entry audit or discharge of the shared
evaluator, libc, startup/caller, domain and inherited-fidelity obligations.

## Raw interpretation of five composed Bitcoin hash programs

`jet_bitcoin_raw_program.v` restores the preserved generic raw-program bridge
unchanged. Its algebra keeps the same primitive signature, uses the frozen
Bitcoin interpretation for base primitives, and computes extended script and
scriptSig hashes from raw bytes. A relation covering all Core combinators,
assertions and failure transports every parametric program through the existing
`project_raw_environment` projection.

`jet_bitcoin_hash_raw_literal.v` composes this result with the accepted literal
output-scripts, input-scripts, input-sequences, input-scriptSigs and tappath
programs and complete C contracts. The generic helper's parametricity and C
execution premises are discharged by the concrete final proofs. The registry
now selects these five raw variants; this is a semantic-boundary strengthening,
not additional declared-jet coverage.

The underlying cache/frame relation is retained through `raw_env_rep`, with
its existing path bound. No actual C caller cache construction is proved by
this batch. The frozen base domain and reported Bitcoin mismatches are
unchanged. This is not a general Haskell interpreter correctness theorem.

Both modules compile and reviewed snapshots match. The direct primitive
projection and literal-parametricity lemmas are closed; the general relation
and program-projection lemmas inherit functional extensionality. All five C
endpoints retain the same six inherited library assumptions, without an added
libc or execution/output premise. Source checks reject 22 further mutations of
raw semantics, representation boundaries and complete C contracts.

Ordinary scoped acceptance passed:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_output_scripts_hash,simplicity_bitcoin_input_scripts_hash,simplicity_bitcoin_input_sequences_hash,simplicity_bitcoin_input_script_sigs_hash,simplicity_bitcoin_tappath_hash
```

This passed the default recursive kernel check on 272 modules, assumption
comparisons for 143 modules, contract comparisons for 166 modules, global
source/mutation checks, gate negative tests and all five AST regenerations.
Audited inputs stayed unchanged and no expectations were updated.

This does not assert a fresh full 454-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Bitcoin tapleaf and tap-environment hash getters

`jet_bitcoin_tap_hash_literal.v` adapts the preserved tapleaf program tree to
the accepted fixed-tag host recipe, literal tagged-context initialization and
algebra-general SHA bridges. It supplies the full canonical `tapleafHash` and
`tapEnvHash` trees, equality in every primitive algebra, and complete original-C
contracts in both abstract and raw interpretations. The registry selects the
two raw endpoints.

The cache/frame relations are unchanged: `hash_getter_rep tapleaf_hash_of 8 8 176`
and `hash_getter_rep tap_env_hash_of 8 72 176`, lifted through `raw_env_rep`.
The final theorems discharge their shared helper's program-parametricity and
execution obligations using the existing proofs. They add no libc or
execution/output premise. The three program-equality and two parametricity
lemmas are closed; all four C variants inherit the same six library assumptions.

The tagged-context adapter is general in an already supplied prefix. Its use
here instantiates the previously checked fixed `TapLeaf` host recipe; it is not
an interpreter claim for arbitrary tags. The source checker compares the actual
explicit algebra trees with the complete canonical programs, checks library
dispatch, initialization and primitive/raw projections, and protects all four
C boundaries, rejecting 22 further mutations. Normal compilation and reviewed
snapshot comparisons passed; these are not acceptance by themselves.

Actual caller cache construction, the existing path bound and frozen-domain
differences remain open as before. No production C, canonical program or
primitive signature/domain has been changed.

Ordinary scoped acceptance passed: 282 kernel-checked modules, matching
assumption records for 153 modules and contract records for 176 modules,
negative tests and all five AST regenerations. Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_tapleaf_hash,simplicity_bitcoin_tap_env_hash
```

This does not assert a fresh full 456-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Bitcoin input outpoint, annex and combined-input hash getters

`jet_bitcoin_inputs_hash_literal.v` reuses the original element-loop body and
the accepted literal SHA/context programs to port the complete canonical
`inputOutpointsHash`, `inputAnnexesHash` and `inputsHash` programs. It generalizes
the outpoint/annex append equalities to every assertion algebra, without changing
the existing option-only APIs. The shared element adapter and all three whole
program equalities/parametricity lemmas are closed.

Six complete C contracts compose the existing getter executions in abstract and
raw primitive interpretations. The registry selects the three raw endpoints.
The cache/frame relations remain `hash_getter_rep ... 0 <offset> 432`, at offsets
112, 272 and 336, respectively, lifted through `raw_env_rep`. They add no libc,
execution or output premise and retain the same six inherited library
assumptions. Caller cache construction, the existing raw path bound and the
frozen-domain discrepancies remain open.

Normal compilation and reviewed snapshot comparisons passed for all fifteen
public theorem records and four new program definitions. The existing source
checker compares complete loop/composition trees, canonical library dispatch,
primitive/raw interpretations and all six C boundaries, rejecting 33 further
mutations. In particular, it distinguishes an absent input (stop) from a
present input with no annex (continue, appending byte zero).

Ordinary scoped acceptance passed: 280 kernel-checked modules, matching
assumption records for 151 modules and contract records for 174 modules,
negative tests and all five AST regenerations. Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_input_outpoints_hash,simplicity_bitcoin_input_annexes_hash,simplicity_bitcoin_inputs_hash
```

This does not assert a fresh full 459-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Computing Bitcoin input hash and seven Elements array hashes

`jet_bitcoin_input_hash_literal.v` composes the complete original C computing
jet with the canonical primitive-bearing `inputHash` program, including its
assertions and absent-input/absent-annex/present-annex cases. The registry
selects the raw interpretation. Its three bridges are closed; both C variants
retain six inherited library assumptions and the existing explicit
`memcpy_model` premise. The existing `input_hash_rep` relation, including SHA
global readiness and environment/output separation, is unchanged.

`jet_sha_hash_words_reader.v` and `jet_elements_words_hash_program.v` restore
the preserved generic option-Reader semantics and seven complete Elements C
cache getters without source changes. They reuse the existing SHA traversal
and absorption/finalization results; there is no artificial Bitcoin environment
or assumed hash/execution oracle.

`jet_elements_array_hash_literal.v` connects these getters to the shared
literal SHA programs. The registry selects output scripts/range proofs/
surjection proofs, input scripts/sequences/scriptSigs, and tappath. Both generic
bridges are closed; all seven C contracts retain the same six inherited
assumptions and no extra libc premise. Their cache/frame relations remain
`hash_getter_rep` at the original offsets (88, 120, 152, 280, 344 and 408 in a
760-byte transaction; 40 in the 176-byte taproot environment).

Normal compilation and reviewed snapshot comparisons passed across the four
new modules: 50 theorem records and 20 definitions. The existing source checker
compares the complete single-input tree/boundaries and the seven Elements
streams, raw primitive/proof views and C boundaries, rejecting 27 and 51 further
mutations, respectively. The exact conditional-count test now expects 129,
including the computing Bitcoin jet's existing libc premise; rejection of
substituted models or missing/extra premises remains required.

Caller environment/cache construction, persistent SHA startup, existing model
domain/path bounds, libc implementation and general host-library fidelity are
not discharged here. No production C, original specification or generation
configuration changed.

Ordinary scoped acceptance passed: 373 kernel-checked modules, 242 assumption
records and 266 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_input_hash,simplicity_output_scripts_hash,simplicity_output_range_proofs_hash,simplicity_output_surjection_proofs_hash,simplicity_input_scripts_hash,simplicity_input_sequences_hash,simplicity_input_script_sigs_hash,simplicity_tappath_hash
```

This does not assert a fresh full 467-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Elements input and taproot hash getters

`jet_elements_inputs_hash_literal.v` composes three complete original C cache
getters with the canonical primitive-bearing input-outpoints, input-annexes and
combined-input hash programs. Both outpoint primitive lookups and early exits,
the absent/present-annex encoding and the full SHA composition are retained.
Nine bridges are closed. The C contracts keep `hash_getter_rep` at offsets
216, 376 and 440 in the 760-byte transaction.

`jet_elements_tap_hash_literal.v` composes the complete original tapleaf and
tap-environment getters with canonical programs using TapleafVersion,
ScriptCMR, Tappath and InternalKey primitives. Seven bridges are closed,
including fixed host serialization and the exact `"TapLeaf/elements"` tag.
Native `Schnorr.PubKey` contains `Word256`, not a field element. The C contracts
keep offsets 8 and 72 in the 176-byte taproot environment.

All five final contracts have the same six inherited library assumptions and
no extra libc premise. Six preserved support modules were restored unchanged;
the generic Reader/loop results and existing complete C getter proofs are
reused, without an assumed execution or arbitrary cached-hash primitive.
Normal compilation, reviewed snapshots for 55 theorem records and 32
definitions, and comparisons without update flags pass. The existing source
checker rejects 36 additional input-tree/boundary mutations and 32
taproot/tag/native-key/boundary mutations. Existing negative tests remain
unchanged.

Caller cache construction, the existing model/domain/path bounds and general
host-library fidelity remain separate obligations. No production C, original
specification or generation configuration changed.

Ordinary scoped acceptance passed: 324 kernel-checked modules, 193 assumption
records and 217 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_input_outpoints_hash,simplicity_input_annexes_hash,simplicity_inputs_hash,simplicity_tapleaf_hash,simplicity_tap_env_hash
```

This does not assert a fresh full 472-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Elements issuance-proof, nonce and amount hash getters

Three adapters connect complete original C cache getters to the canonical
primitive-bearing programs. `jet_elements_issuance_proofs_hash_literal.v`
retains both primitive lookups and early exits and reuses the existing closed
asset/token proof-view lemmas. `jet_elements_nonces_hash_literal.v` distinguishes
absent output from absent nonce and reuses the native Word256 encoder bridge.
`jet_elements_amounts_hash_literal.v` shares the canonical asset/amount
serializers and primitive-pair loop between input and output hashes. Prefixes
0/1/2/3, 10/11 and 8/9 and the explicit amount's 8-byte payload are retained;
there is no new field-element restriction on native nonce words.

Six preserved support modules are restored without source changes. The generic
Reader loop, prefix/payload absorber and existing complete C getter proofs are
reused, not replaced by execution/hash oracles. The four final contracts keep
`hash_getter_rep` at offsets 536, 56, 24 and 248 in the 760-byte transaction.
All four have the same six inherited library assumptions and no extra libc
premise; all 17 adapter bridges are closed.

Normal compilation passes after rebuilding unchanged stale dependencies with
the pinned toolchain. Reviewed snapshots cover 65 theorem records and 52
definitions across nine modules; comparisons without update flags pass. The
existing source checker rejects 19 issuance-loop, 20 nonce and 26 amount-hash
mutations, reusing the mandatory primitive/native-encoding/pair-routing guards.
Existing gate negative tests remain unchanged.

Caller/cache construction, existing representation/domain/layout bounds and
general host-library fidelity remain separate obligations. No production C,
original specification, API or generation configuration changed.

Ordinary scoped acceptance passed: 367 kernel-checked modules, 235 assumption
records and 260 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_issuance_range_proofs_hash,simplicity_output_nonces_hash,simplicity_output_amounts_hash,simplicity_input_amounts_hash
```

This does not assert a fresh full 476-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Elements composite hashes, blinding entropy and issuance status

Ten preserved support modules are restored without source changes; two new
adapters connect complete original C getters to the shared literal programs.
`jet_elements_composite_hash_literal.v` reuses one fixed-vector SHA skeleton
for the canonical four-component outputs hash and two-component input-UTXO
hash. `jet_elements_blinding_entropy_literal.v` retains the three primitive
lookups, optional/new/reissuance routing and actual `Arith.one word8` program,
including its reviewed padding dependencies. The eight adapter bridges are
closed. The three full C contracts keep the original `hash_getter_rep` at
transaction offsets 184, 312 and 568 in the 760-byte structure.

The preserved `jet_elements_issuance_status_local.v` is already a literal
primitive-program endpoint for the original `simplicity_issuance`. It covers
every Word32 index and out-of-range/no-issuance/new/reissuance results. Its
initial relation represents only pointers/count and the enum at input offset
528, with stride 544 and count offset 696. It has no hash-cache, execution,
desired-output, nonzero-issuance or initialized-output premise. The actual
enum reload after the first payload write is preserved by its derived effect.
It still requires valid separated frames and is not an overlapping-buffer API
claim or production caller-construction proof.

All four endpoints retain the same six inherited library assumptions and no
extra libc premise. Normal compilation and reviewed snapshot comparisons pass
for 55 theorem records and 43 definitions across twelve modules. The existing
source checker rejects 26 composite, 24 blinding-entropy and 17 issuance-status
mutations, including component reordering, replacing the one-word program,
reversed `flip match` branches and vacuous final contracts. Existing gate
negative tests remain unchanged.

Caller/cache construction, existing representation/domain/layout bounds and
general host-library fidelity remain separate obligations. No production C,
original specification, API or generation configuration changed.

Ordinary scoped acceptance passed: 362 kernel-checked modules, 231 assumption
records and 255 contract records, followed by the unchanged gate negative tests
and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_outputs_hash,simplicity_input_utxos_hash,simplicity_issuance_blinding_entropy_hash,simplicity_issuance
```

This does not assert a fresh full 480-entry audit or discharge of the remaining
shared evaluator, libc, caller/cache, domain and inherited-fidelity obligations.

## Candidates: Elements computed issuance getters

Three preserved modules supply the complete original `issuance_entropy`,
`issuance_asset` and `issuance_token` getter executions. Two literal adapters
reuse the existing universal SHA-block and Haskell-word bridges. The new
outpoint program retains both compressions, the four-byte index reversal,
288-bit length and original second-block constant. The primitive programs
retain missing input, no issuance, new issuance and reissuance routing;
token selection still distinguishes confidential from explicit asset amounts.

The final contracts retain `application_jet_local_spec_sep` and the initial
`computed_issuance_hash_rep` at issuance-relative offsets 72, 168 and 200.
The actual enum load is at input offset 528, with stride 544 and count offset
696. Cache loads after output writes are derived from separation and effects.
No execution, desired-output, success, zero-output or issuance-kind premise
is added. The three C endpoints retain the same six inherited assumptions
and no extra libc premise. The sixteen new program bridges/parametricity
results are closed.

Normal compilation passes. Reviewed snapshots cover 39 theorem records and
37 definitions in five new modules; the existing calculation snapshots are
unchanged. The existing source checker rejects 35 further mutations of
constants, byte order, primitive routing, offsets and complete C contracts.
These three endpoints passed ordinary scoped acceptance together with annex
context hashing below. Reproduce the getter-only scope with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_issuance_entropy,simplicity_issuance_asset,simplicity_issuance_token
```

The real Elements builder must still establish the cached-value relation.
Existing caller/domain/layout and host-library obligations remain; the
production C, original specifications, API and generation settings are fixed.

## Candidate: Elements annex context hashing

`jet_elements_annex_context_exec.v` composes the original `annex_hash` C jet
with existing Elements SHA execution support. It reuses the nonce source-copy,
context-reader, counter and memory-preservation infrastructure; it does not
copy four complete SHA-jet proof modules into another namespace. The literal
endpoint reuses `literal_bitcoin_annex_hash`, whose tree is also the canonical
Elements `annexHash` program, and the existing generic
`nonce_elements_partial_local_spec` contract over the actual Elements program.

Both absent and present payloads are covered (one absorbed zero byte versus
prefix one plus 32 bytes), including all input context/count values and both
assertion outcomes. The full call derives entry, source copy, SHA updates,
output serialization, return/free and the original framing observations.
There is no cache-value, execution, desired-output or success premise. The
explicit `memcpy_model` and initialized SHA dispatch/counter premises remain;
general caller initialization and libc linkage are not proved by this result.
Both C endpoints use the same six inherited library assumptions.

Normal compilation passes after rebuilding unchanged stale objects under the
pinned toolchain. Fifteen theorem records and thirteen definitions are added
in two modules. The existing source checker reuses the shared literal-tree
checks and rejects thirteen further complete-contract/binding mutations.
This endpoint passed ordinary scoped acceptance with the three computed
issuance getters. Reproduce the checked scope with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_issuance_entropy,simplicity_issuance_asset,simplicity_issuance_token,simplicity_annex_hash
```

No production C, original specification, API or generation setting changed.

## Accepted local contracts: Elements tapleaf and tapbranch builders

`C.jet_elements_tap_builders_literal` supplies the complete original C calls
for `simplicity_build_tapleaf_simplicity` and `simplicity_build_tapbranch`,
against `literal_elements_build_tapleaf` and `literal_elements_build_tapbranch`.
The literal adapters reuse the accepted shared tapleaf payload and universal
SHA block bridge. Their closed tag equalities use `TapLeaf/elements` and
`TapBranch/elements`; the leaf version is 190. Branch ordering covers both
orders and equality. The Elements global environment is the actual
`jets_elements.prog`, not an identification with the SHA-only program.

The initialized frame contract retains arbitrary valid input/output cursors,
pre-existing output bits, the C return value, output encoding, prefix/cursor
preservation and external framing. The explicit `memcpy_model` premise and
initial SHA dispatch/counter and raw tag-byte relations remain. Startup from
the program's initial memory and concrete libc linkage are not discharged by
these local theorems; there is no assumed intermediate execution or digest.
The fixed host tag recipe is source-reviewed, not a general proof of the
Haskell cryptographic runtime.

Normal compilation passes for all twelve added modules. The literal Core
bridges are closed; the two public execution endpoints use only the six
inherited library assumptions. The existing source checker compares the full
shared payload trees, exact tags, actual linkage and complete contracts, and
rejects 29 further mutations. Reviewed snapshots cover 85 theorems and 45
definitions; comparison without update flags passes. Both endpoints passed
ordinary scoped acceptance (309 kernel modules, snapshot comparisons, gate
negative tests and five regenerated ASTs). Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_build_tapleaf_simplicity,simplicity_build_tapbranch
```

No production C, original specification, API or generation setting changed.

## Accepted local contracts: Elements issuance amount arrays and composite hash

The two endpoints in `C.jet_elements_issuance_amounts_hash_literal` execute
the original `simplicity_issuance_asset_amounts_hash` and
`simplicity_issuance_token_amounts_hash` cache getters against their full
literal Simplicity programs. The programs retain indexed primitive lookup,
all no/new/reissuance branches, explicit asset identifiers, confidential or
explicit amounts, byte absorption, traversal termination and finalization.
An absent issuance absorbs exactly two null bytes, rather than terminating
the traversal. The reissuance token amount remains explicit zero.

`C.jet_elements_issuances_hash_literal.elements_issuances_hash_literal_local_spec`
composes those programs with the accepted issuance range-proof and
blinding-entropy programs in canonical order, absorbs their 128 bytes and
finalizes, then proves the complete original composite getter. Its universal
program bridge retains the actual `one word8` program in blinding entropy;
it does not substitute a scribed constant.

All three local contracts retain `application_jet_local_spec_sep`, the actual
Elements program/environment, initial canonical cache correspondence at
transaction offsets 472, 504 and 600 in the 760-byte transaction, arbitrary
writable frame contents/cursors and complete return/output/framing behavior.
No execution or final-output premise and no extra libc model is added.
Establishment of the initial caches by actual callers, general environment
and evaluator admissibility and host-runtime fidelity remain separate.

The four new modules compile through the normal project target. The public
execution endpoints use only the six inherited library assumptions; literal
program bridges are closed. The existing source checker reuses the verified
SHA, issuance-calculation, serializer and traversal checks and rejects forty
further mutations of routing, amount selection, payload ordering, widths,
catalog bindings, offsets and complete C contracts. Reviewed snapshots cover
28 theorems and 23 definitions; comparison without update flags passes.
All three endpoints passed ordinary scoped acceptance (392 kernel modules,
reviewed snapshot comparisons, gate negative tests and five regenerated ASTs).
Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_issuance_asset_amounts_hash,simplicity_issuance_token_amounts_hash,simplicity_issuances_hash
```

No production C, original specification, API or generation setting changed.

## Candidates: Elements transaction and signature hashes

`elements_tx_hash_literal_local_spec` in `C.jet_elements_tx_hash_literal`
proves the original transaction-cache getter against the complete literal
`txHash` program: Version/LockTime, then the input/output/issuance/surjection
hash tuple in canonical order, then the input-UTXO hash and finalization.
The proof composes the existing component results and shared byte-list
absorption/finalization lemmas. Its initial representation is
`hash_getter_rep elements_tx_hash_of 0 632 760`.

`elements_sig_all_hash_literal_local_spec` in
`C.jet_elements_sig_all_hash_literal` proves the original direct txEnv-cache
getter against the complete literal `sigAllHash` program: both copies of
GenesisBlockHash, the transaction and tap-environment hashes, CurrentIndex,
and finalization. It uses the new shared direct-field getter execution proof,
whose initial relation is `elements_direct_hash_rep elements_sig_all_hash_of 48`.
The actual Elements program and the original 88-byte txEnv layout are retained.

Both keep `application_jet_local_spec_sep`, arbitrary valid frame cursors and
old output contents, actual C execution/return, output encoding, prefix/cursor
preservation and external framing. The initial cache correspondence remains
explicit. Actual builder establishment and general caller/evaluator
admissibility are not proved by these local results. No intermediate execution,
output premise or extra libc model is added. The literal program bridges are
closed; the C endpoints use only the six inherited library assumptions.

All three modules compile through the normal project target. The existing
source checker compares the full canonical composition trees, primitive
bindings, word encodings, direct-field representation and complete C boundaries,
and rejects 26 further mutations. Reviewed snapshots cover 13 theorems and
12 definitions in the three modules; comparisons without update flags pass.
Both entries passed ordinary scoped acceptance: 406 kernel modules, 274
assumption modules, 299 contract modules, the gate negative tests and all five
regenerated AST comparisons. Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_tx_hash,simplicity_sig_all_hash
```

No production C, original specification, API or generation setting changed.

## Support only: computing Elements issuance hash

Seven new modules compile in the normal project; reviewed snapshots cover 30
theorems and 25 definitions. They provide the canonical indexed program and
literal bridge (reusing issuance calculations and the actual one8 blinding
program), all-index semantics, actual asset/token-ID compound copies, explicit
zero amount construction, all 32 zero-byte stores and the eight-local function
entry/frame copy. Closed AST equalities match the actual literal initializers.
The shared indexed wrapper is adapted to the actual t'3 result temporary, with
a closed equality specializing it to the existing t'2 wrapper.

These are support results, not a complete C-to-program equivalence for
`simplicity_issuance_hash`. Its three payload paths and their final frame/free
composition remain to be proved; no registration or additional accepted jet
is claimed. See `JET_PROOF_BACKLOG.md` for the next boundary.

## Accepted: computing Elements input hash

The six support modules compile in the normal project, with reviewed snapshots
covering 24 theorems and 16 definitions. The new `jet_elements_single_input_jet`
and `jet_elements_single_input_literal_jet` add two theorems and two definitions.
`elements_single_input_hash_literal_local_spec` proves the whole original
`simplicity_input_hash` against the literal four-primitive `inputHash` program:
index/tag, private SHA initialization, optional pegin, outpoint, index/sequence,
optional annex, finalization, serialization, return and frees, plus the
out-of-range skip branch. It retains arbitrary valid frame cursors, unknown old
output contents, prefix/cursor preservation and external framing.

The initial relation describes the actual input fields and their raw primitive
meaning, plus SHA readiness. Optional hashes require payload words only when
present. Intermediate field loads are derived through the actual SHA calls;
neither those calls nor the desired final digest are assumed. The general
streaming bridge handles all 42/74/106-byte messages.

The literal bridge is closed; the C endpoint retains the six inherited library
assumptions and explicit `memcpy_model`. The existing source checker compares
the full Core tree, primitive routes, initial representation and public boundary,
rejecting 34 new mutations. Ordinary scoped acceptance passed: build, kernel
checking of 434 modules, 303 assumption records, 327 public contract records,
gate negative tests and regeneration of all five ASTs:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_input_hash
```

Builder/caller establishment, libc linkage and evaluator admissibility remain
separate obligations. No production C, original specification/domain/identity,
API or generation setting changed.

## Accepted: computing Elements output hash

`C.jet_elements_output_hash_literal.elements_output_hash_literal_local_spec`
proves the whole original `simplicity_output_hash` against the literal
primitive-bearing `outputHash` program. It includes the index/tag, SHA
initialization, actual asset/amount/nonce calls, script and range-proof digest
absorption, finalization, serialization and frees, and the out-of-range skip
branch. The indexed-frame skeleton and general streaming bridge are reused.

The initial relation describes the actual 248-byte output array: asset at 0,
amount at 104, nonce at 144, script digest at 180 and range-proof digest at 68,
plus SHA readiness. A missing nonce requires only its prefix, not initialized
payload words. Messages span 107, 131, 139 or 163 bytes. No intermediate C call
or desired final digest is assumed. Arbitrary valid frame cursors, unknown old
output contents, cursor/prefix preservation and external framing are retained.

All six modules compile in the normal project. Reviewed snapshots cover 22
theorems and 12 definitions; the literal bridges and parametricity are closed.
The C endpoint retains the six inherited library assumptions and explicit
`memcpy_model`. The existing source checker compares the complete Core tree,
Transaction amount route, initial representation and full public boundary,
rejecting 30 new mutations. Ordinary scoped acceptance passed: build, kernel
checking of 444 modules, 313 assumption records, 337 public contract records,
gate negative tests and regeneration of all five ASTs:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_output_hash
```

Caller/builder establishment, libc linkage, evaluator admissibility and the
remaining canonical-domain/host limits are separate obligations. No production
C, frozen specification/domain/identity, API or generation setting changed.

## Accepted: computing Elements input UTXO hash

`C.jet_elements_input_utxo_hash_literal.elements_input_utxo_hash_literal_local_spec`
proves the whole original `simplicity_input_utxo_hash` against the literal
primitive-bearing `inputUtxoHash` program: index/tag, context initialization,
actual confidential asset/amount hashing, script digest, finalization,
serialization and frees, plus the out-of-range skip branch. Arbitrary valid
frame cursors, unknown old output contents, prefix/cursor preservation and
external framing are retained.

The initial `elements_input_utxo_hash_rep` relates the actual 544-byte input
array, its UTXO at offset 136 and asset/amount/script fields to the raw primitive
environment, and includes SHA readiness. No intermediate C execution or desired
final digest is assumed. Builder/caller establishment and `memcpy_model` linkage
remain obligations. The private SHA chain uses the existing general streaming
lemma for both 74-byte explicit-amount and 98-byte confidential-amount messages.

All four modules compile through the normal project. Reviewed snapshots cover
23 theorems and eight definitions and compare without update flags. The literal
bridge and parametricity are closed; the C endpoint retains the six inherited
library assumptions and explicit `memcpy_model`. The existing source checker
compares the full Core tree, Transaction amount route, public C boundary and
initial representation, rejecting 24 new mutations. Ordinary scoped acceptance
passed: build, kernel checking of 428 modules, 297 assumption records, 321 public
contract records, gate negative tests and regeneration of all five ASTs:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_input_utxo_hash
```

Production C, frozen specifications/domains/identities, API contracts and
generation settings are unchanged.

## Accepted: computing Elements issuance hash

`C.jet_elements_single_issuance_literal_jet.elements_single_issuance_hash_literal_local_spec`
proves the whole original `simplicity_issuance_hash` against its literal
primitive-bearing program. It includes all eight actual allocations, source
frame copying, both index branches, issuance-kind dispatch, every active payload,
SHA initialization/finalization, serialization and actual frees. The initial
relation describes fields/cache correspondence and SHA readiness, never an
assumed intermediate execution or desired final digest. Inactive union arms
are not required. Arbitrary valid cursors, unknown old output bits and framing
are retained.

The canonical Core-tree, initial representation and full C-boundary source
checks reject 50 additional mutations. Ordinary scoped acceptance passed:
475 kernel modules, 344 assumption records, 368 contract records, gate negative
tests and all five regenerated ASTs:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_issuance_hash
```

The endpoint retains the six inherited library assumptions and explicit
`memcpy_model`. Accepted local-contract coverage is 495/533, with 136 entries
conditional on that model. Caller/cache establishment, libc linkage, evaluator
admissibility and remaining source/domain/configuration limits remain separate.
Production C, frozen specifications, API contracts and generation settings are
unchanged.

## Accepted: original affine curve check

`C.jet_secp_curve_local.ge_is_on_curve_literal_local_spec` proves the whole
original `simplicity_ge_is_on_curve` against the literal canonical Core tree.
It derives public allocations and the source-frame copy, both real coordinate
reads and their zero infinity flag, all six arithmetic calls inside the original
validity helper, the actual bit write, successful return and all private/public
frees. The public contract covers every Word256 input pair with ordinary valid
frames: no canonical-input, on-curve, initialized-output or extra libc premise.

The existing predicate source gate checks the full projective/affine tree,
catalog wiring, constant and shared cube/one ports, and exact public boundary.
Its suite rejects 62 mutations, including 28 new curve cases. On `ad63ab2b`,
ordinary scoped acceptance passed: 341 kernel modules, 280 assumption records,
295 contract records, gate negative tests and all five AST regenerations:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_ge_is_on_curve
```

The endpoint retains the same six inherited library assumptions and no extra
libc model. Accepted local-contract coverage is 496/533 (360 without an extra
libc premise; 136 conditional on `memcpy_model`). Production C, frozen
specifications/domains/identities, API contracts and generation settings are
unchanged. This completes this jet, not the broader every-jet goal.

## Accepted: original guarded projective X-equivalence

`C.jet_secp_x_equiv_local.gej_x_equiv_literal_local_spec` proves the original
`simplicity_gej_x_equiv` against the full literal canonical Simplicity tree,
not an assumed numeric predicate. It derives the frame/field/point allocations,
by-value source-frame copy, four actual input reads in `(q,((x,y),z))` order,
the infinity accessor and both short-circuit branches, the complete comparison
helper, bit write, successful return and all private/public frees.

The standard local-frame contract covers all four Word256 inputs, including
zero Z, with one writable output bit. There is no finite-point, on-curve,
canonical-input, zero-initialized-output, desired-result, intermediate-execution
or extra libc-model premise. The final theorem retains the six inherited
library assumptions. The selected multiply/square proofs are reused; the
alternative public field registrations remain excluded.

On `0b694db8`, ordinary scoped acceptance passed with unchanged audit inputs:
318 kernel modules, 257 assumption modules, 272 contract modules, gate negative
tests and all five regenerated ASTs. The extended predicate source suite rejects
87 mutations, including 25 new X-equivalence/dependency cases. Reproduce with:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_x_equiv
```

Accepted local-contract coverage is 497/533: 361 without an extra libc premise
and 136 conditional on `memcpy_model`. The remaining 36 declarations and the
shared fidelity/domain/caller obligations are not completed by this result.
Production C, original specifications/domains/identities, API contracts and
generation settings are unchanged.

## Accepted: original field square-root jet

`C.jet_secp_root_local.fe_square_root_literal_local_spec` proves the complete
original public `simplicity_fe_square_root` against the fixed literal
Simplicity program. It covers arbitrary Word256 inputs, general valid frame
cursors and word crossings, arbitrary unrelated destination contents, and both
sum-result branches. It derives all actual helper calls and their storage
invariants, the addition chain and eleven squaring loops, comparison, tag and
conditional payload/padding, integer-to-bool conversion, successful public
return, twelve helper allocations/frees and three outer allocations/frees.
No mathematical square-root, initialized-result, intermediate execution,
curve-membership or extra libc-model premise is added. The same six inherited
execution assumptions remain.

The proof inputs committed at `fd51b860` passed ordinary scoped acceptance:
355 kernel modules, 294 assumption modules, 309 contract modules, gate negative
tests and all five AST regenerations, with identical audit inputs before and
after the run. The existing source-correspondence gate checks the canonical
catalog, exact tower/candidate/check ports and complete public contract, and
rejects eighteen targeted mutations. Reproduce with Coq 8.17.1 and the prepared
dependencies:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_fe_square_root
```

Accepted local-contract coverage is 501/533: 365 without an extra libc premise,
136 conditional on `memcpy_model`, and 32 declarations remaining. Shared
fidelity/domain/caller obligations remain unfinished. Production C, original
specifications/domains/identities, API contracts and generation settings are
unchanged; the every-jet goal is not complete.

## Accepted: original projective curve check

`C.jet_secp_gej_curve_local.gej_is_on_curve_literal_local_spec` proves the
whole original `simplicity_gej_is_on_curve` against the existing literal
canonical Simplicity program. It derives public entry, the by-value frame copy,
all three actual coordinate reads, the complete original validity helper and
its nine arithmetic calls, the boolean-typed bit write, successful return and
all private/public frees. The selected square and multiplication proofs are
reused; the alternative public field registrations stay excluded.

The standard local contract covers arbitrary Word256 X/Y/Z inputs, including
zero Z, with one writable output bit and ordinary valid frame/cursor layouts.
There is no finite-point, on-curve, canonical-input, initialized-output,
desired-result, intermediate-execution or extra libc-model premise. The final
theorem retains the same six inherited execution assumptions.

On `408a485c`, ordinary scoped acceptance passed with unchanged audit inputs:
321 kernel modules, 260 assumption modules, 275 contract modules, gate negative
tests and all five regenerated ASTs. The existing predicate correspondence
suite now rejects 95 mutations, including eight new public-projective cases.
Reproduce from the repository root with the baseline Coq 8.17.1 and prepared
jet dependencies:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_is_on_curve
```

Accepted local-contract coverage is 498/533: 362 without an extra libc premise
and 136 conditional on `memcpy_model`. The remaining 35 declarations and
shared fidelity/domain/caller obligations remain unfinished. Production C,
original specifications/domains/identities, API contracts and generation
settings are unchanged.

## Accepted: original projective point doubling

`C.jet_secp_double_local.gej_double_literal_local_spec` proves the whole
original `simplicity_gej_double` against the literal canonical Simplicity
program. It derives entry, source-frame copy, coordinate reads, the real
NULL-rzr doubling dispatch, all fifteen arithmetic calls, unconditional XYZ
serialization, successful return and all local frees. The selected field
multiplication and square proofs are reused, not registered again.

The standard local contract covers every Word256 X/Y/Z triple and ordinary
valid frame/cursor layouts, including incoming infinity and finite inputs
with Y=0. No curve-membership, nonzero-coordinate, canonical-input,
initialized-output, intermediate-execution or extra libc-model premise is
added. The six inherited execution assumptions are unchanged.

On `23b1ca34`, ordinary scoped acceptance passed with unchanged audit inputs:
355 kernel modules, 294 assumption modules, 309 contract modules, gate negative
tests and all five regenerated ASTs. The existing point-program correspondence
suite rejects 27 targeted doubling mutations. Reproduce with the baseline
Coq 8.17.1 and prepared jet dependencies:

```sh
bash Coq/check-jets.sh --accept --jets=simplicity_gej_double
```

Accepted local-contract coverage is 499/533: 363 without an extra libc premise
and 136 conditional on `memcpy_model`. The remaining 34 declarations and
shared fidelity/domain/caller obligations remain unfinished. Production C,
original specifications/domains/identities, API contracts and generation
settings are unchanged.

## Accepted: original mixed projective/affine addition

`C.jet_secp_mixed_local.gej_ge_add_literal_local_spec` proves the original
public `simplicity_gej_ge_add` against the complete fixed literal Simplicity
program. It derives the by-value frame copy, both actual readers, the original
in-place NULL-rzr helper on all branches, actual XYZ writing, successful return,
all private helper allocations/frees and all three outer allocations/frees.
It reuses the selected field multiply/square and accepted doubling proofs.

The standard local contract retains arbitrary Word256 coordinates, including
zero/off-curve inputs, general valid cursors, word crossings and unrelated
initial destination contents. No canonical-input, curve-membership,
intermediate-execution, output-value or extra libc-model premise is added.
The six inherited execution assumptions are unchanged.

The proof inputs committed at `63aa1380` passed ordinary scoped acceptance:
431 kernel modules, 370 assumption modules, 385 contract modules, negative
tests and all five regenerated ASTs, with identical audit inputs before and
after the run. The existing point correspondence gate checks the canonical
catalog, all four addition ports and the exact mixed-addition public contract;
it rejects 13 addition-port and eight public mixed-addition mutations.
Reproduce with Coq 8.17.1 and the prepared dependencies:

```sh
JOBS=2 bash Coq/check-jets.sh --accept --jets=simplicity_gej_ge_add
```

Accepted local-contract coverage is 500/533: 364 without an extra libc premise,
136 conditional on `memcpy_model`, and 33 declarations remaining. Shared
fidelity/domain/caller obligations remain unfinished as well. The separate
extended jet `simplicity_gej_ge_add_ex` has a reported ratio normalization
mismatch; see [JET_SECP_RATIO_MISMATCHES.md](JET_SECP_RATIO_MISMATCHES.md).
It is now registered only through
`C.jet_secp_mixed_ex_local.gej_ge_add_ex_literal_local_spec_off_mismatch`: the
unchanged literal contract on every input outside the exactly characterized
mismatch set (equal-point branch with an unreduced input Y word). The
whole-domain theorem `gej_ge_add_ex_normalized_local_spec` states the output
for every input. `jet-coverage.py` counts this entry separately ("proved only
outside a reported specification mismatch") and prints the mismatch on every
run. Production C, original specifications/domains/identities, API contracts
and generation settings are unchanged. Reproduce with
`bash Coq/check-jets.sh --accept --jets=simplicity_gej_ge_add_ex`.
