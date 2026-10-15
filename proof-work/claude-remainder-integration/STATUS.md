# Claude remainder: integration completed, 2026-10-14

Further follow-up: the previously deferred secp frame-constructibility source
is now imported after checked replacements for all four unchecked conversions
found in its normal-tree dependencies. The selected 138-module closure passes
independent kernel checking, with no registry change. See
[`secp-checked-conversions`](../secp-checked-conversions/README.md). The
exclusion notes below record the earlier snapshot, not the current repair.

Follow-up: the previously excluded linked families below have now been
repaired, independently audited and integrated. See
[`linked-repair/STATUS.md`](../linked-repair/STATUS.md). Its three reviewed
source batches add 28 files (26 `.v` sources), with no normal-registry change.
The exclusions and preservation hashes in this earlier report describe the
original non-linked phase; the linked installation ledgers now compose with
its post-installation check. Secp constructibility was initially deferred;
the further checked-conversion repair above now resolves that exclusion.

Reviewed snapshot: `claude/shared-obligations` at
`30404face45383153528f36d915de6d7df11f3f4`. Target:
`feat/jet-equivalence`; pre-review HEAD `3f20b6db`. All commits are signed
and local. Nothing was pushed; Claude's active branch/worktree was preserved.

## Installed batches

| Batch | New files | Recursive kernel check | Scope |
| --- | ---: | --- | --- |
| Common / Elements candidates | 93 | exit 0; 634-module C/support closure | memcpy references and relative consistency, memcmp model/reference/word bridge, rsort contract definition, snapshot frame executability, Elements helpers/contracts/constructibility and forward-memory token-amount candidates |
| Bitcoin readiness / startup | 8 | exit 0; 432-module C/support closure | cached-environment relation readiness, nullable tappath readiness, readable raw-environment existence, initialization implication and startup preservation |
| Elements SHA / startup | 16 | exit 0; 288-module C/support closure | SHA proofs in the Elements program, annex/tapleaf/tapbranch helpers/contracts, startup preservation and fresh-frame execution |
| Elements environment | 59 | exit 0; 356-module C/support closure | actual environment translation unit, taproot/setup/free callers, parsing and copyOutput, confidential/issuance hashing, fee helpers, explicit unresolved sort contract |
| Maintenance generators | 9 | generation check only, not a kernel proof | 32 exact ports, 17 generated modules; 31-constructor signature comparison; six passing anti-admission fixtures |

Total: **185 new source/tool files**, including **169 `.v` sources**. These
are file counts, not new accepted jets. Duplicate dependencies were checked
in each affected program but installed only once. The frame executability
registry describes Claude's older registration snapshot, not a dynamically
updated claim about every currently registered jet.

Source commits: `0ef7b8df` (common/candidates), `a40c1a25` (Bitcoin),
`7a80bd64` (Elements SHA), `6d765954` (Elements callers), `a0449b9d`
(generation tools). Earlier commits in this review contain the tooling and
durable review receipts.

Each proof batch regenerated its applicable production/reference AST,
compiled new modules with pinned Coq 8.17.1/CompCert 3.14, printed complete
theorem types/definitions/assumptions, and recursively checked its roots and
dependencies without unsafe flags. Every batch passed 13 evidence-corruption
and six lexical escape-hatch fixtures. Receipts are in each batch directory;
`README.md` describes replay and post-installation verification.

The reports cover 1,066 / 582 / 170 / 804 results respectively, including
inherited and program-specific supporting lemmas. They are not counts of
independent new jet-equivalence proofs. All dependencies are within the six
previously inherited assumptions, or the additionally documented two
external-function property assumptions needed by forward-memory proofs.
The original registry's assumption policy was not changed.

## What was intentionally not integrated

1. `Coq/linked/` and `Coq/bitcoin-env-linked/`: three definition-list
   equality proofs use unchecked casts:
   `jet_linked_program.v:27`, `jet_linked_sha_program.v:27`, and
   `jet_bitcoin_env_linked_program.v:28`. Their consumers remain excluded.
   Replace those casts with checked proofs and independently audit the
   complete linked closures before importing. CompCert's `Axioms.proof_irr`
   inheritance also needs an explicit linking-only review. A linked-program
   proof must never relabel the unchanged original program's libc premise
   as discharged.
2. `jet_frame_constructible_secp.v`: depends on the existing main
   `C/jet_secp_fe_nv.v:51`, which also uses an unchecked cast. This is a
   source-policy finding, not a claim that its equality is false. Repair
   and check the normalization lemma before integrating the extension.
   Existing main secp work was left untouched.
3. Original startup proofs already transported into main: no redundant
   second proof family was added unless a new program-specific startup
   dependency required it.
4. Broad build/audit scripts and old registry generators: the isolated
   copied-tree driver replaces their shared-tree/symlink workflow. Registry
   generators should be refreshed against the live registry before reuse.
   Old prose/receipts making broader or stale claims were not substituted
   for the main documentation.
5. Uncommitted `simplicity-shared` work, including the `copyInput` experiment:
   not part of the frozen snapshot, not imported or altered.

## Proof boundaries and next work

Registered coverage is unchanged: **364/533**, including **104 conditional
on `memcpy_model`**. No new module was added to `_CoqProject.jets`, public
jet registries, contract snapshots or coverage. The all-jets goal remains
unfinished; this integration does not resume or complete the paused app goal.

- Elements candidate proofs are against the existing Coq specification port.
  The remaining 28 primitive semantic clauses need canonical Haskell source
  review before candidate jets can be admitted. Signature/generation checks
  do not establish semantic correspondence.
- `rsort_model` is a definition only. `sumFees` keeps `memcmp_model` and a
  sortedness premise. `copyInput`, radix-sort implementation verification,
  and the whole Elements mallocTransaction body remain open. Issuance
  helpers' C-level register/hash results still need specification bridges.
- Bitcoin initialization is an implication from successful `Genv.init_mem`,
  not a new existence theorem for that unit. Startup preservation requires
  separation from the relevant globals. Supplied raw transaction-id bytes
  are copied, not computed or validated. The nullable tappath result covers
  empty paths; the legacy readiness theorem retains its nonempty-path bound.
- Reference memcpy proofs/model consistency do not identify the original
  abstract external libc semantics. The plain byte loop additionally needs
  initialized data bytes; do not strengthen existing frame contracts to
  force it through.
- Caller-to-original-jet-program transport and the actual evaluator/dispatch
  execution theorem remain open. No full runtime-driver or alternate build
  configuration claim is made.

Recommended next order: canonical Elements semantic review and narrow
admission batches; checked-cast repairs and linked-program audits; remaining
Elements caller/issuance bridges and transaction-builder body; driver
composition. Preserve the existing secp/range work while doing so.

## Preservation and audit status

Post-installation verification passed: each source addition is byte-for-byte
bound to the frozen snapshot, all existing Coq/C/Haskell inputs are unchanged,
and all stored candidate artifacts/terminal results remain intact.

Original staged patch SHA-256, unchanged:
`f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.
Post-installation audit-input SHA-256:
`503efeef4f5843f420ec87dccbb90ba1c53eb0a7a51ff708d4b540fa5244ff3b`.

These are four independently checked additive closures, **not** a new
combined full-normal-worktree `check-jets.sh --accept` receipt. Existing
dirty/staged metadata and untracked proof experiments were preserved.

Whitespace lint (`git diff --check`) is not clean: the original generated
ASTs and proof templates contain trailing spaces and extra EOF blank lines.
Those bytes were intentionally preserved to keep exact regeneration and
frozen-source provenance. This is a cosmetic lint limitation, not a failed
Coq build/kernel check; no other lint diagnostic category was observed.
