# Proof consolidation and remaining obligations

Current consolidation preserves every useful source identified in the known
branches, worktrees and 84-file scratch inventory. Accepted sources remain in
the active Coq tree. Unaccepted corrections, candidate registrations, helper
sources and review witnesses are versioned in `../../proof-work/`, outside the
accepted build. Consolidation is source preservation, not proof acceptance.

The accepted inventory remains **347/533**, with **104** results conditional on
the explicit original `memcpy_model`. The inherited fidelity review is still
**partial**. `JET_INHERITED_REVIEW.md` is the authoritative eight-criterion
assessment; compilation, snapshots and absence of admissions do not complete it.

## Existing accepted correction and review evidence

The frame exclusive-end correction is accepted as `063e3b04`, and the exact
audited input fingerprint remains the one recorded in
`JET_CONSOLIDATION_2026-10-06.json`. `JET_SHARED_MEMORY_REVIEW.md` records its
definition/domain review. The production C, canonical Haskell, accepted ASTs,
public theorem statements, conclusions and assumption sets are unchanged by
this source-archive consolidation.

The original-C normalization result and its full public lifecycle are already
integrated. The scope of its canonical review is recorded in
`JET_FIDELITY_REVIEW.md` and `JET_ACCEPTANCE.md`.

Prior full-shift family review inspected the literal Haskell catalog and
recursive programs. The twelve `full_left/right_shift_64_{1,2,4,8,16,32}`
contracts retain actual calls, output, prefix, cursor and memory observations,
deriving wide copying from initial frames under explicit `memcpy_model`.
The canonical `Programs.Word.full_shift` dispatch through `compareVectorSize`
and `vectorComp vector2` selects the corresponding `full_left/right_shift1`
instance at depth log2(N)-log2(M). The source gate compares catalog bindings,
literal recursive combinators and concrete Coq specialization for both narrow
and wide families. These facts supplement kernel checking; they do not resolve
the remaining shared-domain or exhaustive per-entry review. See
`JET_FIDELITY_REVIEW.md` and `check-fullshift-specification.py`.

The 26 existing Bitcoin local-contract reviews remain scoped evidence in the
TimeLock/value, simple-getter and indexed/current review reports. Their exact
boundary diagnostic sources are now in `../../proof-work/review-witnesses/`.

## Corrections and inherited review, before additional coverage

1. Complete the same-block range correction. Its 19 unique unintegrated commits
   are preserved as a patch series in `../../proof-work/range/`. The whole
   consumer build fails at `jet_full_multiply8_layout.v:122`; copy and symbolic
   executor consumers retain the old separation interface. Prior scoped kernel
   receipts and the 12 additional built/reviewed modules do not accept the full
   candidate. Repair consumers, review actual definitions/conclusions/hypotheses
   and snapshot differences, and finish independent acceptance.
2. Finish analogous address/representation and constructor-domain review, plus
   every pending registered chain to the literal canonical specification. The
   inherited matrix retains 284 registered rows needing more evidence. Do not
   infer fidelity from names, compilation, generated snapshots or admission
   scans. Keep domain restrictions and execution/output assumptions explicit.
3. Complete remaining raw Bitcoin getter and SHA/composed-hash boundary review
   identified in `JET_INHERITED_REVIEW.md`.

## Additional coverage and support, preserved but unaccepted

- Field odd/zero: 18 proof modules, two source checkers and pending
  registration/snapshot changes are in the exact candidate patch under
  `../../proof-work/secp-field-predicates/`. The candidate contains 43 support
  results including two public results. Actual contract/snapshot review and
  independent acceptance on the selected integration target remain necessary.
- Scalar/uint128: 22 complete helper sources and the historical literal-source
  checker are in `../../proof-work/scalar-u128/`. Eighteen match historical
  compiled/kernel receipts. Four require fresh verification, including a known
  prior compilation failure in `scalar_overflow_flags`. Subsequent shift64,
  scalar-reduce, numeric get-b32 and scalar-set-b32 helper work is preserved;
  the earlier executor diagnosis is not the current final stopping point.
  Canonical reduction/limb correspondence, read/write-scalar calls and complete
  public frame lifecycle chains remain open.
- SHA: the complete initialization/preservation source is preserved under
  `../../proof-work/sha-support/`. Its startup facts come from original global
  initializers. Fresh kernel/contract review and discharge of those facts at
  all consuming public contracts remain open.

Each candidate manifest distinguishes historical evidence, complete source and
fresh acceptance. `python3 proof-work/manage.py` from the repository root checks
hashes and exact candidate-tree replay; it does not accept proofs.

## Removed transient material

`JET_PROGRESS.md` was a chronological continuation journal with superseded
pending/running checkpoints. Its durable status and source pointers are now
here and in the proof-work manifests; the full historical journal remains in
Git at `dcc600b7`. Its active references have been updated. The obsolete initial
prototype worktree is removed after putting its four untracked files in local
Trash for recovery. Generated artifacts, caches, raw logs and superseded open
goal diagnostics remain local.
