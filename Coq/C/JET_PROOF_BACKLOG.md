# Proof consolidation and remaining obligations

Current consolidation preserves every useful source identified in the known
branches, worktrees and 84-file scratch inventory. Accepted sources remain in
the active Coq tree. Unaccepted corrections, candidate registrations, helper
sources and review witnesses are versioned in `../../proof-work/`, outside the
accepted build. Consolidation is source preservation, not proof acceptance.

The accepted inventory is **349/533**, with **104** results conditional on
the explicit original `memcpy_model`. The inherited fidelity review is still
**partial**. `JET_INHERITED_REVIEW.md` is the authoritative eight-criterion
assessment; compilation, snapshots and absence of admissions do not complete it.

## Existing accepted correction and review evidence

The frame exclusive-end correction is accepted as `063e3b04`, ; its historical
audited input fingerprint is recorded in
`JET_CONSOLIDATION_2026-10-06.json`. `JET_SHARED_MEMORY_REVIEW.md` records its
definition/domain review. The production C, canonical Haskell, accepted ASTs,
canonical specifications and public execution/output/framing conclusions
are retained by the repaired range integration. The support-interface and
frozen-predicate changes are reviewed in
`../../proof-work/range/RANGE-CONTRACT-REVIEW.md`.

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

1. The repaired same-block range correction is integrated on
   `codex/range-integration`: 149 exact reviewed files, complete acceptance
   and a matching proof-input fingerprint. Its original 20 patches remain
   historical recovery material. See `../../proof-work/range/RECONCILIATION.json`,
   `RANGE-CONTRACT-REVIEW.md` and `JET_ACCEPTANCE.md`. The broader inherited
   endpoint/evaluator/domain/fidelity obligations remain open.
2. Finish analogous address/representation and constructor-domain review, plus
   every pending registered chain to the literal canonical specification. The
   inherited matrix retains 284 registered rows needing more evidence. Do not
   infer fidelity from names, compilation, generated snapshots or admission
   scans. Keep domain restrictions and execution/output assumptions explicit.
3. Complete remaining raw Bitcoin getter and SHA/composed-hash boundary review
   identified in `JET_INHERITED_REVIEW.md`.

## Integrated extensions and pending support

- Field odd/zero: 18 proof modules, two source checkers and registration
  changes are integrated in `cafb9b31`, with independent full acceptance.
  The exact original candidate patch under `../../proof-work/secp-field-predicates/`
  remains historical recovery material. The extension adds 43 support results,
  including two public results; inherited domain/fidelity review remains open.
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
