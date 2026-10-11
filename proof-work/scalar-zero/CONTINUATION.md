# Scalar-zero integration continuation

## Completed proof milestone

Signed local commit `0ae8b786` contains the complete original-C scalar-zero
local contract and its checked supporting chain. OriginalC compilation,
18-type/three-definition untruncated review, exact dependencies (9 closed,
2 classical-only, 7 execution), independent whole-chain kernel session 14762,
literal source checks and 23 in-memory evidence/canonical/public-contract
negative fixtures all passed. This is formal C-to-literal proof evidence, not
mathematical-only specification correctness.

## Isolated candidate, not accepted coverage

- Immutable accepted baseline: `/tmp/jet-ge-negate-accept.5mtyZa`, terminal
  full acceptance session 13065, fingerprint
  `e07f8b9914471ba13bb9e67d3a676b35667b5f6881f48e30e985f2325d88ce7d`.
- Scalar candidate: `/tmp/jet-scalar-zero-accept.smyVL2`.
- Assembly receipt: `ASSEMBLY.json`. Its 38 modules are the checked dependency
  closure of scalar_zero_local_spec plus canonical parametricity, not every
  exploratory scalar module. Transport is only `OriginalC.` to `C.`, with
  fresh compilation required. Two compatibility export wrappers resolve to
  existing C modules without overwriting them. All 986 inherited .v sources
  and initial snapshots remain byte-identical; eight metadata changes are
  exact append-only inventory extensions and narrow gate/coverage hooks.
- Added audit inventory: 178 results, 120 definitions (including local
  definitions and scalar_bind's Fixpoint), four standalone source-gate/test
  scripts. One provisional coverage row, scalar_is_zero, is added.
- Source scan, coverage parser/tests, literal gate, four public-contract
  mutations and eleven canonical/recursive mutations passed (session 55900
  terminal 0). Candidate inventory reports 356/533 **provisionally**; it is
  not normal full acceptance or checkout integration. Main remains 351/533.
- Assembly baseline and eight in-memory assembly mutations passed (session
  45501 terminal 0). No build/audit inputs were edited by these fixtures.

## Namespace-C normal build — completed

Fresh namespace-C normal build session **58889** exited **0**:

```sh
export PATH=/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin:$PATH
ulimit -S -s 65520
cd /tmp/jet-scalar-zero-accept.smyVL2/Coq
JOBS=1 bash build-jets.sh -j1 > ../scalar-normal-build.log 2>&1
```

All 38 new modules compiled, including the complete public scalar_zero_local_spec
and both canonical parametricity results. Log hash:
`860121f930c266aedf04dc7d8a16471f932a51b56e723314ff17830781af9db6`.
Initial assembled candidate fingerprint before snapshot generation:
`ccb4fb0bf13a71d52c58539ff02e3e8ad2422366ed6cf6bf6ce83da9a818a699`.

**Snapshot generation/review** is not full acceptance:

- contracts session **51658** exited **0**; independent high-depth supplement
  session **9078** exited **0**. The 178 new types and 120 definitions were
  reconciled; all inherited contract records remain byte-identical. All 178
  types and 113 non-tree definitions have untruncated supplements. Seven tree
  prints remain diagnostic, with actual source/run/shape proofs required.
  See `NORMAL-CONTRACT-REVIEW.json` and archived driver. Eight in-memory
  contract fixtures passed (session **81607**, exit **0**).
- assumptions session **29261** is still running,
  `bash audit-jet-assumptions.sh --update`, log
  `/tmp/jet-scalar-zero-accept.smyVL2/scalar-normal-assumption-generation.log`.

Retain/poll session 29261; do not regenerate it. No proof, canonical
specification or infrastructure inputs may change during this audit.
Generation success does not authorize full acceptance before diff review.

## Next checks

1. After terminal snapshot-generation success, reconcile all 178 added
   dependency sets with their previously
   reviewed OriginalC reports and preserve all 4055 baseline sets.
   `review-normal-assumptions.py` is prepared for that check, not yet run on
   terminal generated output. It verifies the candidate's sources/infrastructure
   and compares each exact set with hash-pinned OriginalC reports.
2. Review full types/definitions against the OriginalC evidence modulo only
   the explicit namespace transport. The 120-definition inventory deliberately
   includes local aliases omitted from older partial inventories. Normal
   printing can truncate execution trees or unary numerals: produce bounded
   high-depth supplements and inspect every remaining non-diagnostic term;
   ellipsis-fragment matching does not certify omitted terms. Retain formal
   run/shape proofs for large diagnostic execution trees.
   The present normal/deep printing reconciliation has passed, including exact
   disambiguation of the inherited and new `u128_field` definitions without
   stripping namespaces. Reproduce with `review-normal-contracts.py` and
   `test-normal-contracts.py`; both pin the reviewed driver/output hashes.
3. Preserve inherited snapshots except explicitly inspected printing-context
   qualification changes. Re-run source, registry, assumptions and contract
   negative fixtures. Confirm all unsafe kernel categories remain empty.
4. Only after reviewed snapshots, run `JOBS=1 bash check-jets.sh --accept`
   with `JET_C_REPO=/Users/brenorb/code/PROJECTS/BLOCKSTREAM/simplicity`, pinned
   toolchain/stack and AST inputs. No update/no-build flags on acceptance.
   Freeze all inputs, save session/final exit/log hash/fingerprint. Never
   relabel pending checks as successful coverage.
5. Reconcile accepted candidate with dirty checkout registries separately.
   Preserve staged/unstaged SHA and other unrelated work. Main 351, isolated
   affine 355 and provisional scalar 356 are different states.

`assemble-candidate.py --verify` checks the **initial assembly** including
unchanged baseline snapshots. After generating candidate snapshots it will
intentionally reject those changed snapshots. At that stage retain its source
and infrastructure checks, and replace the initial-snapshot comparison with
an explicit reviewed snapshot receipt, not a silent bypass.

## Coordination

Claude's sibling branch `claude/shared-obligations` reserves concrete memcpy
linkage, SHA startup and general shared core frame constructibility. No overlap
with the scalar caller's size-specific allocation/copy/owned lifecycle. Do not
modify sibling COORDINATION.md unless an overlap appears. Its linked memcpy
contracts are for the linked program, not the unchanged original program;
original memcpy premises must remain identified until actual integration.

The broader all-533-jet goal remains active and unfinished. Preserve local
signed atomic commits; no remote pushes.
