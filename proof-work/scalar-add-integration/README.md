# Normal scalar-add candidate: checked preparation

The complete original-public-C-to-literal-Simplicity scalar-add contract now
freshly compiles in the normal logical namespace `C`:

`C.jet_secp_scalar_add_local.scalar_add_literal_local_spec`.

This is **not yet full acceptance or main-checkout registration**.
Candidate: `/tmp/jet-scalar-add-integration.RxsuOy/Coq`.
Parent: frozen, reviewed `/tmp/jet-scalar-integration.XAMDsw`; its full
acceptance retry **10545** remains live. The earlier failed run is not
acceptance evidence. No parent input is modified.

## Exact namespace transport and reviews

`ASSEMBLY.json` pins the public root's exact closure: **24 modules, 79 results,
41 definitions** from `scalar-add`, `scalar-add-bridge`, `scalar-add-readers`
and `scalar-add-public`. There are no omitted new dependency modules.
Transport changes only `AddC.` to `C.`; all 1,049 inherited .v sources are
byte-identical. Real original functions, literal specifications, predicates,
premises and postconditions are unchanged. Normal build **29824** ended
with exit **0**, compiling all 24 modules.

`PRELIMINARY-REVIEW.json` records:

- All 4,329 inherited dependency records unchanged, all 79 new records
  exactly matching the independently checked AddC reports (51 closed);
  total 4,408 records. New dependency driver **38663**, terminal exit 0.
- Exact append-only result/definition inventories, byte-identical inherited
  contract records, 79 new types and 41 definitions. All non-tree terms
  reviewed with full-context qualification and depth 100000, untruncated.
  Three standard-print ellipses are supplemented by complete deep prints.
  One execution-tree print is diagnostic only, backed by checked run/shape
  proofs and exact original source binding.
- Contract generation **89762**, terminal exit 0, is generation only.
  Reviewed assumption preparation **98043** and pinned read-only re-review
  **52209** ended with exit 0. The kernel axiom allowlist stays unchanged.
- Relocated literal/recursive gates, ten bridge and five public-boundary
  mutations pass. Coverage guard tests **44481** and eight independent
  source/type/dependency/inventory/kernel-allowlist/gate mutations **71491**
  ended with exit 0.
- All four AST preflights (core, Bitcoin, SHA, secp) match. The assembler now
  requires explicit verified sibling C/Haskell source links, avoiding the
  parent's missing-source-layout failure.

The normal review defaults to requiring a terminal successful parent receipt;
it currently **rejects** that missing receipt (90504, exit 1). Its explicit
`--preliminary` mode permits independent review/preparation while the parent
audit runs, not acceptance or registration. The existing parent reviewer and
the checked public archive are revalidated on every closure plan.

## Live verification and status

Independent normal kernel check **86561** is running, log
`/tmp/jet-scalar-add-integration.RxsuOy/normal-kernel.log`.
Preserve it; do not edit candidate sources, inventories, gates or snapshots.
Its completion is not full normal acceptance by itself.

Prepared input fingerprint:
`951402aa40e88c34b42d24b9bd95725285670df885531ff555b8e290127d5ffc`.

Candidate 359/533 is **provisional isolated** coverage (255 without an extra
library premise, 104 conditional on memcpy_model). Main remains **351/533**.
These local-frame / LP64 / RECKLESS contracts do not establish evaluator-wide
or assertion-enabled execution. No every-jet completion is claimed.

Preparation receipts/commands are in `PREPARATION.json`, exact reviewed
source/evidence hashes in the assembly/preliminary receipts.
Read `CONTINUATION.md` before proceeding. Preserve mixed staged/unstaged
main work; Claude owns Elements/shared obligations. Signed local commits
only, no production C/Haskell edits or remote pushes.
