# Normal scalar-normalize / scalar-negate candidate

The two complete original-public-C-to-literal-Simplicity local contracts are
now freshly compiled in the repository's normal logical namespace `C`.
This is **not yet full acceptance or main-checkout registration**.

Candidate: `/tmp/jet-scalar-integration.XAMDsw/Coq`.
Parent: `/tmp/jet-scalar-zero-accept.smyVL2`, whose complete normal acceptance
session 45608 terminated with exit 0; receipt `../scalar-zero/ACCEPTANCE.json`.

## Exact checked transport

`ASSEMBLY.json` records 25 modules, 96 results, 43 definitions and two
provisional coverage entries. Every new source is byte-exact namespace
transport (`OriginalC.`, `WriterC.`, `NegC.` to `C.`) of a pinned, already
compiled/kernel-checked archive. All 1,024 inherited `.v` files are unchanged.
No production C/Haskell, specification, premise or postcondition was changed.

The former estimate of 22 modules / 80 results was incomplete: the whole
serializer also requires three original scalar-get-b32 modules, adding 16
results. These come from the verified `scalar-next` / `scalar-u128` archives.
The separate owned-getter experiments and unneeded u128-accumulator module
are not copied. Existing aliases resolve to real inherited C modules.

Fresh normal build session **82110** terminated with exit **0**, compiling
exactly all 25 transported modules. The public roots are:

- `C.jet_secp_scalar_normalize_local.scalar_normalize_local_spec`
- `C.jet_secp_scalar_negate_local.scalar_negate_local_spec`

They derive actual Clight public calls, return true, local allocation/copy,
reader/arithmetic/writer calls and freeing, exact canonical output, output
prefix/cursor updates and external load preservation. Helper executions,
output/storage and frees are discharged, not assumed in the public theorem.
The negation public target remains the literal Simplicity multiply/modulo
program, not a numerical modular-negation substitute.

## Normal snapshot review

`NORMAL-REVIEW.json` pins the reviewed drivers, outputs and snapshots:

- All 4,233 inherited per-result dependencies are unchanged. All 96 new
  dependency sets exactly match their checked OriginalC/WriterC/NegC reports;
  65 are closed. New assumption driver session **58546**, terminal exit 0.
- All inherited contract bytes are identical. The 96 types and 43 definitions
  are in the exact append-only inventory. Deep full-context printing is
  untruncated for every non-tree term. Three execution-tree prints remain
  diagnostics only, backed by actual run/shape proofs and source checks.
- Contract snapshot generation session **19188**, terminal exit 0. The deep
  full-context driver completed directly with exit 0. Review/preparation
  session **81141** and pinned read-only re-review **4578** exited 0.
- The kernel-level axiom snapshot is inherited unchanged. No admission,
  unsafe checker or new oracle was introduced. Some execution results retain
  inherited Coq/CompCert axioms; this is not a claim of axiom-free Coq.
- Source/coverage validation and all relocated literal/public gates passed.
  Their 16 in-memory wiring/contract mutations were rejected. Assembly's
  eight in-memory drift fixtures passed before snapshot generation; normal
  review's eight evidence/type/dependency fixtures passed after pinning
  (session **36161**, terminal exit 0). No audit input is mutated by fixtures.

The preparation script may copy a **frozen, snapshot-reviewed** parent while
its full audit runs, allowing an independent normal compilation in parallel.
It never writes the parent. Normal review now requires its terminal full
acceptance receipt. Preparation/snapshot generation never authorize main
registration; full normal acceptance is still required.

## Current acceptance and scope

Full `JOBS=1 bash check-jets.sh --accept`, without update/no-build flags,
session **83287**, terminated with exit **2** after the build, kernel check
(829 modules), assumption audit (4,329 results / 2,292 closed), public
contract comparison and negative gates passed. AST regeneration failed
because the copied candidate lacked its sibling `C` directory, not because
an AST or proof differed. This run is **not full acceptance**.

Read-only source links `C` and `Haskell` now point to the main repository,
matching the accepted parent's layout. The pinned normal reviewer completed
again with exit 0 (session **40956**), and core AST regeneration then passed.
No proof, inventory, snapshot, gate or production input was changed.
The full acceptance retry is running as session **10545**; preserve it and
every candidate input. Its separate log is
`/tmp/jet-scalar-integration.XAMDsw/scalar-integration-full-acceptance-retry.log`.
Pre-acceptance fingerprint:
`aa652e53f690b80bcdc03a263f11114d04b1e9743f3dac471a41b00e9dac42ec`.
Log: `/tmp/jet-scalar-integration.XAMDsw/scalar-integration-full-acceptance.log`.

358/533 is **provisional isolated candidate** coverage (254 entries without an
extra library premise, 104 conditional on the original memcpy model), not
main-checkout coverage. Main registration remains 351/533. These theorems
retain inherited local-frame, LP64, RECKLESS/assertion-disabled scope; they
do not complete evaluator/all-frame or assertion-enabled proof obligations.
No every-jet completion is claimed.

Claude's shared memcpy linkage, SHA startup, frame/Bit-Machine constructibility
and Elements translation-unit/getter work do not overlap these files. Their
integration and exact proof boundaries remain separate obligations.

See `CONTINUATION.md` before proceeding. Signed local commits only; no pushes.
