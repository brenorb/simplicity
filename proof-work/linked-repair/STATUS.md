# Checked linked families integrated, 2026-10-14

Follow-up: the four unchecked conversions in the normal secp dependency tree
are repaired and kernel-checked, along with their selected local-contract
callers and the newly installed frame-constructibility module. See
[`secp-checked-conversions`](../secp-checked-conversions/README.md). The earlier
diagnostic-only/deferred notes below are historical. Original linked receipts
are unchanged; their driver provenance and source-preservation checks compose
only the exact documented successor hooks and five source repairs.

Source: `claude/shared-obligations` at
`30404face45383153528f36d915de6d7df11f3f4`. Target:
`feat/jet-equivalence`. This follows the earlier 185-file non-linked review.
The branch was not merged wholesale, rewritten, deleted or pushed. Its active
worktree and uncommitted Elements copyInput experiment were untouched.

## What changed

Three definition-list equalities used unchecked conversion casts. Each was
replaced with `timeout 10 (vm_compute; reflexivity)`, without changing its
statement or other proof bodies. The complete modules and callers compiled
and passed recursive kernel checks—not just the small initial experiment.

| Batch | New source/tool files | C/support modules checked | Reported results | Recursive kernel check |
| --- | ---: | ---: | ---: | --- |
| Core | 6 | 522 | 223 | exit 0 |
| SHA / startup | 20 | 352 | 154 | exit 0 |
| Bitcoin environment callers | 2 | 359 | 22 | exit 0 |

Total: **28 new source/tool files**, including **26 `.v` files**. These are
not new accepted-jet counts. The core results include 104 linked jet
contracts and 104 fresh-frame execution results. The Bitcoin batch includes
seven proof-valued caller/composition aliases, whose types and assumptions
were audited as results. Required original `JetStartup` namespace modules
were copied only where the new linked startup tree needed them.

Signed local source commits:

- `954c53d6`: linked core and verified reference-memcpy infrastructure.
- `7b20d338`: linked Bitcoin environment callers.
- `8c651286`: linked SHA and startup proof families.

`668367f5` and `946686c3` contain the isolated audit tooling and scoped
assumption parser. `5f274d27` records the separate bounded secp diagnostic.
No unrelated staged change was included in these commits.

## Verification and assumptions

Each batch regenerated its original applicable C program(s) and memcpy
reference with the pinned target/profile and compared exact AST bytes.
Linked programs were derived using the frozen generator and independently
regenerated during review. The formal linking theorems check the resulting
programs against CompCert's actual linker. Call-site sources were derived
with the frozen patcher; every new, renamed or changed-program-dependent
module was freshly compiled in a copied namespace with Coq 8.17.1 / CompCert
3.14. A confirming make preserved and hash-bound the initial fresh build
trace after a report-parser correction; no proof-source change was needed.

Full exported types, definitions and assumptions were reported. The reports
contain 12 / 18 / 12 closed results respectively. AST-level linker results
and all three repaired equalities are closed. The two whole-program linking
declarations in each linker module inherit CompCert's existing
`lib.Axioms.proof_irr`. That allowance is confined to those declarations;
it was not added to the ordinary registry policy or jet execution contracts.
Other dependencies are the six inherited assumptions, plus the two already
documented external-function property assumptions used by forward-memory
startup proofs. No new axiom or proof skip was introduced.

Recursive `coqchk -o` checked every root and its dependencies, without unsafe
options. No unsafe (co)fixpoints or assumed positivity were reported. All
three batches passed 16 evidence-corruption fixtures, six lexical proof-escape
fixtures, and namespace/specification-copy/link-policy checks. `REVIEW.json`,
`ASSEMBLY.json`, `TESTS.json` and `INSTALLATION.json` in each batch directory
bind the sources, commands, objects, logs, assumptions and actual terminal
results. `README.md` provides copied-tree replay commands.

## What this does—and does not—prove

These are execution-to-specification results for **internally linked
programs using the proved reference memcpy**, not for the unchanged program
using arbitrary abstract external libc semantics. The original registry's
104 `memcpy_model`-conditional entries remain conditional. SHA startup,
readability, separation and application-input requirements remain as stated
in the individual contracts; they were not silently dropped.

Registered coverage remains **364/533**. No normal registry, contract
snapshot, assumption allowlist or `_CoqProject.jets` entry was changed. These
are independently checked program-specific closures, not a new combined
full-normal-worktree acceptance receipt. The all-jets goal remains unfinished.

## Remaining exclusions and next repair

`Coq/C/jet_frame_constructible_secp.v` is still excluded from installation:
its normal-tree dependency `jet_secp_fe_nv.v` contains an unchecked cast.
Unlike the previously blocked diagnosis, we now have a successful checked
probe: the exact `nv_run_eq` equality compiled with the same ten-second
conversion and printed a closed assumption report. See `secp-probe/`.
The main file was **not** changed, and the probe is not a full normalization
module/caller/kernel audit.

Next: make that narrowly scoped main normalization repair, rebuild and
recursively check its transitive callers and the new constructibility module,
then integrate it. Preserve concurrent secp work. Because this intentionally
changes an existing tracked proof source, give it its own reviewed repair
ledger/baseline; do not silently bypass these additive preservation checks.

Other omitted code is duplicate startup work already transported into main,
obsolete shared-tree/symlink build and audit scripts, stale registry
generators, or old expansive receipts/prose. They should not be imported
as-is. Actual outstanding proof work remains: Elements canonical semantic
review and specification bridges, radix-sort/copyInput/whole Elements
transaction construction, caller transport to the original program, and
runtime-driver composition. This import does not discharge those obligations.

## Preservation

Both the linked and preceding non-linked post-installation checks passed.
Every pre-existing Coq/C/Haskell input is unchanged; additions are bound to
their source-only installation ledgers. The original staged patch SHA-256 is
still `f2083389e06d3a5aed12c83d0aae554895eab94eef8e107c5d445f9268d86bbe`.
Claude's head is unchanged, and its only untracked file remains
`Coq/elements-env/C/jet_elements_env_copyin_defs.v`.

Frozen generated/template whitespace is preserved for exact provenance;
cosmetic whitespace lint is not being represented as clean. Nothing was
pushed, and the paused all-jets app goal was not resumed or marked complete.
