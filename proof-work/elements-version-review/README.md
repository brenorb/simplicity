# Independently reviewed Elements Version proof

This milestone reuses Claude's finished proof **byte-for-byte** from frozen
commit `adff42d3365d759a988740d520c45c9d286a51ab`.
It does not modify the sibling worktree, its reserved builder work, main proof
inputs/registries, or the live scalar-lambda acceptance candidate.

Public root:
`C.jet_elements_version_local.elements_version_local_spec`.

The root proves execution of the original `f_simplicity_version` against
`Primitive.Combinators.prim Elements.Version`, under initial physical/logical
environment representation and arbitrary represented frame/cursor conditions.
It returns the canonical encoded output, advances the destination cursor and
preserves the specified prefix and other memory loads. Execution/output/free
are derived, not premises. There is no explicit libc model on this result.

## What was independently checked

- All **13 selected modules**, including the generated program and primitive
  port, were freshly compiled in normal C namespaces: build 13233, exit 0.
- All **34 result assumptions** and **38 full type/definition records** were
  generated: 85166, exit 0; 130,630 untruncated bytes, no diagnostics.
  Sixteen results are closed, seven inherit four classical parameters, eleven
  (including the public root) inherit those plus the two existing CompCert
  semantics parameters. Exact per-result sets are pinned.
- Whole-dependency independent kernel: 69374, exit 0; inherited 15-name library
  context matches, all three unsafe categories empty.
- The actual production-source Elements AST was regenerated with pinned
  CompCert 3.14 / Linux-amd64 glibc configuration and matches byte-for-byte:
  `be40201b9e508ea3c1d5309f0ecc21ebd1ec24914044aed2929feef0476a9a95`.
- The **selected Version correspondence** was reviewed and guarded: Haskell
  jet dispatch is `primitive Prim.Version`; primitive namespace/name/type are
  Elements/version/Unit-to-Word32; semantics return the unsigned transaction
  version. The Coq target is the literal primitive, not a replacement numeric
  specification. Its CompCert int carrier uses Int.unsigned and fromZ.
- Seventeen source/public mutation fixtures and eighteen evidence/report
  corruption fixtures pass. Review/receipt pins sources, objects, drivers,
  reports, generated AST and log.

## Do not overclaim the port or registration

The other **30 Elements primitive semantics clauses are not accepted by this
review**. The original port's pending-review status remains unchanged; only
Version's selected clause and its dependencies/correspondence are reviewed.
No every-Elements or evaluator/environment-builder completion is claimed.
The primitive signature checker alone would not establish semantics.

The derived Elements translation unit includes the original frame/core/SHA/
Elements ops/Elements jets sources. The older accepted baseline's preparatory
unit omitted SHA and ops. This explicit unit change is scratch-only and pinned;
it is not a substitution of production C bodies or a silent change to main.

No normal registry or expected snapshot is edited. Main remains **361/533**
accepted jets, and scalar-lambda full audit **21530** is separate and live.
Normal Elements admission needs narrowly scoped source/primitive identity
guards, closure inventories/type/definition/dependency review and a full
acceptance run including a **fifth (Elements) AST check**. Do not let the old
four-AST gate alone imply this unit was checked.

## Reproduce and continue

From the repository:

`stage-version.py --candidate ... --verify` is read-only.
Without --verify it only stages a fresh dedicated scratch copy of the immutable
accepted square base; it uses apply_patch and refuses inherited source drift.
The reusable proof sources remain in the immutable local Git commit rather than
duplicating the three-megabyte generated artifact in an archive.

Next finish lambda acceptance/integration, then admit Version through normal
Elements gates and extend semantic correspondence review/getter families.
Respect Claude's builder reservation, reuse its verified execution structure,
keep all-533 goal active; signed atomic local commits, never push.
