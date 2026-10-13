# Elements Version integration

This batch imports the thirteen-module Version closure, byte-identical to
Claude commit `adff42d3365d759a988740d520c45c9d286a51ab`. The original independent
review and kernel/AST receipts are in `../elements-version-review/`.

Only `Elements.Version` primitive identity and semantics have been reviewed.
The target is the literal program `Primitive.Combinators.prim Elements.Version`,
not a replacement numerical specification. The public theorem executes the
real `simplicity_version` function in the original-production Elements unit,
with full frame/output/cursor/prefix/memory obligations. Its initial environment
relation requires represented transaction-version fields; this is not a proof
of the actual Elements environment builder or evaluator. It adds no libc model
premise; the six inherited CompCert/classical assumptions remain explicit.

`import.py` imports frozen blobs through `apply_patch`, checks shared dependency
hashes and preserves the existing index. The translation unit additionally
includes original `sha256.c` and `elements/ops.c`; no production C is edited.
The added normal source guard tests seventeen correspondence/public-boundary
mutations. The normal AST gate now includes actual Elements regeneration.

`admission.py assemble` copies the current worktree to an isolated candidate,
capturing the seven original metadata hashes and staged-patch hash.
`prepare --candidate DIR` explicitly recompiles the thirteen modules, prints
new compact and fully expanded records, reuses only independently checked
dependency sets and kernel-checks the fresh closure.
`review --candidate DIR` rejects changes to any inherited type/definition or
dependency record, nonexact inventory extensions and unrelated coverage edits.
`test-review.py DIR` rejects eight in-memory evidence corruptions.
`install --candidate DIR` installs only the reviewed seven-file worktree delta,
without changing existing staging. These dirty shared metadata files are not
swept into a scoped commit.

Preparation and installation are not acceptance. After review, freeze main's
inputs and run `Coq/check-jets.sh --accept`, without update/no-build flags, with
Coq 8.17.1 and a 65520 KiB stack. Only its terminal exit-zero receipt permits
claiming normal acceptance: 362/533 entries, 104 still conditional on
`memcpy_model`, 171 missing. The full all-jet goal is not complete.

Next reviewed batch: SHA startup establishment/preservation. Keep its startup
state boundary, external memcpy condition, and any archived-source repair
separate from actual-caller or evaluator claims. Do not register other Elements
jets without reviewing their primitive semantics and literal specifications.
