# Actual scalar-add reader checkpoint

Five modules / 15 results construct the helper's owned eight-limb input
representation and execute both original scalar readers from caller frames.
The second reader's execution preserves the first normalized scalar and its
Freeable ownership; the source cursor advances to `rc+512`. Both reader
outputs are the concrete stores for canonical scalar normalization. No
reader calls, second cursor or first-store preservation are assumed.

`eval_scalar_add_from_normalized_scalars` derives the original arithmetic
helper call and the literal add-result writer representation from those
stores, without separate weighted-value hypotheses. Combined with
`eval_scalar_add_two_readers`, this supplies the inputs needed for the next
read/read/add/write caller theorem. These are separate checked contracts,
not yet a composed public scalar-add theorem.

The proof reuses the established field-add caller structure with explicit
scalar adapters: 32-byte scalar regions instead of 40-byte fields, actual
scalar readers, and the checked scalar radix/normalization lemmas. The
invariant rebasing retains output capacity rather than treating consumed
input length as output capacity.

All final sources freshly compiled. Kernel session **91538** ended with
exit **0**. All 15 types and four definitions were reviewed untruncated;
exact dependencies are seven closed, five with four inherited classical
dependencies, and three execution results with those plus CompCert external/
inline-assembly semantics. The 15-axiom kernel context is unchanged and
all unsafe categories are empty. No new axioms, admissions or unchecked
tactics are introduced. Ten in-memory evidence mutations are rejected.

This is **internal caller support**, not public coverage, normal registration
or full acceptance. The actual writer and original public three-local
entry/copy/return/free remain. Scope is original local-frame / LP64 / RECKLESS,
not all evaluator frames or assertion-enabled execution. Main coverage stays
351/533 and all other authors' dirty work/registries remain untouched.
