# First original field-multiplication checkpoint and reduction conservation

This additive proof support advances the original `fe_mul_inner` value bridge.
It does **not** register a new jet or claim complete field-product equivalence.

`Columns.columns_conservation` proves an explicit conservation identity for
the original algorithm's unbounded integer carry/reduction schedule: the
polynomial input minus the reduced result is the field prime times an
explicit quotient. `columns_modulo` follows. These results are closed and
have no input-range restriction. They do not establish that the C machine
operations avoid overflow or that a public jet matches its specification.

`Prefix` extracts the first 32 heads of the **actual original statement
spine**, ending just after the first `d >>= 52`, and proves that this prefix
and the untouched suffix reconstruct the original body. It derives execution
and representation/framing from the verified executor, with the existing
owned input/local-storage and environment/temp representation premises.
These are slice-entry premises, not discharged whole-function entry results.

`Ops`/`Machine` factor the actual unsigned multiplication, multiply-accumulate,
word accumulation and 52-/64-bit shift expressions. Their numeric observations
include modulo-128-bit wrap; no-overflow is not silently assumed.
`Bridge.exec_first_machine_atomic` executes the actual prefix and derives
current loads for both `c` and `d` limbs and the live `t3` value as compact
machine expressions. It returns an atomic representation for subsequent
slices, with the same physical memory and live temporary environment.

`Atomic` generalizes existing `C.jet_sx_revalue_cells` support to all regions
and temporaries. Its proofs preserve denotation, layout, permissions,
ownership, memory, event log and fresh-variable counter. It introduces no
new variables or assumed equations; values are existing machine denotations.

## Verification boundary

The first slice's exact integer observations and derived carry bounds are
extended in `../secp-field-first-values`; caller reader bounds and the
remaining original slices are still open.

## Lessons and next step

Direct equality between the full extracted output tree and a factored
symbolic schedule timed out at ten seconds under both direct conversion and
VM reduction. A node-count experiment terminated unsuccessfully with an empty
log; no node count or memory-error diagnosis was established. Those failed
experiments are outside this proof packet. They do not demonstrate a C bug.

Astra Medium reviewed the direction read-only and recommended the existing
checkpoint pattern used by scalar reduction, rather than beginning a new
fresh-variable oracle/valuation framework. Both cell **and temporary**
representations must be compressed at a boundary; cell compression alone
does not remove large live temporary expressions.

When specializing `field_stmt_normal`, first make the recursive `xstmt`
constant opaque along with the already-checked checkpoint values. Otherwise
Coq unfolds its fixed fuel during conversion while reconciling the named run
with its explicit statement form. `prefix_typed_run` caches the exact type;
no AST, theorem conclusion or kernel check is changed. The completed prefix
proof needs no increased reduction timeout. The independent integer
conservation certificate's kernel check was measured at about 27 seconds;
only that `Qed` has a bounded 60-second allowance, with tactics still at ten.

Next: derive the first checkpoint's no-overflow/range facts from the original
limb bounds, instantiate the unbounded `d3`/`p8` reduction equations, then
execute the next original slice from atomic entry values. Repeat through the
remaining carry/reduction stages; connect the complete machine result to
`Columns`, the actual readers/normalizer/writer and the literal canonical
`fe_multiply` specification. Existing public source and input domains stay
fixed. Pure integer conservation or a slice theorem alone is not completion.
