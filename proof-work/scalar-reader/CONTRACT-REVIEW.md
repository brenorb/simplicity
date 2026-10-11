# Reviewed internal reader boundary

The complete 476-line contract output was reviewed: 31 actual theorem types
and 23 non-tree definitions, including the five local frame aliases. None
prints an abbreviated term. The exact source/output hashes and dependency
sets are enforced by `review.py`, with nine in-memory rejection tests.

The abstract oracle lift has a proved-oracle premise, external stability and
log neutrality: these are discharged by `shift64_frame_oracle`, not exported
as an assumed public call. Separation proves external bytes are outside the
symbolic footprint; all old valid blocks remain valid. Nonwrite events do
not change `has_wr`, `outsA` or `written`.

The first-call result uses actual read8s linkage, a 32-byte owned undefined
buffer, cursor variable zero and fresh byte variables 1..32. Its frame and
input hypotheses are the existing reader contracts, not the desired output.
The allocation equality only describes `xalloc`; concrete entry/allocation
composition remains open.

The setter result runs the original setter prefix in the actual three-region
context, proves the NULL suffix and call, and retains source and buffer cells.
The original reader's second `Scall` is then proved directly, including its
array expression, real integer-to-NULL cast, argument casts and function
lookup. `scalar_reader_body_exact` checks the original statement sequence;
no substitute body is executed.

The numeric bridge substitutes each byte variable pointwise into the already
verified setter expressions. Its five arithmetic/substitution results are
closed. Four actual Mint64 loads come from the final memory representation.
The composed actual body derives external stability/framing and preserves
the real buffer's Freeable range; none of these is an added call/output/free
premise. The buffer is not yet freed by this theorem.

Independent kernel session 17676 exited 0: 15 inherited context axioms, no
type-in-type, unsafe fixpoint or assumed-positivity categories. Exact per-result
reports (50338 exited 0): 19 closed, four with the inherited four
classical/extensionality dependencies, eight with the inherited six execution
dependencies. Do not confuse the imported context list with each result's
dependency set.

The two deep computed-tree prints (81933 exited 0), 62479 lines, are diagnostic
text. Their untruncated inventory was checked. Formal run/region equalities
and body decomposition supply the correspondence, not an informal reading
of omitted or abbreviated terms.

Still required: concrete reader entry/allocation/return/free composition;
public scalar jet lifecycle and literal canonical specification/source/
parametricity gates; ordinary full acceptance. This archive adds no public
coverage and does not prove arbitrary evaluator frame layouts. SHA/memcpy
reservations and all unrelated staged work are preserved. No remote writes.
