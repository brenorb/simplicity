# Checked shared-input scalar square body

This is progress toward the public `simplicity_scalar_square` C-to-Simplicity
equivalence, not that final equivalence. No covered jet or main registration
is added. The original generated C remains unchanged (LP64 / RECKLESS).

The actual square wrapper calls `scalar_mul(a,a,a)`. Multiplication's earlier
two-input owned contract cannot prove this by instantiating equal pointers:
ownership of one block must not be duplicated. These five modules use exactly
two regions, `[l,a]`: a fresh uninitialized 64-byte product buffer and one
initialized owned 32-byte scalar. The real `scalar_mul_512(l,a,a)` call is
derived using the sound compact executor, including its own function boundary.

`den_sx_rename` is a general, closed lemma preserving machine-value denotation
under renaming of symbolic variables. The square execution's output is proved
to be the existing symbolic product with its second operand variables renamed
to the first. All eight real current-memory product loads and the full 512-bit
square value follow from the checked product arithmetic; no separate arithmetic
development or new specification is introduced.

`square_product_reduce_entry_rep` establishes the real next call's two-region
representation from that actual product memory. `eval_square_product_then_reduce`
composes both actual calls and derives the square modulo the canonical order.
`exec_scalar_square_body_inplace` derives the unchanged original `scalar_mul`
body execution for `r=a=b`, output representation and outside-region framing.
The three-slot layout used to instantiate an expression/call rule is **not**
asserted to own three regions; all execution and memory premises use `[l,a]`.

Still required: `scalar_mul`'s actual fresh-array allocation, function entry,
void return and free; then the public square wrapper's single scalar reader,
writer, original locals/cursor/framing cleanup and literal Simplicity term.
Those are not replaced by assumed execution or output premises. The modular
identity here is an internal bridge, not the public target specification.

## Verification

There are **22 results** and **nine definitions**. Sixteen results are closed;
one representation theorem retains four inherited classical/extensionality
dependencies, and five execution results retain those plus CompCert's two
semantic parameters. The dependency-wide kernel context is the inherited
15-axiom allowlist; all three unsafe categories are empty. No new axiom was
added. The complete type/definition report is untruncated (18,186 bytes).
Nineteen in-memory corruption fixtures passed.

Signed atomic local commits only; never push. Claude's shared/Elements builder
reservation is untouched. The all-533 goal remains active and incomplete.
