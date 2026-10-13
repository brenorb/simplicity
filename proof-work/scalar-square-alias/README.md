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

All five modules were explicitly rebuilt in order (session **63195**, exit 0).
Both complete audit drivers terminated with exit 0 (**32921** for assumptions,
terminal chunk **7207bc** for contracts). Independent whole-dependency kernel
check **21157** terminated with exit 0. Sources were frozen during that check.
`REVIEW.json` pins all sources, compiled objects, drivers, reports and kernel log.

There are **22 results** and **nine definitions**. Sixteen results are closed;
one representation theorem retains four inherited classical/extensionality
dependencies, and five execution results retain those plus CompCert's two
semantic parameters. The dependency-wide kernel context is the inherited
15-axiom allowlist; all three unsafe categories are empty. No new axiom was
added. The complete type/definition report is untruncated (18,186 bytes).
Nineteen in-memory corruption fixtures passed.

The narrow scratch namespace is `SqrC` at `/tmp/jet-scalar-square.xWr06l`.
Dependencies are the frozen normal multiply candidate, whose fingerprint is
`1b159005caeac45684fe3b38d56f46bd78a166845fa62fc365137cafe82c3669`.
Its full public acceptance is a separate ongoing run **38093**; this helper
receipt neither claims that acceptance nor main integration. No new AST
regeneration is claimed by this helper verification.

```sh
python3 -B proof-work/scalar-square-alias/review.py
python3 -B proof-work/scalar-square-alias/test-review.py
```

For a fresh rebuild, use the pinned Coq 8.17.1 compiler and `ulimit -S -s 65520`.
From `/tmp/jet-scalar-multiply-integration.yIS07H/Coq`, run
`bash build-jets.sh --coqc -Q /tmp/jet-scalar-square.xWr06l SqrC` with each
absolute scratch `.v` path in manifest order, then both audit drivers. Capture
their fresh exits and reports. Run `--coqchk -silent -o` with the same narrow
mapping and the two roots in `REVIEW.json`; use measured process bounds
(120 seconds per compile, 900 for the independent kernel). Do not reuse stale
compiled objects as evidence for edited sources.

Signed atomic local commits only; never push. Claude's shared/Elements builder
reservation is untouched. The all-533 goal remains active and incomplete.
