# Sequence contracts: final-namespace preparation

Both actual-C sequence contracts are now freshly compiled and recursively
kernel-checked as `C.jet_elements_sequence_literal` and
`C.jet_elements_current_sequence_literal`, not only in external review
namespaces. This is preparation for normal registration, **not acceptance**:
no main source, manifest, registry, snapshot or compiler output was changed,
and this batch adds zero registered jets.

The complete ten type prints (eight literal results and the two original C
contracts), five definition prints and per-result assumptions passed. No
ellipsis or unresolved print placeholder is accepted. Both literal C
contracts have exactly the original six inherited assumptions; the two
all-width decoder lemmas remain closed. The existing source correspondence
guard passes on these final module names, and recursive `coqchk -silent -o`
preserves the fifteen-axiom library context with all unsafe categories empty.
The generated C program and all old sources are unchanged from the fully
accepted count candidate, whose production ASTs were checked there.

## Next normal admission

Extend the coverage guard narrowly: input sequence is the separated
`Elements.env`, `Word32 -> Sum Unit Word32` contract; current sequence is the
plain `Elements.env`, `Unit -> Word32` contract. Keep the five existing
Elements entries unchanged and continue rejecting all unaudited names. Add
negative coverage fixtures for function, linked/logical environment, widths,
whole-contract shape and vacuous premises. Install the selected sequence
source guards and their negative tests into normal acceptance. Do not count
368/533 or install new main metadata until the independent full acceptance
has actually succeeded. Actual-main verification is a separate step.

The original main staging contains substantial unrelated work and must not
be swept into a commit. Follow the count batch's exact delta/preservation
ledger pattern if that staging remains. These proofs and their dependency
receipts describe the actual working checkout, not a clean-HEAD build.
The all-jet goal and broader environment/evaluator obligations remain open.
