# Sequence contracts: final-namespace preparation

Both actual-C sequence contracts are now freshly compiled and recursively
kernel-checked as `C.jet_elements_sequence_literal` and
`C.jet_elements_current_sequence_literal`, not only in external review
namespaces. This is preparation for normal registration, **not acceptance**:
no main source, manifest, registry, snapshot or compiler output was changed,
and this batch adds zero registered jets.

The input module is byte-identical to its previously checked source archive.
The current module changes only its import of that input module from
`SequenceReview` to `C`. All eighteen missing normal-build dependency modules
were explicitly freshly compiled in topological order (including the two new
literal modules); the sixteen inherited modules have unchanged source. The
module list and exact source/object hashes are in `PREPARATION.json`.

The complete ten type prints (eight literal results and the two original C
contracts), five definition prints and per-result assumptions passed. No
ellipsis or unresolved print placeholder is accepted. Both literal C
contracts have exactly the original six inherited assumptions; the two
all-width decoder lemmas remain closed. The existing source correspondence
guard passes on these final module names, and recursive `coqchk -silent -o`
preserves the fifteen-axiom library context with all unsafe categories empty.
The generated C program and all old sources are unchanged from the fully
accepted count candidate, whose production ASTs were checked there.

Candidate: `/private/tmp/jet-elements-sequence-normal.gDntta`.
Read-only source base: `/private/tmp/jet-count-admission.ww8e4z3b`.
This uses its immutable copied objects, not main's live compiler outputs.
The main input fingerprint and preexisting staged patch stayed unchanged
throughout preparation. Complete durable reports and final-name source
archives are retained beside this file.

```sh
python3 -B proof-work/elements-sequence-normal/review.py
ulimit -s 65520
python3 -B proof-work/elements-sequence-normal/prepare.py /absolute/independent-tree
```

## Next normal admission

Wait for the actual-main count acceptance (session 49451); do not mutate its
frozen inputs. Assemble the sequence admission in an independent candidate.
Add the eighteen dependency modules to both normal manifests and register
the appropriate new public results/definitions. Preserve every inherited
contract record byte-for-byte/in order and every inherited assumption set.
Register only `simplicity_input_sequence` and `simplicity_current_sequence`
against the checked canonical implementation contracts, retaining the proved
literal bridges and their reviewed source correspondence.

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
