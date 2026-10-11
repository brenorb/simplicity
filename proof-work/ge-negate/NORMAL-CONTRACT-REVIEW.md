# Affine normal-load-path contract review

Normal serial build 96488 exited 0. The generated standard contract snapshot
matches the reviewed deep report for all 109 new types and 37 new definitions,
subject only to whitespace and explicitly listed printing qualifications.
Every inherited contract is preserved byte-for-byte. NORMAL-CONTRACT-REVIEW.json
records the actual snapshot hash and nine deep-supplement diagnostics.

Those supplements are the same one reader type/eight computed run/tree
definitions reviewed earlier. Matching retained fragments is not a certificate
for omitted terms; actual source and independent kernel evidence still apply.
No public premise/postcondition, canonical expression or executable AST was
rewritten. The public contract is still original simplicity_ge_negate on any
Word256 pair, with literal Simplicity take fe_normalize &&& drop fe_negate,
under the unchanged inherited local frame predicate.

The normal driver opens BitMachine and Translate. The comparison therefore
normalizes only their specific Cell/encode globals, f_writeBit and the explicit
reviewed C-module qualification list. It does not erase arbitrary prefixes.
Inherited printed definitions contain internal fields with repeated display
names; the complete byte sequence is preserved instead of collapsing it into
a dictionary. Two duplicated inherited inventory rows are preserved exactly;
new inventory/contract records must be unique.

Parser/normalization fixtures pass. Five full-context report mutations reject:
an inherited false premise, a new public false premise, canonical-spec
replacement, an unreviewed qualification and missing public result. These
fixtures patch in-memory report reads only. No frozen proof/audit file changes.
Read-only source guards cover all 948 inherited Coq source files, the 38 new
proofs, two checkers, eight metadata hashes and absence of extra modules.

Reproduce:

```sh
python3 proof-work/ge-negate/review-full-snapshots.py \
  --work /tmp/jet-ge-negate.aFl8mr --contracts-only
python3 proof-work/ge-negate/test-review-full-snapshots.py \
  --work /tmp/jet-ge-negate.aFl8mr
```

This is a partial contract receipt, not full snapshot review or acceptance.
Full axiom generation 90113 remains live; after terminal success, run the
reviewer WITHOUT --contracts-only, review/record all old and new axiom sets,
then full check-jets.sh --accept. Point candidate acceptance 77601 has passed
the 728-module coqchk step but remains live in its subsequent assumption gate.
Neither run is accepted here. Actual checkout coverage stays unchanged.
