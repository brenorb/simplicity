# Input/current pegin: actual-C contracts with literal digest decoding

The new `jet_elements_pegin_literal.v.source` proves full separated C contracts
for `simplicity_input_pegin` and `simplicity_current_pegin` in `elements_ge`.
It reuses the existing indexed/current C execution and framing proofs, the
generic current-input assertion bridge, the all-width Haskell word decoder,
and the checked four-limb digest conversion. No C execution, output property
or mathematical replacement specification is assumed.

Pegin here is an **optional direct Hash256**, not merely a flag or raw bytes
to hash. InputPegin returns two presence layers: out-of-range index, present
input without a pegin, or present input with a digest. CurrentPegin removes
only the outer layer through CurrentIndex/assert. The literal specifications
retain that distinction and Haskell's actual index and digest decoding.
Historical generated comments describing hashing pegin bytes must not be
read as this theorem's premise/result: these jets copy an existing digest.

## Checked evidence

Private tree: `/private/tmp/jet-elements-pegin.IIkzRv`.
It is an unchanged private copy of the checked five-jet final-name tree.
The new proof is in `Proof/`, narrowly mapped to `PeginLiteral`, outside
normal registration. No live audit-tree compiler output is copied.

Twenty-one C dependencies plus the new literal module were freshly compiled.
Complete reports cover 231 helper/final result types and 168 definitions.
The declaration scanner preserves Coq identifiers ending in apostrophes;
an earlier truncated-name report failed visibly and was corrected before
the recorded fresh run. No declaration or failed proof was skipped.
The only proof correction normalized an `option_map` before case analysis,
leaving the symbolic digest untouched and using the existing digest lemma.

The two semantic matching lemmas inherit functional extensionality from the
primitive reader interface; they are not reported as axiom-free. Both final
C contracts retain exactly their originals' six inherited assumptions, with
no additional external-library premise. The shared word/digest representation
lemmas are reused, not reproved by enumeration or unchecked computation.

Recursive kernel checking of both actual-C roots and the new module passed,
with unchanged inherited context and no unsafe fixpoints/assumed positivity.
Regenerating the production Elements unit matched `jets_elements.v` exactly.
The selected source guard checks the optional-hash primitive, current-input
program, shared index/digest/assertr interpretation, whole original/literal C
contracts, field relations and footprints. Twenty source corruptions are
rejected; evidence tests additionally reject truncated apostrophe names,
scope/source/command/kernel/AST substitutions. Invalid proofs are never compiled.

Input records remain 544 bytes, the pegin flag is at 537, the digest at 32,
the transaction count at 696, and the environment current index at 80. The
same initial physical/logical relation, separated footprint, output, prefix,
cursor and memory guarantees are preserved. No new zero-initialized-output
or exact-padding assumption is added. Absent payloads retain unspecified
padding cells, as prescribed by the existing sum encoding.

`PREPARATION.json` binds sources/objects, base, original index, successful
commands, terminal statuses, reports and tools. All 22 source archives and
full type/definition/assumption/kernel/AST reports are retained here. The
literal source is outside the inherited Coq fingerprint and separately pinned.
Receipts describe the actual dirty/staged source base, not clean-HEAD
reproducibility.

```sh
python3 -B proof-work/elements-pegin/review.py
python3 -B proof-work/elements-pegin/test-review.py
```

## Continuation and boundaries

Coverage added is **zero**: final-C-name preparation and normal admission
remain required. Only the two pegin correspondences are newly reviewed here;
other asset/amount/issuance/hash jets in the shared dependency modules are
not thereby certified against their canonical Haskell programs or registered.
This checked dependency closure can be reused for their subsequent proofs.

First check the literal module under `C` without changing its proof text,
then prepare a normal candidate with the exact selected source gates, full
statement/definition/assumption review and mandatory complete acceptance.
Use apostrophe-aware declaration parsing in every inventory/report step.
Do not install while a predecessor audit still requires main's source map
to remain frozen; do not duplicate completed/live audits.

Environment-builder establishment, evaluator composition, other primitives,
and assertion-enabled/non-LP64 builds are not proved by this batch. The
existing LP64/RECKLESS scope and all remaining jets/shared conditional-library
obligations remain part of the unchanged full goal.
