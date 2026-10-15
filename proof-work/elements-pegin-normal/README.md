# Indexed/current Elements pegin contracts under final C names

Both actual C jets (`simplicity_input_pegin` and `simplicity_current_pegin`)
now have their checked canonical-source bridges under the normal
`C.jet_elements_pegin_literal` namespace. The literal proof is byte-identical
to the previously checked private-namespace source in `../elements-pegin/`.
The primitive is an optional digest, not bytes to hash or a Boolean. The
indexed contract retains both presence tags; the current-input contract
retains the canonical assertion that removes the outer tag.

Private candidate: `/private/tmp/jet-elements-pegin-normal.yNBGhn`.
All 22 unregistered dependency/root modules were freshly compiled. Complete
reports cover 231 result types and 168 definitions, including identifiers
ending in apostrophes. Assumption sets match the previously checked proofs
exactly after namespace rebasing. The two literal matching lemmas retain
functional extensionality; the two endpoint contracts retain their originals'
six inherited assumptions. They are not claimed to be axiom-free.

Recursive kernel checking of all three C roots passed, as did exact Elements
AST regeneration, the canonical-source guard, and its 20 source mutations.
The evidence review passed and rejected 21 in-memory corruptions of scope,
apostrophe-aware inventories, source, commands, reports, kernel and AST
evidence. Invalid proof text was not compiled. All 1,582 inherited source,
metadata, registry and guard files remain byte-identical, with exactly one
new proof source added. Sources, objects, commands, terminal exits and tools
are bound in `PREPARATION.json`; complete reports and the proof are archived.

```sh
python3 -B proof-work/elements-pegin-normal/review.py
python3 -B proof-work/elements-pegin-normal/test-review.py
```

Normal coverage added here is **zero**. Registration and full normal
acceptance remain required. Main has 371/533 installed jets and its distinct
actual-main getter audit is still running as session 74479 (confirmed live
when this checkpoint was written). Keep that audit's inputs frozen; poll its
existing handle rather than restarting it. Prepare the next admission in an
independent tree, combining these two jets with the five checked timelock/
assertion jets from `../elements-check-lock-normal/` to reuse shared helpers
and one full acceptance run. Do not register unrelated jets merely because
their helpers share these dependency modules.

The original separated frames, arbitrary output contents, cursor/prefix,
environment representations and permitted-memory-change contracts are
unchanged, as is the LP64/RECKLESS build scope. These results do not prove
environment-builder/evaluator composition or assertion-enabled builds.
Receipts bind the actual dirty/staged source base, not a clean-HEAD build.
The full all-jet objective remains unfinished.
