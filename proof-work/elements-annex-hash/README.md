# Two annex-hash C contracts and shared optional-digest conversion

Checked actual-C endpoints: `simplicity_input_annex_hash` and
`simplicity_current_annex_hash`, with their original whole separated
frame/environment/memory contracts. The new
`C.jet_elements_optional_digest_literal` module contributes six results and
three definitions: a generic optional-digest conversion, a compatibility
lemma showing the existing pegin model is its instance, two semantic bridges
and two complete C endpoint theorems. The two generic/compatibility lemmas
are closed; semantic bridges retain functional extensionality, and endpoint
assumptions exactly match their originals' six inherited assumptions.

## Verified evidence

All **24** unregistered dependency/root modules were freshly compiled, with
complete deep reports for **244** result types and **187** definitions.
Apostrophe-ending identifiers are preserved. Assumption sets of all inherited
pegin dependencies match the prior receipt; all new helper dependencies are
within the unchanged six-assumption set. Recursive kernel checking of both
C-execution roots and the new module passed with the unchanged library
context, no unsafe fixpoint categories and no assumed positivity. Exact
Elements AST regeneration passed.

The source guard reuses the checked pegin/digest/current-assertion source
correspondences and adds the actual optional-annex byte-hash primitive,
transaction/library bindings, Coq projection, complete environment predicates,
flag/hash fields, literal definitions and all four original/final C contracts.
It passed and rejected **26** in-memory corruptions. The independent evidence
review passed and rejected **23** scope, apostrophe-inventory, source, command,
report, kernel and AST corruptions. Invalid proof text is never compiled.

## Exact behavior and unchanged scope

The indexed jet has three distinct cases: invalid input index, an existing
input without an annex, and an existing input with annex bytes. A present
empty byte string is in the **third** case and returns its SHA-256 digest;
it is not an absent annex. The literal model retains both presence tags and
the unspecified absent payload cells. The current jet uses the canonical
`CurrentIndex >>> assert (primitive InputAnnexHash)` program to remove only
the outer index-presence tag.

The C functions copy cached digest words, with flag field at offset 536 and
hash field at offset 0 in each 544-byte input. The initial environment relation
requires the cache to represent the existing `Digest.byteStringHash` primitive
model on the selected annex bytes. This does not prove caller construction
of caches or equivalence of host cryptography libraries. No new external-
library premise, axiom or unchecked cast is added. Original arbitrary output
contents, frame cursors, output prefixes, environment footprints and permitted
memory changes are retained, as is the LP64/RECKLESS build configuration.

## Normal admission remains required

Coverage added here is **zero**. Main's 371/533 full acceptance has passed.
The seven-jet predecessor audit remains live as session **96260**, last
confirmed during this checkpoint. Its source inputs are unchanged. The
eight-getter candidate at `../elements-digest-getters-admission/` is reviewed
and proposes 386/533 only after predecessor acceptance/installation and its
own full audit; its full audit has not started.

After that sequence, the annex delta needs two newly registered modules:
the existing `C.jet_elements_annex_local` (seven results/sixteen definitions)
and the new optional-digest module (six results/three definitions). All other
twenty-two dependency modules are already in the earlier seven-jet batch.
Thus there are thirteen result and nineteen definition additions, thirty-two
new complete records, one new proof source, two mandatory source/negative
guards and two selected coverage entries. Preserve every inherited record
and assumption set and add exact nested-sum/width/whole-contract coverage
fixtures before full normal acceptance and guarded source-only installation.

The same generic conversion is available for the remaining optional direct
digest projections (reissuance blinding, new issuance contract, reissuance
entropy); consider proving their indexed/current jets next and combining
them with this pair in one reviewed admission batch. Each still requires its
own canonical projection and complete C-contract review; sharing a helper is
not coverage. All remaining jets, caller/environment/library links, inherited
fidelity and configuration obligations remain in the active all-jet goal.
