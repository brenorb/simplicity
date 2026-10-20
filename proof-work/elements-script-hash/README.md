# Four indexed/current Elements script-hash C contracts

Checked actual-C endpoints:

- `simplicity_input_script_hash`
- `simplicity_input_script_sig_hash`
- `simplicity_current_script_hash`
- `simplicity_current_script_sig_hash`

The new `C.jet_elements_script_hash_literal` module contains one shared,
closed conversion lemma for any input-to-digest projection, four semantic
bridges and four whole-C endpoint theorems. It reuses the checked index-word,
four-limb digest, separated-contract transport and generic current-input
assertion lemmas. It does not reimplement C execution or replace it with an
assumed output: every endpoint transports an existing actual Clight call
contract to the literal index/digest specification.

## Verified evidence

All 18 unregistered dependency/root modules freshly compiled. Complete deep
reports cover 206 result types and 130 definitions, with apostrophe-ending
identifiers preserved. The new module contributes nine results and five
definitions. The generic conversion is closed; the four semantic bridges
retain functional extensionality from the existing primitive interface.
Every final endpoint has exactly its original C theorem's six inherited
assumptions, without a new external-library premise.

Recursive kernel checking of the new module and both C-execution roots
passed with the unchanged library context and no unsafe fixpoint or assumed
positivity categories. Exact Elements AST regeneration passed. The source
guard passed and rejected 30 in-memory script-selection, digest, tag,
representation and whole-contract mutations. The evidence review passed
and rejected 22 scope, apostrophe-inventory, source, command, report, kernel
and AST corruptions. Invalid proof text was never compiled.

## Exact specification and memory boundary

The indexed getters implement the selected primitives; the current getters
implement `CurrentIndex >>> assert (primitive InputScriptHash/InputScriptSigHash)`.
The guard checks the actual Haskell catalog, primitive projection, library
record/adapter and assertion program, together with the Coq projections,
literal conversions and complete original/final C contracts. ScriptPubKey
and scriptSig are distinct fields, at offsets 136 and 64 within the 544-byte
input layout. The indexed contracts keep the out-of-range result tag and
unspecified absent-payload cells. Current-index bounds are those of the
existing logical environment.

These C functions copy cached digest words. The initial environment relation
requires those words to represent `Digest.byteStringHash` of the selected
logical script. The existing byte-string hash primitive model is unchanged:
this batch adds no cryptographic algorithm equivalence or caller-cache
construction theorem. The guard pins the selected hash/model definitions
and their use; it is not a proof of the Haskell cryptography implementation.
The original separated frames, arbitrary output contents, cursor/prefix,
environment footprint and permitted-memory-change contracts are unchanged,
as is the LP64/RECKLESS build scope.

## Normal admission remains open

After that predecessor is accepted and installed, prepare the next normal
four-jet batch from its immutable checked source state. The seventeen shared
dependency modules here are already in that predecessor's 34-module addition.
Only this new proof module (nine results/five definitions), the two mandatory
source/negative guards and the four selected coverage entries need adding.
Use a new-module-only explicit-parameter printer rule and compare every
inherited type/definition/assumption record unchanged. Run independent normal
review and full acceptance before a guarded source-only installation; preserve
the entire preexisting index and copy no compiler objects.

The generic conversion can subsequently serve other indexed digest fields,
but each needs its own selected canonical projection and whole-C contract
review; merely sharing a dependency module never establishes coverage.
Caller/environment composition, remaining conditional-library obligations,
assertion-enabled builds and all other missing jets remain in the full goal.
