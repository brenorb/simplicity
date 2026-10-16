# Three original C asset getters against literal specifications

`input_asset`, `output_asset` and `current_asset` now have complete local
C-to-literal-specification contracts. They reuse the existing C execution
proofs without adding an execution, success, output or field-canonicality
premise. They are not yet normally registered.

Private tree: `/private/tmp/jet-elements-asset-literal.sz6ggpg1`.
Input SHA-256:
`551425ad587081088a7547e1f81cbf84b22c216cad6d5f415fb9656a0a760f2b`.
The completed nonce proof tree supplied the seed; no objects were copied from
a live audit. All inherited proof sources and metadata remain byte-identical.

## Specification and reusable structure

The input/output targets are the actual InputAsset/OutputAsset primitives.
CurrentAsset follows CurrentIndex followed by the assertion of InputAsset.
The three full C contracts retain the original represented arrays, field
offsets, footprints, arbitrary output contents, frame/cursor/prefix behavior,
entry/copy/read/write/return/free execution and permitted memory changes.
Caller construction and the inherited empty-array/null-pointer domain remain
separate obligations; current input validity follows the logical environment's
existing bounded-index condition, not a newly assumed successful branch.

The shared `encode_confidential_literal_matches` is polymorphic in the
explicit payload type. Explicit asset hashes use the existing hash decoder;
confidential assets use parity and the packed field word. Haskell's
`fe_repr = toInteger . fe_pack` reads that packed Word256 value. The Coq point's
hash field models its serialized bytes, decoded using the checked four-limb
native-word bridge. No field reduction or group computation is substituted.
The port's total extension to arbitrary packed words does not assert that all
such words are valid Haskell FE values. No new canonicality premise is needed
for the projection-only encoding theorem.

The shared confidential encoder can also support the amount family: its
explicit payload is Word64 rather than an asset hash. The indexed and current
transports reuse the previously checked payload-polymorphic index bridge and
current-input/assertion semantics, with explicit word depth and payload types.

## Completed checks and honest boundaries

The new module has nine results and six definitions. Three encoder/projection
results are closed; the three primitive transports retain functional
extensionality. Each whole-C endpoint has exactly the six inherited project
assumptions and no added libc model.

Checker 55689 terminated with exit 0: it freshly recompiled the original
`C.jet_elements_asset_jets` and `C.jet_elements_current_input_jets` execution
modules before the new `C.jet_elements_asset_literal`, printed all fifteen
full new type/definition records and actual assumption sets, regenerated the
Elements AST and recursively kernel-checked the new module's full closure.
Source/object hashes and exact commands/logs bind all three fresh modules.
No admissions, assumed declarations or unchecked casts are used.

Independent review 81359 terminated with exit 0: selected canonical/source
correspondence, 64 packed-field/asset/current/representation/whole-C source
corruptions and 38 independent proof/evidence/object corruptions passed.
`EVIDENCE-REVIEW.json` binds the checked receipt, all tools and all three review
command/log results. The guard pins the actual Haskell packed-field projection,
proof-clearing views, literal programs, Coq port/representation definitions,
both versions of all three complete C contracts and actual C bodies. This is
not a proof of host lens/compiler behavior, field arithmetic, or environment
construction. LP64/RECKLESS and the larger imported kernel context remain
explicit and distinct from the six assumptions of each endpoint.

Normal registration and full acceptance are separate next steps. Do not
repeat completed checker/review runs. Main remains 401/533; main401 audit 92989,
isolated402 audit 26900 and combined407 audit 23810 continue on frozen inputs.
The combined407 candidate is not to be changed to add these getters during its
audit. Prepare a separate successor over its reviewed source if registering
these proofs. The entire original staged patch remains preserved. The full
every-jet goal, including 104 explicit `memcpy_model` conditions, is unfinished.
