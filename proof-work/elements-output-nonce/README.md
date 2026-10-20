# Elements output_nonce: literal specification and original C execution

The full `elements_output_nonce_literal_local_spec` theorem compiles and passes
recursive kernel checking. It reuses the existing actual-C execution theorem
through a proved specification transport; it is not merely a statement that
two specifications coincide. No normal coverage has been added yet.

## Exact scope and reuse

The literal specification follows `primitive OutputNonce`, optional output
lookup, and optional nonce encoding. It distinguishes an absent output, an
absent nonce, an explicit hash nonce, and a parity/native-Word256 nonce. The
latter is **not** a Schnorr field element: the Haskell carrier is
`Either (Bool, Word256) Hash256`, and its native word uses `toInteger`, not
`fe_repr`. The four-limb word model and digest decoder are reused unchanged.

`word_indexed_value_literal_matches` generalizes the existing digest-only
indexing bridge to any payload encoder, word depth, and finite list. Future
indexed getters need only prove the encoder correspondence. It is closed, as
are the native-word bridge, nonce encoder bridge and32-bit index range. The
primitive semantic transport has the inherited functional-extensionality
dependency; it is not axiom-free. The whole-C endpoint has exactly the six
inherited project assumptions, with no added libc model or execution premise.

The inherited C theorem derives entry/source-frame copying, actual `read32`,
count comparison and indexing, `nonce`/`writeHash`/bit-writing/skipping calls,
return and freeing locals, with output/prefix/cursor and memory framing over
arbitrary initial output contents. The literal theorem preserves its exact
`indexed_ptr_rep` relation and offsets248/144/8/704. Initial represented arrays,
pointer/readability bounds and footprints remain explicit. This batch does
not prove real environment-builder construction or generalize that inherited
array relation's treatment of null pointers for empty arrays. LP64/RECKLESS
and host-library/fidelity boundaries are unchanged.

## Verification

The selected canonical guard checks the Haskell catalog/primitive/field
carriers and raw-word/bit encoding, the corresponding Coq definitions, both
full C contracts and initial nonce representation, actual C helper/jet bodies,
prefix enums and absent-case padding. It reuses the completed indexed and
native-word guards; it is not a formal proof of host-library behavior.

Main401 audit92989 and isolated402 audit26900 remain live on immutable semantic
inputs. The reviewed404 and406 candidates are not installed. The every-jet
goal, including104 explicit `memcpy_model` conditions, remains unfinished.
