# Direct 256-bit hash getters: actual C to literal specifications

The actual `simplicity_script_cmr` and `simplicity_genesis_block_hash` C jets
now have checked contracts against the selected Haskell primitive/program
interpretations. They return the supplied environment digest, decoded through
the literal big-endian byte fold into Haskell's four-limb numeric `Word256`,
then through `Ty.Word.toWord256`. This does not replace a required hash value
with an unrelated mathematical specification or assume the C execution.

The final theorems retain the original `application_jet_local_spec_sep`, actual
C functions, `elements_ge`, `Elements.env`, `Unit -> Word256`, original initial
representations/footprints and complete execution/output/prefix/cursor/memory
postconditions. The CMR representation reads the taproot pointer at environment
offset 8 and the eight words at taproot offset 136. Genesis reads its eight
words at environment offset 16. Their original bounds and separation premises
are unchanged. Invalid pointers/frames are not claimed as valid inputs.

## Reusable representation bridge

`source/jet_haskell_hash_word.v.source` contains 27 **closed** lemmas. It models
the four ordered unsigned 64-bit limbs explicitly, including `fromInteger`'s
successive divisions and truncation, `toInteger`'s Horner expression, pointwise
OR, lifted left-shift, and the tail-recursive byte fold starting at zero.
Reachable limb bounds are proved, not assumed. The fold's integer result is
the byte-Horner value modulo 2^256, for arbitrary byte lists; the shared
all-width `toWord` lemma accounts for that modulus without enumerating values.

The bridge also proves the VST/Simplicity digest byte representation's 32-bit
word decomposition, regroups its bytes into eight registers, proves the exact
integer view of `Word.from_hash256`, and concludes
`haskell_hash_word256`: literal Haskell digest conversion equals the existing
canonical Coq word encoding. A generic four-digit radix lemma is reused for
both the 64-bit numeric limbs and the four bytes of each 32-bit register.
The hash's represented byte length is proved to be 32.

`source/jet_elements_hash_literal.v.source` uses one generic field-based literal
specification, two interpretation bridges and the previously checked shared
separated-contract transport to obtain the two full C contracts. Each final
dependency set equals that of its original C theorem: the same six inherited
assumptions, no additional libc model or proof shortcut. These results concern
the two direct digest fields only. In particular they do not establish that
arbitrary cached hashes were computed correctly, or identify the widened
field/public-key carriers in other primitive clauses with valid curve values.

## Verification evidence

The source guard follows the actual selected jet/primitive identities, digest
fields, hidden hash carrier/32-byte serialization convention, big-endian
adapter, four-limb `Simplicity.Word` implementation, balanced `toWord256`, Coq
ports, exact initial representations and whole C contract statements. It
reuses the already reviewed generic word traversal/transport dependency.
This is a checked Coq model with source-correspondence guards, not a verified
translation of the Haskell compiler or its standard libraries.

## Normal integration remains pending

After those admissions complete, recompile these modules under final `C`
names, include both original-C getter modules and the checked literal bridge
in normal manifests/public/definition registries, integrate the selected
source guards/mutations and exact coverage shapes, review all inherited/new
snapshots and run full acceptance. It may be efficient to batch this with the
already checked tapleaf getter. Do not count them before admission. Retain the
original staging/source map plus an exact owned delta, as in the count batch;
do not sweep the user's dirty registries into a commit. These receipts cover
the actual copied working checkout, including the preexisting shared word
converter, not a clean-HEAD build. The all-jet goal remains unfinished.
