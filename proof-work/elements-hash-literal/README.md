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

Candidate: `/private/tmp/jet-elements-hash-literal.MumnoF`.
Namespace: `HashLiteral` in its separate `Proof/` directory.
Source/object base: the sealed tapleaf-version tree
`/private/tmp/jet-elements-tapleaf-literal.VNAVqR`. The inherited six tapleaf
dependency objects and eighteen sequence dependency objects are checked
against their existing source/object receipts. Both original C getter modules
and both new modules were explicitly freshly compiled; no source was changed
in the inherited Coq tree or either live acceptance run.

The driver printed all 31 new result types, the two original C types, and the
definitions giving their meaning, with explicit implicit parameters and no
ellipsis/unresolved placeholder. It checked every result's assumptions,
recursively kernel-checked the actual-C closure, regenerated and byte-compared
the production Elements AST, checked source correspondence and ran nineteen
in-memory source corruptions. Ten independent scope/source/object/assumption/
terminal receipt corruptions are also rejected. Invalid proofs are never
compiled. The fifteen inherited library-context axioms and empty unsafe
categories remain unchanged. Complete durable reports are `contracts.log`
and `assumptions.log`; `REVIEW.json` binds sources, objects, commands, exits,
tool hashes and full terminal evidence.

The source guard follows the actual selected jet/primitive identities, digest
fields, hidden hash carrier/32-byte serialization convention, big-endian
adapter, four-limb `Simplicity.Word` implementation, balanced `toWord256`, Coq
ports, exact initial representations and whole C contract statements. It
reuses the already reviewed generic word traversal/transport dependency.
This is a checked Coq model with source-correspondence guards, not a verified
translation of the Haskell compiler or its standard libraries.

```sh
python3 -B proof-work/elements-hash-literal/review.py
python3 -B proof-work/elements-hash-literal/test-review.py
ulimit -s 65520
python3 -B proof-work/elements-hash-literal/finish.py /absolute/hash-tree
```

## Normal integration remains pending

No main proof source, registry, manifest, snapshot or compiled object was
installed; this batch adds **zero registered coverage**. Main's count audit
(session 49451) and the isolated sequence admission (53695) remain distinct
live runs: do not modify their inputs or restart them on an observation
timeout. Both have passed their kernel stage and reached assumption auditing
at this milestone; poll their actual handles for later state.

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
