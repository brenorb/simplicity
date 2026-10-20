# Elements tapleaf_hash: compiled literal-tag C-to-program checkpoint

`source/jet_elements_tapleaf_hash_program.v.source` contains the original
Elements `f_simplicity_tapleaf_hash` execution contract against the literal
tagged-hash Simplicity program using `TapleafVersion` and `ScriptCMR`.
The usual explicit separated frame/cache relation remains. The cached field
is the taproot hash at offset8; this result does not establish caller setup.

The tag prefix is constructed from the sixteen ASCII bytes of
`TapLeaf/elements`, SHA-256 of those bytes and compression of the repeated tag
digest. The word uses the checked Haskell/native-hash converter. There is no
unconnected assumed numeric midstate. The exact string and word/leaf-size
bridges are proved; the actual tagged-context absorption/finalization proof
is reused from the Bitcoin development with this different prefix.

The complete fresh compiler/report phase passed:

The evidence reviewer checks the original main420 source map against actual
immutable private-tree bytes and its accepted baseline fingerprint. It does
not require today's main to remain420 forever. The review recorder separately
checks preservation of the actual live main/index during its run. This avoids
confusing historical proof evidence with a successor's current source state.

Main420 and the private443 full audit remain frozen and separate. Normal
registration/admission remains; no additional accepted coverage or full normal
acceptance is claimed here. Host-library equivalence and actual caller cache
establishment remain separate.
