# Canonical Elements tapEnvHash and native key source correspondence

The recorded positive check and all38 read-only corruption fixtures passed.
`SOURCE-REVIEW.json` and the exact logs bind the candidate, sources, commands,
zero exits and checker versions. The fixed model pins eight whole Coq
definitions/statements; it is not regenerated while checking.

The inherited tapleaf/stream guards cover the actual Elements SigHash library
body, literal tag construction, 8-bit tappath loop, word/hash representation,
primitive port, SHA helpers and separated C getter contracts. This extension
checks `TapEnvHash` catalog/wrapper bindings, the complete composed program,
its raw computed hash value, the actual C getter and the entire final theorem.

The key boundary is explicit: the environment's native `Schnorr.PubKey` wraps
native `Word256` and `encodeKey` uses `toWord256 . toInteger`. The Simplicity
program type `PubKey` is separately an alias for Simplicity `Word256`. The
`Spec` module re-exports, rather than shadows, that native key constructor.
Nothing here decodes arbitrary word bits as field elements or assumes curve
validity. The source tests reject those substitutions, as well as swapped
component hashes, wrong primitives/SHA lengths/C fields and weakened/vacuous
endpoint contracts.

This is source-correspondence review, not a formal verification of host
Haskell/SHA libraries. It does not establish caller cache construction, claim
recursive kernel success, register a jet or constitute full normal acceptance.
