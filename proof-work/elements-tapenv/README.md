# Elements tap_env_hash: literal program composition and original C getter

`C.jet_elements_tap_env_hash_program` defines the original program composition:
initialize SHA, absorb the tapleaf hash, then the tappath hash and `InternalKey`,
and finalize. It reuses the checked generic Reader and SHA results, the literal
Elements tapleaf semantics, and the checked 8-bit tappath program semantics.
The final theorem covers actual `f_simplicity_tap_env_hash` execution in
`elements_ge`, with the computed value in the explicit taproot cache/frame
relation at offset72. It does not assume the desired C execution/output.

The complete fresh dependency/module compilation and type/assumption reporting
phase passed:

The native Haskell `Schnorr.PubKey` wraps `Word256`; `encodeKey` uses its integer
conversion. This getter/program does not deserialize arbitrary bits as a field
element or prove curve validity. Host-library correspondence and actual caller
cache establishment remain separate obligations; source review must preserve
this native-word boundary.
