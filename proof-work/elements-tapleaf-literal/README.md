# Literal 8-bit tapleaf-version C contract

The actual `simplicity_tapleaf_version` C getter now has a checked contract
against the literal Haskell `Elements.TapleafVersion` interpretation:
`toWord8 . toInteger . tapleafVersion` of the taproot environment. This is an
implementation-to-specification result, not a mathematical specification-only
identity. The final theorem retains the complete
`application_jet_local_spec_sep`, actual C function and `elements_ge`, logical
`Elements.env`, `Unit -> Word8` types, original environment/footprint relation,
Clight execution, output, prefix, cursor and memory guarantees.

The two new results are the literal interpretation bridge and its full C
contract. They reuse `haskell_to_word_matches` at depth **3** (eight bits) and
`application_jet_local_spec_sep_pointwise` unchanged. The sequence proofs use
the same all-width converter at depth **5** (32 bits). Thus the shared
structure is exercised by actual C endpoints at both widths; no enumeration,
new axiom, assumed execution or weakened postcondition was introduced.

The initial representation still requires the taproot pointer at environment
offset 8, the unsigned byte at taproot offset 169, the original representable
record bounds and footprint, and the shared valid-frame premises. The theorem
does not claim correctness for arbitrary invalid bytes/pointers. The literal
bridge uses inherited functional extensionality via the word converter; the
final result has exactly the original six inherited assumptions and no extra
libc premise. This does not prove environment-builder/evaluator composition.

## Evidence

This batch adds **zero normal registration/coverage** and changed no main
proof, registry, snapshot or compiled output. It ran while the main count and
isolated sequence acceptances stayed frozen. The original staged patch is
unchanged. The evidence describes the actual copied checkout, including the
preexisting shared converter, not a clean-HEAD build. After the current
admissions finish, recompile under the final `C` namespace, integrate this
source correspondence and its mutation tests, review exact metadata/snapshot
deltas and run full normal acceptance before counting this jet.
