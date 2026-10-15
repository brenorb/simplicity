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

Candidate: `/private/tmp/jet-elements-tapleaf-literal.VNAVqR`.
Namespace: `TapleafReview`, in its separate `Proof/` directory.
Read-only source/object base: the sealed final-namespace sequence tree
`/private/tmp/jet-elements-sequence-normal.gDntta`. Its eighteen source/object
bindings are checked unchanged. Six additional existing dependencies were
freshly compiled: write32s execution/layout, hash-write/getters, write8-step
and the original tapleaf-version C module. No inherited source was edited.

Fresh compilation, three fully quantified type prints (two new and the
original C contract), four complete definition prints, per-result assumption
comparison, recursive `coqchk -silent -o`, and exact production Elements AST
regeneration all passed. The fifteen inherited library-context axioms and
empty unsafe categories are unchanged. Complete reports are `contracts.log`
and `assumptions.log`; the source archive is
`source/jet_elements_tapleaf_literal.v.source`.

The selected source guard reuses the shared sequence-conversion dependency
review and additionally checks the canonical tapleaf catalog/primitive
dispatch, unit-domain convention, unsigned byte carriers, Word8 tree shape,
literal byte conversion, initial representation and whole actual-C contract.
Thirteen in-memory source corruptions are rejected. Ten independent receipt
corruptions reject unearned coverage, source/object drift, unsafe flags,
missing kernel stages and changed assumptions. Bad proof text is not compiled.
`REVIEW.json` binds source/objects, commands, successful exits, complete logs,
source guards and inherited source fingerprints.

```sh
python3 -B proof-work/elements-tapleaf-literal/review.py
python3 -B proof-work/elements-tapleaf-literal/test-review.py
ulimit -s 65520
python3 -B proof-work/elements-tapleaf-literal/finish.py /absolute/tapleaf-tree
```

This batch adds **zero normal registration/coverage** and changed no main
proof, registry, snapshot or compiled output. It ran while the main count and
isolated sequence acceptances stayed frozen. The original staged patch is
unchanged. The evidence describes the actual copied checkout, including the
preexisting shared converter, not a clean-HEAD build. After the current
admissions finish, recompile under the final `C` namespace, integrate this
source correspondence and its mutation tests, review exact metadata/snapshot
deltas and run full normal acceptance before counting this jet.
