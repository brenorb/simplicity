# Literal Elements input-sequence bridge

The actual `simplicity_input_sequence` C jet now has an independently checked
contract against the literal Haskell primitive interpretation: decode the
input with `fromWord32`, perform the indexed lookup, return Left for absence,
and encode a present unsigned sequence with the literal `toWord32` state
traversal. The proof retains the original complete
`application_jet_local_spec_sep` execution/output/prefix/cursor/load-framing
contract, `elements_ge`, logical environment and initial footprint relation.
It does not assume the C execution or result being proved.

The module has five results:

- Two closed, all-width input-decoder lemmas, including the arbitrary integer
  accumulator. They reuse `word_modulus_S`; there is no exhaustive enumeration.
- The formal bridge from the canonical primitive program's denotation to the
  literal input/output conversion interpretation, reusing the existing shared
  `haskell_to_word_matches` lemma.
- A generic pointwise transport lemma for separated application contracts.
- The actual-C local contract transported through those proved equalities.

This is not merely a mathematical identity between specifications. The final
result still requires and concludes the actual Clight execution and full
observable postcondition. Its assumption set equals that of the inherited C
contract: the six inherited assumptions, with no extra libc premise. The two
new decoder lemmas are closed; the interpretation bridge additionally uses
the already-inherited functional extensionality assumption through the shared
output conversion.

## Verification and scope

The selected source guard checks the catalog dispatch, primitive identity,
unsigned record field, lookup/presence embedding, both literal Haskell word
algorithms, their Coq ports, and the exact original-C endpoint/representation.
Twenty-four in-memory mutations are rejected without compiling bad proofs.
Ten separate receipt/source/command/evidence corruptions are also rejected.
No other Elements primitive semantic clause is certified by this guard.

The existing all-width output converter is reused without editing its source
(`C/jet_haskell_word_conversion.v`, already in the current normal manifest).
That source is among the preexisting untracked/staged main work: this receipt
describes the current copied checkout, not a clean-HEAD build. The shared
converter's exact source hash and read-only dependency fingerprint are pinned.
The existing indexed-scalar C proof and frame predicates are reused unchanged.

No main Coq source, metadata or compiled object was installed. Registration
and normal acceptance remain pending; coverage is unchanged by this module.
The current-sequence getter was inspected but is **not** claimed proved by this
batch. The complete Elements environment builder and evaluator composition
also remain separate obligations. All work stayed outside the ongoing count
audit's frozen inputs.

`finish.py` is the compiler/checker driver, not a coverage generator. A later
normal integration must compile the module under its final C namespace,
review its registry/snapshot additions and pass full acceptance.
