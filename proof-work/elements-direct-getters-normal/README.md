# Direct getters: final C namespace preparation

The checked tapleaf-version, script-CMR and genesis-block-hash getter proofs
now also compile and pass recursive kernel checking under final `C` names.
The two direct-hash endpoints share the closed four-limb/byte/word conversion
bridge; the byte getter reuses the same generic `toWord` infrastructure.
All three preserve their original full separated C contracts, initial memory
representations and framing guarantees, with exactly the original six
inherited assumptions and no new libc premise. The 27 shared digest lemmas
remain closed under the global context.

Verification includes 33 new result types, the three original C types, all new
definitions, per-result assumptions, recursive `coqchk -silent -o`, and both
selected source guards plus their 13 byte and 19 digest corruptions. Reports
reject elision or unresolved print placeholders. The inherited fifteen-axiom
library context and all three empty unsafe categories are unchanged. Original
C AST fidelity is established by the hash/tapleaf source receipts on these
unchanged program sources, and is still required in later normal acceptance.

No main Coq source, manifest, registry, snapshot or compiler object was
installed. This adds **zero registered coverage** and is not full normal
acceptance. The complete main source map and preexisting staged patch were
unchanged throughout preparation. These receipts describe the actual copied
checkout, including preexisting shared converter work, not a clean-HEAD build.

## Next normal admission

First finish the existing sequence audit and its exact reviewed installation;
main's count acceptance has now actually completed successfully. Keep the
sequence candidate frozen until its terminal result. Its new installer and
postcheck require both successful predecessor receipts and preserve every
original staged byte; syntax checks of those helpers are not an installed-main
success claim.

Then admit this three-jet batch against the following canonical C contracts:

- `simplicity_tapleaf_version`:
  `C.jet_elements_tapleaf_version_local.elements_tapleaf_version_local_spec`.
- `simplicity_script_cmr`:
  `C.jet_elements_script_cmr_local.elements_script_cmr_local_spec`.
- `simplicity_genesis_block_hash`:
  `C.jet_elements_genesis_hash_local.elements_genesis_block_hash_local_spec`.

Append the eleven dependency modules to both manifests, register their public
results/definitions and the literal bridges, and preserve all inherited
contract records byte-for-byte/in order and all inherited assumption sets.
Coverage allows only the three exact separated `Elements.env` contracts:
`Unit -> Word8` for tapleaf, `Unit -> Word256` for the two digests. Retain all
previous Elements restrictions. Add negative coverage fixtures and integrate
both source guards/mutation suites into mandatory normal acceptance.

The contract printer must expose implicit parameters of **new modules only**,
including `C.jet_haskell_hash_word`; do not change inherited print behavior.
Load that numeric helper with `Require`, not an incidental broad import, if
needed to keep inherited names byte-identical. Print its record definition as
well as functions/fixpoints. Run the ordinary whole-registry contract
comparison before full acceptance. Only after reviewed isolated acceptance,
exact-delta installation and actual-main verification may the three entries
be counted. A proposed 371/533 is not a result of this preparation.

Do not conflate this direct-digest bridge with validation of cached hashes,
SHA/caller initialization, elliptic-curve/public-key representation or the
full evaluator. Those and every other uncovered jet remain work for the
unchanged all-jet goal.
