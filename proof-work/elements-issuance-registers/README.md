# Issuance asset/token register bridges

`Registers.v.source` contains nine closed lemmas, including the three exact
canonical-program/register equalities needed to connect the existing C helper
proofs in `Coq/elements-env/C/jet_elements_env_calc{,_token}.v`:

- asset: compress the IV with the eight entropy registers and eight zero words;
- explicit token: the entropy registers followed by `0x01000000` and seven zeros;
- confidential token: the entropy registers followed by `0x02000000` and seven zeros.

The shared block-pair and compression lemmas use the existing formally proved
`Simplicity.SHA256.hashBlock_correct`; only closed IV/zero/token constants are
computed. There is no symbolic whole-program evaluation or new assumption.
These are representation bridges for implementation composition, not new
claims about mathematical correctness, helper linkage or complete C jet calls.

Next composition obligations remain explicit: transport/link the existing
derived-unit `eval_calculateAsset`/`eval_calculateToken` results to the original
Elements jet program, establish their initial owned-memory requirements and
sequence the actual public reader/helper/writer lifecycle. The entropy
double-hash/byte-order bridge and production environment-cache establishment
are separate remaining work. Do not substitute a derived translation unit's
execution theorem for the original jet's call.

The existing core-only `C.jet_transport` is not directly applicable to these
helpers: it deliberately rejects external calls and global-variable reads,
whereas calculateAsset/calculateToken use `memcpy` and the SHA dispatch global.
Do not just add them to `elements_core_helpers` or assume genv equality.

A more direct reuse route already exists in
`Coq/elements-sha/C/jet_elements_sha_program.v`: in a **distinct derived proof
tree**, `C.jets_sha` is an exact copy of the original `C.jets_elements` AST, and
the checked `elements_sha_program`/`elements_sha_genv` lemmas establish program
and genv equality. Recompile the minimal existing calc/calc_token dependency
closure in that original-program overlay, reusing the Elements SHA/tapleaf
support. The environment field-evaluation dependency is generic. Check every
actual body/layout/symbol lemma, preserve explicit `memcpy_model` and dispatch
premises, and use program equality to state the result for `elements_ge`.
This changes neither production C nor generation settings. Do not overwrite
the main SHA unit, reuse its incompatible objects, or import the environment
unit's theorem without this rechecking. Only then compose these register
equalities and the public jet lifecycle, and discharge startup/caller premises.
