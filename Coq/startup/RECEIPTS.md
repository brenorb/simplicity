# Receipts — SHA startup invariant

Environment: Coq 8.17.1 (opam switch `simplicity`), CompCert 3.14, VST 2.14,
stack 65520 KiB. Fork point `a8685146`. Prerequisites (read-only, from the
main checkout's `proof-work/sha-support`, verified by `build-startup.sh`):

| file | SHA-256 |
| --- | --- |
| `jet_clight_forward.v.source` | `6d60b8220d833178e2c3a0abd219a79925eedc5a35d9e42dbb5f9f2601197515` |
| `jet_sha_initial_globals.v.source` | `a82426e6fde0b53adf9e1a25fa88098098d562a349d9817fc57701f9c50a2788` |

## 2026-10-11 — `bash Coq/build-startup.sh --check`, exit 0 (21 min)

Sources at commit `38501bec`.

- Generated `jet_sha_startup_runs.v` byte-identical to the committed file.
- No `admit`/`Admitted`/`Axiom`/`Parameter`/`Conjecture` in `startup/proofs`.
- `Print Assumptions` for all 87 theorems/lemmas of the nine modules: each
  within `ClassicalDedekindReals.sig_forall_dec`, `sig_not_dec`,
  `Classical_Prop.classic`, `functional_extensionality_dep`,
  `Events.external_functions_sem`, `Events.inline_assembly_sem`,
  `Events.external_functions_properties`, `Events.inline_assembly_properties`
  (the eight assumptions already inherited by accepted SHA-unit results; the
  two `_properties` axioms enter through forward-memory and determinism
  lemmas). 21 jet contracts over the invariant.
- `coqchk -silent -o` on `jet_sha_startup_{globals,state,jets,env_jets,setup,
  env_callers,executable,runs,lifecycle}` and their whole dependency chains
  (accepted SHA unit included): passed.

| module | SHA-256 |
| --- | --- |
| `jet_sha_startup_globals.v` | `27b06100698b9b4f55fa75f604489a24359e44332ecc30fe3996b25eba651116` |
| `jet_sha_startup_state.v` | `e8b0b15ad6c65695d9571415a22457768ac3e5729a113f9be17835653dd85941` |
| `jet_sha_startup_jets.v` | `a6d17f9730ea96f131414f5c45ca0efe66b2623e12030457953bdb457f28109b` |
| `jet_sha_startup_env_jets.v` | `4c0bd54d63d0ac8b28b3476b674ae7d23514f2a6693af537bfe18181f6cd3652` |
| `jet_sha_startup_setup.v` | `007e63bd0bc35fe419fa8edebaecb3d6f660bcdacba8d299760730b140a97e1e` |
| `jet_sha_startup_env_callers.v` | `3f6c935387a5fd3635b1c9b3b23619536b743dfa27b45685036dcf7217c51932` |
| `jet_sha_startup_executable.v` | `a9dbc1acbc8ab7eb67380e2792d5428a795926c3f5a0e5583c927c94794e4aac` |
| `jet_sha_startup_runs.v` | `28c506fbfb58bc3ff012265e323ccded14ed598658211e6c4fd3cf597485274b` |
| `jet_sha_startup_lifecycle.v` | `1b36e3253d81bf4b2e070ba15506e258f760dfbd8be6cfb4c927284de2d2d738` |

## `jet_sha_startup_init.v` (added after that pass, commit `eeb63cd9`)

SHA-256 `19167d194d7b632d465f488499c042a8965a33e92618c9ca1c3841140cd9e16b`.
Compiled; `Print Assumptions sha_init_mem_exists`: closed under the global
context; `sha_startup_state_exists`: the four logic axioms;
`sha_lifecycle_exists`: those plus `external_functions_sem`,
`inline_assembly_sem`. Included in the module list of `build-startup.sh`
from the next pass on (see the dated entries below).
