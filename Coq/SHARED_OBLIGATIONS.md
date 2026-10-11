# Shared obligations — continuation record

Branch `claude/shared-obligations`, worktree `simplicity-shared`, fork point
`a8685146` of `feat/jet-equivalence`. Local commits only. The shared
registries (`_CoqProject.jets`, `jet_coverage.tsv`, `jet_public_theorems.txt`,
`*.expected`, `check-jets.sh`) are untouched: nothing here is registered
coverage; integration belongs to the owner of the main checkout
(coordination notes: `../COORDINATION.md`).

No admissions, no new assumed declarations, no edit to production C, to
canonical Simplicity, or to any accepted Coq module. All results use only
assumptions already inherited by the accepted proofs, except one linking
statement that inherits `Axioms.proof_irr` from CompCert's own `link_program`.

## 1. Concrete memcpy and linkage — `linked/README.md`, `linked/RECEIPTS.md`

- `C/jet_memcpy_exact.{c,v}` (+ generated `C/memcpy_exact.v`): libc-ABI
  memcpy, internal Clight function, meets the conclusion of `memcpy_model`
  under its premises for arbitrary memory values.
- `C/jet_memcpy_impl.{c,v}`: plain byte loop; same conclusion for initialized
  data bytes (not linked: the contracts do not provide that premise).
- `linked/`: derived tree in which the core and SHA programs bind `memcpy` to
  the exact definition; accepted proof scripts compile unchanged; 124
  `_linked` contracts (104 core, 20 SHA-unit) without `memcpy_model`; both
  linked programs are CompCert's `link` of the accepted program with the
  memcpy unit.
- `C/jet_memcpy_model_consistent.v`: `memcpy_model_consistent` — there is an
  assignment of semantics to all external functions satisfying CompCert's
  `extcall_properties` for every name/signature under which the statement
  of `memcpy_model` holds (memcpy interpreted as the libc contract). So the
  premise of the 124 accepted conditional theorems does not contradict
  CompCert's axioms on external functions and those theorems are not
  vacuous on that account. Closed under the global context; coqchk exit 0;
  SHA-256 `f9458776eda459f36eb9690bdb5ba7c48b4542d395ea5499555c84eac55de6af`.
  This is model existence, not a discharge of the premise.
- **Boundary:** theorems about the linked programs. The accepted theorems for
  the unchanged programs keep `memcpy_model`; nothing in Coq can discharge it
  for an external function.

Verify: `bash Coq/audit-linked.sh`.

## 2. SHA initialization and preservation — `startup/README.md`, `startup/RECEIPTS.md`

- `sha_startup_state` (dispatch pointer, max counter, three tag arrays incl.
  two writable ones) from `Genv.init_mem jets_sha.prog`.
- Preserved by all 21 SHA-unit jets with a state premise, using only the
  public frame contract; by caller setup operations on other blocks; along
  arbitrary lifecycles mixing both (`sha_lifecycle_state`, via Clight
  determinism).
- Caller obligations about global objects removed from the three
  environment-reading hash jets.
- Each jet runs on freshly constructed frames for every input.
- Linked variants (no libc premise, no global-object premise):
  `linked/startup/jet_sha_startup_linked.v`.
- **Boundary:** `eval.c` is not in a proof translation unit, so the actual
  evaluator is not shown to be such a lifecycle; a run-time dispatch
  optimizer is a different program state.

Verify: `SHA_SUPPORT=<main>/proof-work/sha-support bash Coq/build-startup.sh --check`
and `... bash Coq/build-linked-startup.sh --check` (after `build-linked.sh`).
Two archived prerequisites are referenced by hash, not copied.

## 3. Shared representation — `C/JET_FRAME_CONSTRUCTIBLE.md`

- Frame premises of all frame-only contracts are constructible for every
  input; 310 registered jets instantiated (`jet_frame_executable_registry.v`),
  plus the 36 Bitcoin application jets given a represented environment
  (`jet_app_executable_registry.v`): 346 of 349 registered jets.
- `bm_rep`/`bm_separated`/`active_write_writable` are jointly satisfiable for
  every Bit Machine state within addressability bounds; `jet_context` and
  `jet_context_separated` therefore apply to every context and input.

Verify: `bash Coq/build-jets.sh --coqchk -silent -o
C.jet_frame_constructible_context C.jet_frame_executable_registry
C.jet_frame_constructible_bm` (after building the registered core modules).

## Open items (unclaimed unless noted in `../COORDINATION.md`)

1. Environment relations of the 36 Bitcoin jets: stability and executability
   are done (`C/jet_env_rep_stable.v`, `C/jet_app_executable_registry.v`);
   *constructing* a representing memory for every logical environment is
   open (per-relation work).
2. secp contract shape: executability instances (needs the secp unit built).
3. Linked-tree instances of the executability registry (104 memcpy jets
   become unconditional end to end): generator sketch in section 1's tree;
   requires building the remaining core modules in `linked/tree`.
4. A plain-C memcpy link would need a data-byte frame invariant threaded
   through the copy family; not started.
5. Integration: the archived `proof-work/sha-support/jet_sha_global_frame.v.source`
   does not compile at `a8685146`; `startup/proofs/jet_sha_startup_globals.v`
   carries the one-line fix.

## Build notes

- `build-jets.sh` always builds `all`; the scripts here generate the makefile
  themselves to build selected targets.
- SHA chain: ~15 min to build at -j6 (`jet_sha_finalize_bridge.v` ≈ 7 min);
  coqchk of the SHA chain ≈ 20–60 min.
- Never copy onto a path that may be a symbolic link into `Coq/C` (see the
  incident note in `linked/RECEIPTS.md`).
