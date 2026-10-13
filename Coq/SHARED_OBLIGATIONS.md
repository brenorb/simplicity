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

1. Environment relations: stability and executability are done
   (`C/jet_env_rep_stable.v`, `C/jet_app_executable_registry.v`).
   *Constructing* a representing memory for every logical environment:
   - generic steps: `C/jet_env_constructible.v` (stores into fresh blocks,
     word arrays, record parts, arrays of structured elements; `built`,
     `elem_local`, `elem_buildable`), independent of any translation unit;
   - Elements: `C/jet_elements_env_constructible.v` (indexed, current-pointer
     and current-generic relations), `C/jet_elements_elem_buildable.v`
     (every element relation), `C/jet_elements_runs_everywhere.v` — 30 jets
     with statements that carry no memory, frame or environment premise
     (`runs_everywhere`). Six inherited assumptions; coqchk exit 0 at
     `1fe00a21` together with all other Elements modules (80 s);
   - Bitcoin (**all 36 registered application jets, done**):
     `C/jet_bitcoin_env_constructible.v` (13: record-only relations),
     `_indexed.v` (8: indexed and current-input), `_distance.v` (4) and
     `_raw.v` (11: script_cmr and the ten raw-environment jets), over
     `C/jet_env_constructible_array{,_x}.v`. Statements
     `bitcoin_runs_everywhere`, `bitcoin_partial_runs_everywhere` (assertion
     jets: the C verdict is the canonical one) and `raw_runs_everywhere`: no
     memory, frame or environment premise. For raw environments the one
     remaining hypothesis is the input requirement of the accepted raw
     contracts, a tap path of at most 128 elements. Six inherited
     assumptions each; `coqchk -silent -o` on the four modules with whole
     dependency chains at `72bec58e`: exit 0 (90 s);
   - Elements: all 50 proved jets (`C/jet_elements_runs_everywhere{,_rest}.v`);
   - SHA unit: the three environment-reading hash jets, on top of any memory
     with the startup invariant (`startup/proofs/jet_sha_startup_env_runs.v`,
     `sha_env_runs_everywhere`; linked variants without `memcpy_model` in
     `linked/startup/jet_sha_startup_linked.v`). Constructed memories are
     extensions (`C/jet_env_constructible_ext.v`), which is what carries
     the invariant through the environment construction.
   Kernel receipt for this item after the `built` strengthening (all
   dependents rebuilt): `coqchk -silent -o` on the four Bitcoin environment
   modules, `jet_env_constructible_ext`, both Elements `runs_everywhere`
   modules and the five Elements executability modules, with whole
   dependency chains, at `e4655dcf`: exit 0. `Print Assumptions`: the six
   inherited assumptions for each of the 36 + 50 no-premise theorems.
   What these results do not say: that `C/bitcoin/env.c` builds such a
   memory from a serialized transaction (it is in no proof translation
   unit); they show the relations are satisfiable for every logical
   environment and that the C jets then compute the canonical result.

2. (done) secp contract shape: `C/jet_frame_constructible_secp.v`; all 349
   registered jets have an executability instance.
3. (done) Linked executability: `linked/C/jet_frame_executable_linked.v` —
   the 104 memcpy jets run unconditionally in the linked program.
4. Plain-C memcpy link — characterized, blocked for the frame copies.
   The jet units call `memcpy` at `frame.c:237` (bulk copy of frame words)
   and `sha256.h:213/230/238` (hash words and message bytes). A byte loop
   `*d++ = *s++` is only defined in CompCert's Clight when every source byte
   is a data byte (`C/jet_memcpy_impl.v` has exactly that premise): the
   implicit cast of an undefined or pointer-fragment byte has no semantics
   there, although ISO C allows copying such bytes through `unsigned char`.
   Frame words legitimately contain undefined cells (the contracts carry
   `None` cells, e.g. after `skipBits`), so the bulk frame copy cannot be
   linked to a plain loop without changing the frame contracts; this is a
   limit of the memory model, not of the C code. The exact variant
   (`EF_memcpy`) has no such premise and is what `linked/` uses. For the
   three SHA call sites the copied bytes are always data, so a plain-loop
   link is possible in principle there, but it needs the data-byte fact at
   each call site and therefore re-proving those call sites rather than
   reusing the accepted scripts; not started.
5. Integration: the archived `proof-work/sha-support/jet_sha_global_frame.v.source`
   does not compile at `a8685146`; `startup/proofs/jet_sha_startup_globals.v`
   carries the one-line fix.

## Elements (unregistered; `C/JET_ELEMENTS.md`)

50 Elements jets proved in `elements_ge` against their canonical
specifications, each with an executability instance; the canonical side is
a Coq port of the Haskell primitive semantics that still needs source
review. `issuance_token_amount` and its `current_` variant, whose static
helper passes a stack-allocated compound literal, were blocked on the
closed-world shape of `write_effect` (all loads outside the output ranges);
they are now proved in `forward/` (see `forward/README.md`) with
`write_effect_x` (effects up to one private block,
`C/jet_elements_effects_local.v`) and the archived forward-memory property
of Clight executions, at the price of the two CompCert `_properties`
assumptions the accepted SHA-unit results already inherit.

## SHA jets and start-up invariant for the Elements unit — `elements-sha/README.md`

The accepted SHA proof chain recompiled against the Elements program (14 SHA
jets for `elements_ge`), plus `annex_hash`, `build_tapleaf_simplicity`,
`build_tapbranch`, the start-up invariant from `Genv.init_mem
jets_elements.prog` and executability on fresh frames for those 17 jets.
Finding: Elements' writable tag arrays (17 and 19 bytes) can alias a frame
record in the memory model, so `el_frame_record_sep` is an explicit caller
premise there (discharged for fresh and caller-owned blocks). Audit and
`coqchk` receipt at `d4214a5e` in the README.

## Actual environment builders — `bitcoin-env/README.md`, `elements-env/README.md`

The accepted hash-getter relations assume that the cached fields of the C
environment hold the canonical hashes. For the taproot half this is now
derived from the caller: `C/jets_bitcoin_env.v` (SHA unit + `bitcoin/env.c`)
and `eval_mallocTapEnv` / `mallocTapEnv_cached_hashes` show that the actual
`simplicity_bitcoin_mallocTapEnv` returns a block holding
`hash256_reg (tapleaf_hash_of e)`, `(words_hash_of 5 3 (tappath_of e))` and
`(tap_env_hash_of e)` (offsets 8, 40, 72) for a logical environment `e`
built from the raw data (`tapenv_describes_exists`). Kernel receipt in the
README.

**Update 2026-10-13 — the whole Bitcoin environment.** In the same derived
unit (now also containing `bitcoin/txEnv.c`), see `Coq/bitcoin-env/README.md`:

- `eval_mallocTransaction`, `eval_build_txEnv`, `eval_freeTransaction`,
  `eval_freeTapEnv`: the remaining real environment functions;
- `hash_buffer_bytestring`: the C streaming SHA-256 is `byteStringHash`;
- `build_environment` / `build_environment_readable`: the three builders in
  sequence on readable raw memory leave a `txEnv` that is `env_ready` for
  `project_raw_environment R`, and such an `R` always exists
  (`raw_environment_exists`);
- 50 theorems `ready_<jet>` plus `ready_tappath_nullable`: every environment
  relation that an accepted Bitcoin application-jet theorem takes as a
  premise holds for that `txEnv`. The relation premises are therefore facts
  the real caller establishes, with two documented exceptions that are
  input requirements or contract findings: the raw `txid` bytes
  (`ready_transaction_id`), and the accepted `tappath` relation for an empty
  path (resolved additively by `C/jet_bitcoin_tappath_nullable.v`);
- SHA start-up state: `env_unit_started` (holds in `Genv.init_mem` of the
  actual unit), `build_keeps_startup`, `free_keeps_startup` (kept by the
  real callers), `free_environment` (life cycle).

Elements: `el_ready_{script_cmr,internal_key,tapleaf_version,tappath}` for
the real `simplicity_elements_mallocTapEnv`, and
`elements_tappath_nullable_local_spec`. Open: the Elements transaction
builder (`elements/env.c`, 650 lines with null-data parsing and fee
sorting), `simplicity_elements_build_txEnv`, the `exec.c` drivers.

## Manifest for integration

`Coq/SHARED_MANIFEST.tsv` (generated by `python3 Coq/shared-manifest.py
write`, verified by `... check`) lists every Coq module added on this
branch since the fork point with its group, SHA-256, number of proved
results and the script that verifies the group. Nothing in the manifest is
registered coverage.

## Build notes

- `build-jets.sh` always builds `all`; the scripts here generate the makefile
  themselves to build selected targets.
- SHA chain: ~15 min to build at -j6 (`jet_sha_finalize_bridge.v` ≈ 7 min);
  coqchk of the SHA chain ≈ 20–60 min.
- Never copy onto a path that may be a symbolic link into `Coq/C` (see the
  incident note in `linked/RECEIPTS.md`).
