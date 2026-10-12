# Receipts — memcpy-linked proofs

Environment: Coq 8.17.1 (opam switch `simplicity`), CompCert 3.14, VST 2.14
(`JET_DEPS=~/.local/share/simplicity-coq-deps`), macOS arm64 host, stack
65520 KiB. Fork point `a8685146`.

## 2026-10-11 — `bash Coq/audit-linked.sh` (JOBS=-j6), exit 0

Sources: commit `94c373f5` (generators, model, call-site rules and the 124
`_linked` theorems are unchanged since `e69311e5`/`abb21d8c`).

| input | SHA-256 |
| --- | --- |
| `Coq/C/jets.v` (accepted, unchanged) | `093bf037b96c2a16f2eafb8401301a469e7c9f4c50ea9a8492f1c163d2a4cd88` |
| `Coq/C/jets_sha.v` (accepted, unchanged) | `44b138300b7429d0a18e8035361aba028965e277e52538fb032a01dbf1db1913` |
| `Coq/C/memcpy_exact.v` (clightgen of `jet_memcpy_exact.c`; regeneration byte-identical) | `756b76144356747ff0a9cefed711428ea81f532f63d7749ad7760e07eded4f7a` |
| derived `linked/tree/C/jets.v` | `09e1371c8ebf77b9b3f71db1e0a9da7341093a557bef0b9dc9405478e52a4960` |
| derived `linked/tree/C/jets_sha.v` | `2f99fa090b922a478bc9086cba40fd464d6e1c81961043cd29f21d7c385830d7` |

Steps and results:

1. Generated theorem modules byte-identical to the committed ones
   (`gen-linked-theorems.py`, `gen-linked-sha-theorems.py`).
2. No `admit`/`Admitted`/`Axiom`/`Parameter`/`Conjecture` in `linked/C/*.v`,
   `C/jet_memcpy_exact.v`, `C/jet_memcpy_impl.v`.
3. Derived tree built from scratch earlier the same day (core part: 116
   modules in 244 s at -j7; SHA part afterwards); all targets up to date.
4. `Print Assumptions` for 127 theorems:
   - 124 `_linked` jet contracts and `memcpy_model_holds`: exactly
     `ClassicalDedekindReals.sig_forall_dec`, `ClassicalDedekindReals.sig_not_dec`,
     `Classical_Prop.classic`, `Events.external_functions_sem`,
     `Events.inline_assembly_sem`,
     `FunctionalExtensionality.functional_extensionality_dep` — the six
     assumptions of the accepted conditional theorems, and no `memcpy_model`.
   - `linked_ast_is_compcert_link`: closed under the global context.
   - `linked_program_is_compcert_link`: `compcert.lib.Axioms.proof_irr` only
     (inherent in CompCert's `link_program`).
5. `coqchk -silent -o` on the 14 linked modules (`C.jet_memcpy_model`,
   `C.jet_linked_program`, `C.jet_linked_memcpy_jets`, eleven `*_linked`) and
   their whole dependency chains: passed. Context summary: no type-in-type,
   no unsafe fixpoints, no assumed positivity.

Counts: 104 core contracts (36 leftmost/rightmost, 32 pad, 36 full shift)
and 20 SHA-unit contracts (10 `ctx_8_add_n`, `add_buffer_511`, `finalize`,
`tapdata_init`, 7 Bitcoin hash/taproot jets).

## 2026-10-11 (second pass) — `bash Coq/audit-linked.sh` (JOBS=-j4), exit 0 (21 min)

Sources at commit `38501bec`; adds `jet_linked_sha_program.v` (the SHA-unit
program is CompCert's link of the accepted SHA unit with the memcpy unit).

- Generated modules fresh; no forbidden declarations.
- `Print Assumptions` for 129 theorems: the 124 `_linked` contracts and
  `memcpy_model_holds` as above; `linked_ast_is_compcert_link` closed for
  both programs; `linked_program_is_compcert_link` depends only on
  `Axioms.proof_irr` for both programs.
- `coqchk -silent -o` on the 15 linked modules and their dependency chains:
  passed.
- `jet_linked_program.v` `5b0ebfa15adb14c846dc010b3e040545c4b75e5d77716d4c9fbd128f1c5e7b66`,
  `jet_linked_sha_program.v` `67175bcbb458752255ee31947b16b373f05e71d389639f4e346f06eb50fdc344`,
  `jet_memcpy_model.v` `57044542a6645c0d896ccdcfffb2bd351df562dd11dd405ddbcc14039d78b3df`.

## 2026-10-11 — `bash Coq/build-linked-startup.sh --check`, exit 0 (18 min)

Sources at commit `38501bec`. Startup modules compiled against the linked SHA
program; generated `linked/startup/jet_sha_startup_linked.v` fresh;
`Print Assumptions` for the 40 `_linked` startup theorems (20 contracts over
the invariant, 3 caller-side environment contracts, 17 executability
results) and `sha_startup_state_initialized`: within the eight inherited
assumptions, no `memcpy_model`; `coqchk -silent -o
JetStartup.jet_sha_startup_linked` with its whole dependency chain: passed.

## Standalone memcpy proofs (normal tree)

- `C.jet_memcpy_impl`: compiled; `Print Assumptions eval_memcpy_impl` = the
  six assumptions above; `coqchk -silent -o C.jet_memcpy_impl` exit 0
  (commit `106be1e9`).
- `C.jet_memcpy_exact`: compiled; `Print Assumptions eval_memcpy_exact` = the
  same six; `coqchk -silent -o C.jet_memcpy_exact` exit 0 (commit `f4d383d5`).

## Incident note

An earlier revision of `build-linked.sh` copied derived files through stale
symbolic links and overwrote three accepted sources *in this worktree only*
(`jets_sha.v`, `jet_sha_uchars_prep.v`, `jet_sha_uchars_loop.v`). They were
restored with `git checkout` (hash of `jets_sha.v` re-verified against
`HEAD`), the script now removes the destination before copying, and every
result above was produced after the fix. The main checkout was never
touched.
