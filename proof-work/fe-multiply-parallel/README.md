# Parallel proof: `simplicity_fe_multiply` and `simplicity_fe_square`

> **Archived alternative (2026-10-19).** See [ARCHIVE.md](ARCHIVE.md). The modules
> named below as `Coq/C/jet_parallel_fe_*.v` are now `modules/*.v.source`. The
> integration instructions at the end are superseded: the registered proofs for
> these jets are the main ones.

Branch `codex/fe-multiply-parallel`, started from `de1623ea` (`feat/jet-equivalence`).
See [RESERVATION.md](RESERVATION.md) for the coordination check. Nothing here is
registered; integration belongs to the main agent (instructions below).

## Results

Both are the repository's standard `secp_jet_local_spec`
(`C.jet_secp_normalize_local`). They state, for arbitrary input values, the
actual function entry, local allocations, source-frame copy, original readers,
in-place helper call, original wide writer, return value `1`, freeing of all
locals, the encoded output cells, write-prefix preservation, the destination
cursor update, and unchanged loads outside the frames.

| Jet | Theorem | Canonical program |
| --- | --- | --- |
| `simplicity_fe_multiply` | `C.jet_parallel_fe_mul_local.fe_multiply_literal_local_spec` | `literal_fe_multiply` = `multiply_word_spec 8 >>> literal_fe_normalize512` (negate candidate's literal port of `fe_multiply = mul256 >>> fe_normalize512`) |
| `simplicity_fe_multiply` | `C.jet_parallel_fe_mul_local.fe_multiply_local_spec` | `canonical_fe_multiply` (via `literal_fe_multiply_matches`) |
| `simplicity_fe_square` | `C.jet_parallel_fe_sqr_local.fe_square_literal_local_spec` | `literal_fe_square` = `iden &&& iden >>> literal_fe_multiply` (new literal port of `fe_square = iden &&& iden >>> fe_multiply`; `literal_fe_square_parametric` proved) |

Input type `Prod (Word 8) (Word 8)` / `Word 8`, output `Word 8` (`Word 8` is
256 bits). Assumptions of all three: `Classical_Prop.classic`,
`FunctionalExtensionality.functional_extensionality_dep`,
`ClassicalDedekindReals.sig_not_dec`, `ClassicalDedekindReals.sig_forall_dec`,
`Events.external_functions_sem`, `Events.inline_assembly_sem` — all on the
inherited allowlist of `Coq/audit-jet-assumptions.sh`. No external-library
premise (`memcpy_model` etc.) occurs: every function reached is internal to
the secp translation unit. No admits, axioms, unsafe flags or skipped
obligations; the original-target guard (`git diff 91d89bac -- C Haskell
Coq/Simplicity`, excluding `C/test.c`) is clean.

## How the proof works

* `jet_parallel_fe_mul_math` — `fe_mul_core`: the 42-step 128-bit dataflow of
  the original `secp256k1_fe_mul_inner`, with every accumulator bound derived
  from normalized limbs (no intermediate bound assumed) and the exact identity
  `fe_val r + K·p = Σ P_k·2^{52k}` with an explicit `K`.
* `jet_parallel_fe_mul_sx`, `_oracle`, `_shift` — proved oracles for the
  original `u128_mul`, `u128_accum_mul`, `u128_accum_u64` (executed through
  their bodies by the pure executor, results checked against canonical terms)
  and `u128_rshift` at counts 52 and 64 (actual statements). Each names its two
  result words by fresh variables whose meaning is the 128-bit update;
  `oracle_ok` is proved over the real Clight calls.
* `_run` / `_sqr_run` — the whole original `secp256k1_fe_mul(&a,&a,&b)` /
  `secp256k1_fe_sqr(&a,&a)` runs symbolically (single result, 42 / 32 events,
  aliasing `r = a` handled by the actual statement order).
* `_model` / `_sqr_model` — generated (tools/gen_fe_mul_model.py) integer models;
  the valuation is proved to solve every event (`fm_solves`, `fs_solves`) and
  the outputs are bounded and equal the product mod p (`fm_mul_values`,
  `fs_sqr_values`; squaring reuses `fe_mul_core` with b = a, splitting each
  doubled product).
* `_field`, `_calls`, `_local`, `_sqr_field`, `_sqr_local` — composition with the
  original readers (field-add chain), the original wide writer (negate
  candidate), entry/allocation/copy/free and the public contract.

## Dependencies outside this branch

* The unaccepted field-negation candidate (23 modules) of the main checkout,
  pinned byte-for-byte in [negate-dependency/](negate-dependency/) with its
  manifest. Used: `jet_secp_write_fe_wide_exec`/`_values`,
  `jet_secp_negate_writer_bridge`, `jet_secp_negate_literal_contract`
  (`literal_fe_multiply`, `literal_fe_normalize512`), `jet_secp_canonical_negate`
  (`canonical_fe_multiply`, `canonical_fe_normalize512_numeric`) and their
  closure (literal division ports).
* Committed field-add modules not listed in `_CoqProject` at `de1623ea`
  (`jet_secp_add_two_reads`, `_add_prepare`, `_add_entry`, `_add_body`,
  `_add_pair_input`, `jet_secp_field_add_initial`, `jet_secp_read_fe_*`,
  `jet_secp_field_read_preservation`); their closure is built by `verify.sh`.

## Evidence

`bash proof-work/fe-multiply-parallel/verify.sh OUT [targets]` exports the
committed HEAD into a clean tree, rebuilds the pinned CompCert/VST from their
checksummed tarballs, materializes the pinned negate sources after checking
their hashes, builds the target closure from scratch, prints theorem types and
assumptions, and runs recursive `coqchk`. Recorded runs:

* `evidence-mul-62c0abee/`: `simplicity_fe_multiply`.
* `evidence-41dac7e2/`: both jets.

(Not kept in the archive; they remain on `codex/fe-multiply-parallel`. See `ARCHIVE-VERIFY.md`.)

In each, `STATUS` lists the exit status of every step, `coqchk.log` the
kernel summary (axioms equal `Coq/C/jet_coqchk_axioms.expected`; no
type-in-type, unsafe fixpoints or assumed positivity), `report.log` the full
`About`/`Print Assumptions` output, `sources.sha256` / `objects.sha256` the
hashes of the checked sources and objects.

## Remaining obligations (not done here, by instruction)

* Integration of the field-negation candidate and of the field-add support
  modules into the project files.
* Registration: project inventories, `_CoqProject`/`_CoqProject.jets`,
  `jet_coverage.tsv`, public-theorem list, contract and assumption snapshots,
  acceptance (`check-jets.sh --update-expected`, review, `--accept`).
* Canonical-fidelity review of `literal_fe_square` (new literal port) alongside
  the negate candidate's `literal_fe_multiply`.

## Integration instructions

1. Integrate the field-negation candidate; its files must match
   `negate-dependency/fe-negate-manifest.json` (then this branch's modules
   compile unchanged).
2. Merge this branch; it adds only `Coq/C/jet_parallel_fe_*.v` and this directory.
3. Add to `Coq/_CoqProject` and `Coq/_CoqProject.jets`, in order:
   `jet_parallel_fe_mul_sx`, `_math`, `_oracle`, `_shift`, `_model`, `_run`,
   `_field`, `_calls`, `_local`, `jet_parallel_fe_sqr_model`, `_sqr_run`,
   `_sqr_field`, `_sqr_local` (plus any missing field-add support modules).
4. Register `simplicity_fe_multiply → C.jet_parallel_fe_mul_local
   fe_multiply_literal_local_spec` and `simplicity_fe_square →
   C.jet_parallel_fe_sqr_local fe_square_literal_local_spec`, regenerate and
   review the snapshots, then run full acceptance.
