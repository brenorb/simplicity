# Bitcoin fee model correction (2026-11-23)

Status: accepted on 2026-11-24 after fresh affected-closure validation and final
integrated acceptance. The authorized model correction was made on 2026-11-23.

The user authorized this focused model repair, superseding the former static
review restriction for M2. Starting checkout: `feat/jet-equivalence`,
`b2226a8b581a1ae01a9a1bc979ac12f6428abba8`; no tracked changes. Existing
untracked `.cursor/`, caches, `brag-output/` and `jet-proof-review.patch` are
preserved. The initial frozen-source gate passed on all 283 inputs.

## Exact change and domain

`Coq/Simplicity/Primitive/Bitcoin.v:54` changes only
`sigTxTotalOutValue - sigTxTotalInValue` to
`sigTxTotalInValue - sigTxTotalOutValue`. The reversed original comes from
upstream `6e0ddfbbbc55903833b7cdc30790b0a2269505fb` (2018-05-01).
The original file hash is
`f83df11d0834fc25109f6f2a26866645d1adc7ad3b148c832bdd746244d84165`.
The corrected local SHA-256 is
`450d8881d39a7e9a63407150b6c01dacd628400c77789beb55cc13fe617a3583`.
The current manifest records that hash; its checker and CI pins
are intentionally updated together. The other 282 content pins are unchanged.
Neither production C, canonical Haskell nor generated Clight is edited.

| Condition | Original | Corrected |
| --- | --- | --- |
| Fee | output total minus input total | input total minus output total |
| Fee range | 0 through MAX_MONEY | 0 through MAX_MONEY |
| Relation between totals | inputs <= outputs | outputs <= inputs |
| Positive ordinary fees | excluded | admitted |
| Zero fees | admitted | admitted |
| Per-item amounts / both totals | money range, signed int64 | unchanged |
| Input/output counts | both positive and below 2^32 | unchanged |
| Script length | below 2^32 | unchanged |
| Current input index | exists in input list | unchanged |

The fee upper bound follows from the retained total bounds and outputs <=
inputs. The lower bound expresses an ordinary non-creating transaction. This
is not an expansion to every raw Haskell/C constructor: negative fees, empty
outputs, out-of-money-range values and overflowing aggregates remain excluded.
This repair makes no claim about coinbase fee accounting. No dependency
requires widening those restrictions.

## Proof and representation chain

`jet_bitcoin_fee_domain.v` supplies:

- `bitcoin_fee_admissible` and `bitcoin_tx_from_lists`: construction from arbitrary
  nonempty bounded lists with the existing amount/script/aggregate bounds and
  outputs <= inputs. There is no equal-total premise.
- `fee_domain_tx` / `fee_domain_env`: parameterized one-input/one-output family;
  `positive_fee_totals` checks input total 10, output total 9, fee 1;
  `zero_fee_total` checks input total 10, output total 10, fee 0.
- `fee_domain_raw` and `fee_domain_raw_projection`: actual raw data and canonical
  computed txid/cache projection retaining the complete base environment,
  including current index and script CMR.
- `bitcoin_fee_rep_constructible`: a physical memory satisfying every field of
  the registered fee representation, with exact input/output totals and valid
  footprint blocks, for every corrected logical environment.
- `bitcoin_fee_rep_stable`: that relation survives fresh-frame allocation.
- `bitcoin_fee_every_environment_checked`: instantiates the existing actual-C
  `bitcoin_fee_local_spec`, retaining the call-memory relation, encoded Unit
  input, source-frame fields, writable destination, footprint separation,
  successful C return, exact Word64 output, prefix preservation, final cursor
  and full load-framing conclusion. `bitcoin_fee_word_exact` connects the
  decoded word to the unbounded integer input-minus-output without wrap.
- `positive_fee_checked` / `zero_fee_checked`: full instances of that same
  execution contract, not weak existential execution summaries.

The existing fee, totals, getters, raw/extended projections and transaction-hash
statements and proof bodies remain unchanged. Resource-budget directives needed
for fresh builds are listed below. They compute inputs minus
outputs or read/project transaction data without using the reversed sign.
The new construction uses exact totals, matching the current representation;
no modular-cache relaxation or assumed execution premise is introduced.

## Complete inventory and archived boundaries

[JET_BITCOIN_FEE_AFFECTED.tsv](JET_BITCOIN_FEE_AFFECTED.tsv) lists all 194 active
modules transitively importing `Simplicity.Primitive.Bitcoin` (including the new
module), each affected import edge, all 1,369 source proof declarations and all 1,130
registered declarations, plus 6 proof-bearing helper definitions.
This includes base environments, count/current/indexed readers, fee/totals,
raw/extended primitives, transaction and composed hashes, shared SHA helpers,
Elements consumers, secp consumers and the executable registry. It is a reverse
import inventory, independently matched against Coq's generated dependency graph,
not a search only for the fee identifier. No additional active `.v` sources exist
outside the C/Simplicity trees in `Coq` and `proof-work`. Its forward build
prerequisites are reproducible with the existing `jet-closure.py` over the C
module column. Some named modules aggregate otherwise unrelated proof families;
those prerequisites remain in the build scope.

[JET_BITCOIN_FEE_ARCHIVED.tsv](JET_BITCOIN_FEE_ARCHIVED.tsv) inventories 60
archived candidates linked by explicit imports to this closure. These are
preserved historical candidates, not normal build or acceptance entries.
In particular:

- `original-target-boundary/OriginalDomainBoundary.v.source` uses the separate
  historical `OriginalBitcoin` namespace. Its positive-fee exclusion concerns
  the original revision only; its README's old current-source assertion is
  superseded by this report. It must not be transported to corrected `Bitcoin`.
- Four `unbuilt-support/jet_bitcoin_env_constructible*.v.source` candidates
  already fail after the 2026-10-19 rollback (modular vs exact totals). They are
  not evidence of constructibility. The new active exact-total constructor
  discharges fee nonvacuity without importing them.
- `review-witnesses` contains old high-bit/empty-output examples, already outside
  the retained amount/count domain. The fee correction does not admit them.
- `derived-trees` is alternate translation-unit/namespace work, not additional
  current registered C-call coverage.

The new contract snapshot freezes all twelve theorem types and three semantic
definitions: the arbitrary-list constructor, raw-data constructor and complete
execution-witness predicate. The full-base raw projection retains current index
and script CMR. The execution predicate exposes all C-call preconditions and
postconditions; its closed amount examples and universal execution theorem also
check the helper constructions. Comparison-only contract and assumption checks
pass for this module.

No existing registry entries are removed. The new results and contract
predicates are added to both normal build projects and the existing per-module
contract/assumption audit registries.

## Assumptions before and after

| Result | Before | After |
| --- | --- | --- |
| `bitcoin_fee_spec_value` | functional extensionality | unchanged; records match |
| `bitcoin_fee_local_spec` | six inherited axioms below | unchanged; records match |
| Existing public types and explicit premises | original `sigTx` environment domain | text unchanged; Bitcoin environments use the corrected record; full contracts match |
| New admissibility, exact fee, positive/zero totals and raw projection | absent | closed |
| New fee-program-to-record equality | absent | functional extensionality |
| New physical construction / stability | absent | four inherited logical axioms (the six below excluding the two event interpretations) |
| New full execution witnesses | absent | same six inherited fee-local axioms |

[The complete before/after table](JET_BITCOIN_FEE_ASSUMPTIONS.md) lists all
1,130 registered affected theorems: 1,118 existing assumption sets are unchanged,
and twelve results are new. These are global axioms reported by `Print
Assumptions`. Explicit theorem hypotheses, including conditional external-library
models, remain visible and unchanged in the checked contract snapshots.

The six existing fee-local assumptions are
`Classical_Prop.classic`,
`FunctionalExtensionality.functional_extensionality_dep`,
`ClassicalDedekindReals.sig_forall_dec`,
`ClassicalDedekindReals.sig_not_dec`,
`Events.external_functions_sem`, and `Events.inline_assembly_sem`.
There are no added axioms, admitted proofs, external-library models or assumed
fee/output/execution conclusions. Existing conditional models in other families
retain their named theorem premises and are not discharged by this repair.

## Validation and reproducibility

All required checks passed on the corrected sources. The full audit and final
integrated acceptance each retained an unchanged input fingerprint. Historical runs
are not used to validate the correction. Inventory serialization was normalized, and four primed
declaration names were transcribed in full. Module/import entries, selected
dependencies and all Coq, C, Haskell, registry, manifest and snapshot bytes are
unchanged. Final integrated acceptance was repeated after these documentation
corrections.

| Check | Coverage | Result |
| --- | --- | --- |
| Fresh dependency build | 2,113 C modules plus canonical Bitcoin; all selected objects newer than their sources | Exit 0; artifact-free project build with the compatible pinned toolchain |
| Full kernel check | All selected modules and recursively loaded dependencies | Exit 0; exactly the fifteen existing library axioms; no type-in-type, unsafe fixpoints or assumed positivity |
| Assumption comparisons | 1,948 modules with registered theorems | Exit 0; all records match, including unchanged existing fee/totals assumptions |
| Contract comparisons | 1,984 modules with registered theorems or definitions | Exit 0; all records match; only the two authorized canonical fee-expression changes and the new module's records differ from the starting snapshots |
| General and concrete nonvacuity | All twelve new results; arbitrary valid lists; full 10/9/1 and 10/10/0 C-call witnesses; full-base raw/extended projection | Compiled and kernel-checked; complete encoding, call-memory relation, success, exact non-modular result and framing retained |
| Frozen-source guard and mutation tests | 283 inputs; other 282 content pins unchanged | Pass; drift, additions, deletions and symlinks still rejected |
| Primitive identity | Eight extended constructors and base-name comparison | Pass with the retained documented `LockTime` mismatch printed |
| Final integrated fee acceptance | 86 kernel modules, 26 assumption modules and 41 contract modules; global source/registry/mutation checks, negative fixtures and five AST regenerations | Exit 0 on stable sources; all five ASTs match; no update/no-build flags |

No active affected proof remains unvalidated. Existing conditional results retain
their stated premises. The new construction establishes the complete physical
precondition of the fee theorem; it is not an execution proof of the production
environment builder. The retained raw-domain restrictions and unrelated
mismatches are unchanged. Archived candidates are inventoried historical work,
not newly accepted implementation proofs.

Use the repository-pinned Coq 8.17.1, CompCert 3.14, VST 2.14 and pinned
CoqPrime/safegcd dependencies. The compatible local compiler is
`/nix/store/57myhb98wx8k9dr21cf51bsmvxjs67h6-coq-8.17.1/bin/coqc`, built with
OCaml 4.14.4, matching the prepared libraries. The system Rocq 9.3 and the
8.17.1/OCaml 4.14.1 installation cannot consume those objects. Dependency archive
checksums match `jet-deps.sh`; CompCert reports 3.14, x86/model64, Linux, standard
ABI and little endian.

Fresh builds use an external artifact-free tree made from `git archive` of the
starting revision, overlaid with the repair's current files. All local objects
from the incompatible compiler attempt were deleted before the compatible
build. No pre-existing project `.vo` is used as validation. Temporary logs,
compiled artifacts and process records stay outside the repository.

### Pre-existing resource ceilings exposed by the fresh build

The following proofs exceeded their existing limits. Statements, complete proof
operations, coefficients, assumptions and semantic conclusions are preserved.
The short proofs receive a local 30-second default with the former 10/15-second
default restored afterward. The two larger certificates use the existing
budgets of comparable adjacent certificates, also restored afterward.

| Module / theorem | Original limit | Measured expensive command(s), seconds | Current result |
| --- | ---: | --- | --- |
| `jet_secp_field_prime.secp256k1_field_prime` | 10 | VM 14.639 | Actual module rebuild and unchanged records pass |
| `jet_secp_taptweak_entry.taptweak_free` | 10 | Disjointness 18.773 | Actual module rebuild and unchanged records pass |
| `jet_secp_modinv_de_exec.de62_run_ok_true` | 10 | VM 11.693 | Actual module rebuild and unchanged records pass |
| `jet_nonce_exec_payload.nonce_payload_exec` | 10 | Context disjointness 11.295 | Actual module rebuild and unchanged records pass |
| `jet_secp_add_literal_step.literal_gej_add_finite_step` | 10 | Statement elaboration 11.506 | Actual module rebuild and unchanged records pass |
| `jet_bitcoin_tap_hash_literal.literal_bitcoin_tap_env_hash_parametric` | 10 | Rewrite/application/closing 11.742/11.563/12.633 | Actual module rebuild and unchanged records pass |
| `jet_elements_make_tapbranch_exec.el_eval_make_tapbranch` | 10 | Disjointness 13.497 | Actual module rebuild and unchanged records pass |
| `jet_elements_single_issuance_jet.elements_single_issuance_hash_program_local_spec` | 15 | Dispatch/finalization 16.905 | Actual module rebuild and unchanged records pass |
| `jet_secp_modinv_de_recurrence.de62_recurrence_matches` | 10 | Closing 16.070 | Actual module rebuild and unchanged records pass |
| `jet_secp_mixed_ratio_function.eval_mixed_equal_ratio_function` | 10 | Disjointness 10.726/12.260 | Actual module rebuild and unchanged records pass |
| `jet_secp_table_step9.table_step9_coefficients` | 60 | VM 86.075, closing 86.092 | Actual module passes with 240-second ceiling; records unchanged |
| `jet_secp_table_step13.table_step13_coefficients` | 360 | VM 377.568, closing 321.920 | Actual module passes with 1,200-second ceiling; records unchanged |
| `jet_secp_modinv_var_fg.inv_fg_next_value` | 10 | Finite cases 11.285, closing 9.154 | Actual module rebuild and unchanged records pass |
| `jet_secp_scalar_de_recurrence.scalar_de62_recurrence_matches` | 10 (inner command 30) | Reflected comparison 16.877 | Actual module rebuild and unchanged records pass |
| `jet_secp_globalz_pass2.globalz_word_walk_pass2` | 10 | Literal rewrite 13.691, closing 9.901 | Actual module rebuild and unchanged records pass |
| `jet_secp_hashgen_function.eval_hashgen_internal` | 10 | Block disjointness 13.234 | Actual module rebuild and unchanged records pass |
| `jet_secp_strauss_first_loop.exec_strauss_preprocess_finite` | 10 | Temporary-environment bookkeeping 10.380 | Actual module rebuild and unchanged records pass |
| `jet_secp_strauss_general_loop.exec_strauss_general_loop` | 10 | Temporary-environment bookkeeping 13.800 | Actual module rebuild and unchanged records pass |
| `jet_secp_taptweak_body.exec_taptweak_body` | 10 (closing already 60) | Field-frame bookkeeping 11.278; closing 11.953 | Actual module rebuild and unchanged records pass; existing closing ceiling preserved |
| `jet_elements_taptweak_point_prepare.exec_elements_taptweak_strauss_preprocess_finite` | 10 | Temporary-environment bookkeeping 10.747 | Actual module rebuild and unchanged records pass |
| `jet_secp_taptweak_function.eval_generic_taptweak` | 10 (closing already 60) | Separation bookkeeping 12.480 | Actual module rebuild and unchanged records pass; existing closing ceiling preserved |
| `jet_elements_taptweak_body.exec_elements_taptweak_body` | 10 | Parallel field-frame timeout; isolated field step 9.186, closing 14.450 | Actual module rebuild and unchanged records pass |
| `jet_elements_taptweak_function.eval_elements_taptweak_generic` | 10 | Separation bookkeeping 10.300, closing 9.287 | Actual module rebuild and unchanged records pass |

Bounded isolated diagnostics identified the expensive steps using the same
statements and proof operations. All twenty-three adjusted actual modules rebuild
and retain their existing contract and assumption records. Read-only token
comparison also confirms that all existing statements and proof operations are
unchanged after removing comments and timeout directives. Raising an inner
command timeout did not resolve the two Elements failures; adjusting only the
enclosing theorem's
default did. Three other parallel-build timeouts (`jet_secp_point_square_z`,
`jet_secp_curve_square`, `jet_secp_rescale_prefix`) passed isolated rebuilds of
their unchanged sources, so those files have no edits. The completed build used
two jobs to reduce contention. These are prerequisite resource issues, not fee
arithmetic counterexamples or changes to the reported mixed-ratio discrepancy.

### Reproduction

Run in Bash from an artifact-free checkout with the compatible compiler on
PATH. These commands use the existing build, closure and audit tools:

```bash
set -euo pipefail
export JOBS=4
fee_work=$(mktemp -d)
fee_scope="$fee_work/scope.txt"
fee_inputs_before=$(python3 Coq/jet-audit-inputs.py)
fee_roots=$(awk -F '\t' 'NR > 1 && $1 ~ /^C[.]/ {print $1}' Coq/C/JET_BITCOIN_FEE_AFFECTED.tsv)
python3 Coq/jet-closure.py $fee_roots > "$fee_scope"
printf '%s\n' Simplicity.Primitive.Bitcoin >> "$fee_scope"
export JET_ONLY_MODULES="$fee_scope"
export JET_TARGETS=$(printf '%s\n' $fee_roots | sed 's|\.|/|g; s|$|.vo|' | tr '\n' ' ')
bash Coq/build-jets.sh -j2
ulimit -S -s 65520
fee_kernel_modules=$(awk '/^C[.]/ {print}' "$fee_scope" | tr '\n' ' ')
bash Coq/build-jets.sh --coqchk -bytecode-compiler yes -silent -o $fee_kernel_modules > "$fee_work/kernel.log" 2>&1
awk '/^\* Axioms:/{f=1;next} f&&NF==0{exit} f{print $1}' "$fee_work/kernel.log" | sort > "$fee_work/axioms.txt"
diff -u Coq/C/jet_coqchk_axioms.expected "$fee_work/axioms.txt"
grep -q 'Constants/Inductives relying on type-in-type: <none>' "$fee_work/kernel.log"
grep -q 'unsafe (co)fixpoints: <none>' "$fee_work/kernel.log"
grep -q 'positivity is assumed: <none>' "$fee_work/kernel.log"
bash Coq/audit-jet-assumptions.sh
bash Coq/audit-jet-contracts.sh
[[ "$fee_inputs_before" == "$(python3 Coq/jet-audit-inputs.py)" ]]
bash Coq/check-jets.sh --accept --jets=simplicity_bitcoin_fee
```

The explicit broader build/kernel/snapshot commands cover the complete inventory
beyond the fee jet's own smaller closure. The scoped integrated command also
runs global source-correspondence/registry/mutation checks, negative fixtures
and all five AST regeneration comparisons. Library axioms and kernel safety
are compared with the existing baseline, as in `check-jets.sh`; snapshot
generation is never acceptance. The explicit full checks cover the new module
even though it is a consumer of the fee theorem and is outside the smaller
fee-jet-only dependency closure.

The saved static specification audit at
`/Users/brenorb/code/codex/2026-11-18/is-this-an-autoresearch-project/outputs/specification-audit-report.md`
was consulted. It reviews the starting revision and separates the fee-domain
omission from unrelated findings. Its historical runs certify only their
recorded sources; none validates this repair. Its N11 warning about weak
execution summaries motivates the complete witness above. This task makes no
claim of rebuilding every unrelated Coq module or accepting archived candidates.
