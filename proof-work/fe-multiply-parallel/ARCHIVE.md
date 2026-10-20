# Archived alternative: parallel `fe_multiply` / `fe_square` proofs

Status: **archived, not registered.** Nothing here is in `_CoqProject`,
`_CoqProject.jets`, `jet_coverage.tsv` or any snapshot. The `.v.source`
extension keeps these modules out of every build and coverage scan.

Archived on 2026-10-19 while integrating side branches into
`feat/jet-equivalence`. Sources:

| Origin | Commit | What |
| --- | --- | --- |
| `codex/fe-multiply-parallel` | `ef4aa19c` | the 13 `Coq/C/jet_parallel_fe_*.v` modules (now `modules/*.v.source`), `README.md`, `RESERVATION.md`, pinned negation dependency, `tools/`, `verify.sh` |
| `codex/fe-multiply-integration` | `a8bfb8b1` | `CANONICAL-REVIEW.md`, `ACCEPTANCE-STATUS.md`, `HANDOFF.md`, `BITCOIN-BLOCKER-PROPOSAL.md`, `scoped-acceptance.sh`, the `Coq/mul-review` gate (now `mul-review/*.py.source`) and the registration commit `dd4579a7` (now `unapplied-registration.patch`) |

Both branches remain in the local repository; this directory makes the work
available on the main branch without them.

## Why this is the archived copy

The parallel proofs and the main proofs have **the same public statements**:

| Jet | Registered proof | This archived proof |
| --- | --- | --- |
| `simplicity_fe_multiply` | `C.jet_secp_multiply_literal_jet.fe_multiply_literal_local_spec` (`proof-work/secp-field-literal` origin) | `C.jet_parallel_fe_mul_local.fe_multiply_literal_local_spec` |
| `simplicity_fe_square` | `C.jet_secp_square_local.fe_square_local_spec` (`proof-work/secp-square-*`) | `C.jet_parallel_fe_sqr_local.fe_square_literal_local_spec` |

Each states `secp_jet_local_spec f_simplicity_fe_… … (@literal_fe_… Alg.CoreFunSem)`
over the same `literal_fe_multiply` (`jet_secp_negate_literal_contract.v`,
byte-identical on both sides) and the same `literal_fe_square :=
iden &&& iden >>> literal_fe_multiply`. Both have unrestricted inputs, the original
unchanged C, no `memcpy_model` premise, and the same six inherited
assumptions. Neither is logically stronger.

The main proofs are selected for integration and this one is retained as the
checked alternative because:

1. **Equal logical scope.** Both alternatives prove the complete original-C
   local contracts over arbitrary inputs, with the same inherited assumptions.
   Neither is selected by weakening its statement or adding premises. The
   earlier user preference is also recorded in [HANDOFF.md](HANDOFF.md).
2. **More source-correspondence evidence.** The main multiply packet reruns the
   recursive-port, literal-add, foundation, normalization and wiring gates
   (173 rejected mutations). `mul-review` here rejects 41.
3. **Downstream work builds on the main proofs.** That includes the
   separate-output square (`proof-work/secp-square-separate`) and the beta
   multiply (`proof-work/secp-beta-*`). Switching would mean re-basing that work.

The choice favors source-correspondence coverage and downstream reuse; it is
not a claim that the alternative is logically weaker. The parallel execution
model is faster and remains available for comparison and reuse. Final coverage
comes only from the selected endpoint after the standard acceptance command.

Reasons to keep this copy:

- It is plain `C.`-namespace modules with one `verify.sh`. That script rebuilds from a
  clean export with fresh CompCert/VST and runs a recursive `coqchk`. It needs no
  private namespaces and no `/private/tmp` candidate trees.
- `jet_parallel_fe_mul_oracle.v` / `_shift.v` hold proved fresh-word oracles for
  the original `u128_mul`, `u128_accum_mul`, `u128_accum_u64` and
  `u128_rshift` (52, 64). `jet_parallel_fe_mul_math.v` (`fe_mul_core`) holds a closed integer
  dataflow theorem. Both can be reused for other secp jets that use the u128
  helpers. A whole `fe_mul`/`fe_sqr` symbolic run takes under one second.

## Layout

- `modules/`: the 13 proof modules, plus `modules-manifest.json` (SHA-256,
  materialized name, build order, 135 named results).
- `negate-dependency/`: the 23 pinned field-negation sources these modules import.
  They are byte-identical to `proof-work/secp-field-literal/inherited/` and to the
  candidate that is uncommitted in the main checkout.
- Run logs are not kept in the repository. The branch's original evidence folders
  (`evidence-mul-62c0abee/`, `evidence-41dac7e2/`) remain on `codex/fe-multiply-parallel`.
  [ARCHIVE-VERIFY.md](ARCHIVE-VERIFY.md) summarizes the fresh run made after archiving.
- `mul-review/`: the archived source gate (`check-mul-wiring.py`) and its
  mutation tests. They target these modules and are not wired into `check-jets.sh`.
- `unapplied-registration.patch`: **do not apply** while the main proofs are
  registered. It would register a duplicate.
- `scoped-acceptance.sh`, `ACCEPTANCE-STATUS.md`: historical records of the
  registration attempt. `BITCOIN-BLOCKER-PROPOSAL.md` still describes open
  repository-wide acceptance blockers (Bitcoin value domain, LockTime identity).

## Checking and rebuilding

```sh
python3 -I proof-work/fe-multiply-parallel/check.py
python3 -I proof-work/fe-multiply-parallel/check.py --extract /tmp/fe-mul-parallel
JET_SRC_CACHE=~/.local/share/simplicity-coq-deps/src \
  bash proof-work/fe-multiply-parallel/verify.sh /tmp/fe-mul-verify \
    C.jet_parallel_fe_mul_local C.jet_parallel_fe_sqr_local
```

`verify.sh` exports the committed `HEAD` and checks the original-target guard.
It materializes the pinned negation sources and `modules/` after checking their
hashes. If the main branch already holds one of these files, the existing copy
must be byte-identical. The script then builds the closure, prints the types and
assumptions, and runs a recursive `coqchk`.

## Verification after archiving

See [ARCHIVE-VERIFY.md](ARCHIVE-VERIFY.md).
