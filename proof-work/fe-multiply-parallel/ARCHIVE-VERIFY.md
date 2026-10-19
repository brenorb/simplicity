# Fresh isolated verification of the archived copy

Run on 2026-10-19 from a clean export of the integration branch: `feat/jet-equivalence`
`d7515911` plus this archive. Command:

```sh
JET_SRC_CACHE=~/.local/share/simplicity-coq-deps/src JOBS=6 \
  bash proof-work/fe-multiply-parallel/verify.sh OUT \
    C.jet_parallel_fe_mul_local C.jet_parallel_fe_sqr_local
```

| Step | Exit | Notes |
| --- | ---: | --- |
| guard | 0 | `C`, `Haskell`, `Coq/Simplicity` identical to `91d89bac` |
| deps | 0 | CompCert 3.14 / VST 2.14 rebuilt from tarballs `5588747d…` / `c11551c4…` (SHA-256) |
| materialize | 0 | 23 pinned negation sources and 13 archived modules, all hash-checked; none were already in the export |
| build | 0 | 197 modules compiled from scratch (4 min 38 s) |
| report | 0 | types and `Print Assumptions` for all 135 results |
| coqchk | 0 | recursive, `-o`, 1 min 13 s |

The kernel axiom set matches `Coq/C/jet_coqchk_axioms.expected` exactly. There is no
type-in-type, no unsafe (co)fixpoint and no assumed positivity. Both public endpoints
depend only on the six inherited assumptions listed in `README.md`.

This run covers the branch tip `ef4aa19c`. The tip differs from the branch's own
`evidence-41dac7e2` run only by the helper-lemma rename in
`jet_parallel_fe_mul_math.v` (`mod_mod_pow` → `fm_mod_mod_pow`). It was built against
the current main modules rather than the branch's starting point `de1623ea`.
Logs are not kept in the repository; rerun the command to reproduce them.
