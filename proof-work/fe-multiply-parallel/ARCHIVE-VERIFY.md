# Fresh isolated verification of the archived copy

Run on 2026-10-19 against commit `9d930cf1`, the first commit containing this
archive on `integrate/jet-equivalence` (branched from `feat/jet-equivalence`
`d7515911`). Command:

```sh
JET_SRC_CACHE=~/.local/share/simplicity-coq-deps/src JOBS=6 \
  bash proof-work/fe-multiply-parallel/verify.sh OUT \
    C.jet_parallel_fe_mul_local C.jet_parallel_fe_sqr_local
```

Evidence: [`evidence-archive-9d930cf1/`](evidence-archive-9d930cf1/).

| Step | Exit | Notes |
| --- | ---: | --- |
| guard | 0 | `C`, `Haskell`, `Coq/Simplicity` identical to `91d89bac` |
| deps | 0 | CompCert 3.14 / VST 2.14 rebuilt from the same checksummed tarballs as the earlier runs |
| materialize | 0 | 23 pinned negation sources and 13 archived modules, all hash-checked; none were already in the export |
| build | 0 | 197 modules compiled from scratch (4 min 38 s) |
| report | 0 | types and `Print Assumptions` for all 135 results |
| coqchk | 0 | recursive, `-o`, 1 min 13 s |

The kernel axiom set matches `Coq/C/jet_coqchk_axioms.expected` exactly, with no
type-in-type, unsafe (co)fixpoints or assumed positivity. Both public endpoints
depend only on the six inherited assumptions listed in `README.md`.

This run differs from `evidence-41dac7e2` in one proof source:
`jet_parallel_fe_mul_math.v` carries the later helper-lemma rename
(`mod_mod_pow` → `fm_mod_mod_pow`, `ef4aa19c`). So this is the first recorded
fresh check of the branch tip, and it is built against the current main
modules rather than the branch's starting point `de1623ea`.
