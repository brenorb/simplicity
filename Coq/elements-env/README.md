# The Elements environment builders (`C/elements/env.c`)

Counterpart of `Coq/bitcoin-env` for Elements. Unregistered; accepted sources
are only read.

## Program

`C/jets_elements_env.v` is clightgen's output
(`C/regenerate-elements-env.sh`) for `C/jet_elements_env_translation_unit.c`:
`frame.c`, `jets.c`, `sha256.c`, `elements/ops.c`, `elements/env.c`.
`elements/elementsJets.c` is not in this unit, because it and
`elements/env.c` each define a static `isFee` with a different type and so
cannot share a translation unit. `check-definitions.py` checks that the 64 C
definitions mentioned by the SHA proof modules used here are textually those
of the SHA unit, and that the Elements tap operations (`make_tapleaf`,
`make_tapbranch` and their tag arrays) are those of the Elements jets unit.

## Proofs

`simplicity_elements_mallocTapEnv` has the same C text as the Bitcoin
function up to the names of the two structures and of `make_tapleaf`, and
the structures have the same members. `gen-elements-env-ports.py` ports the
thirteen C-side modules of `bitcoin-env/C` by asserted substitutions; Coq
re-checks everything against the Elements program (statement shapes by
`reflexivity`, field offsets by computation, the tapleaf tag
"TapLeaf/elements" through the Elements `make_tapleaf` proof of
`elements-sha/C`).

Result (`C/jet_elements_env_tapenv.v`): `eval_mallocTapEnv` for
`f_simplicity_elements_mallocTapEnv` — the returned fresh block holds the
path pointer, `tapLeafHash = el_make_tapleaf_regs …`, `tappathHash`,
`tapEnvHash`, internal key, script CMR, path length, leaf version and the
path array; pre-existing memory is unchanged. Same premises as the Bitcoin
theorem, with the Elements tag array.

Not ported: the links to canonical hash values (they use the Bitcoin
specification modules; the Elements primitive port of `C/jet_elements_prim.v`
has no cached-hash relations yet).

## Build

```bash
bash Coq/build-elements-env.sh -j4
```

```bash
bash Coq/audit-elements-env.sh
```

## Receipts

| Commit | Command | Result |
|---|---|---|
| `a0681969` | `bash Coq/audit-elements-env.sh` | generated ports current; no admissions; assumption audit passed: 3 reports within the six inherited assumptions (`eval_sha256_toMidstate`, `ctxo_hash`, `eval_mallocTapEnv` for `f_simplicity_elements_mallocTapEnv`); `coqchk` passed for `C.jet_elements_env_tapenv` and its dependencies; exit 0; 16 min |
