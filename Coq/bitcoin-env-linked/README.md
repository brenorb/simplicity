# Environment builders for the memcpy-linked environment unit

Branch `claude/shared-obligations`; unregistered.

`bitcoin-env/` proves the real environment functions of `C/bitcoin/env.c`
and `C/bitcoin/txEnv.c` under the explicit premise `memcpy_model` (the unit
declares `memcpy` external). Here the same proof sources are compiled,
unchanged, against the *linked* unit: `C/jets_bitcoin_env.v` with that
external declaration replaced by the internal definition generated from
`C/jet_memcpy_exact.c` (`linked/gen-jets.py`, the derivation used for the
linked core and SHA units). In that program `memcpy_model` is the theorem
`memcpy_model_holds` (`linked/C/jet_memcpy_model.v`), so:

| Result (`C/jet_bitcoin_env_linked.v`) | Statement |
|---|---|
| `eval_mallocTapEnv_linked`, `eval_mallocTransaction_linked`, `eval_build_txEnv_linked` | the three builders, no `memcpy_model` premise |
| `mallocTapEnv_raw_cached_hashes_linked`, `mallocTransaction_raw_cached_hashes_linked` | cached hashes canonical for the raw environment |
| `build_environment_linked`, `build_environment_readable_linked` | the composed builders leave `env_ready` |

Boundary (as in `linked/README.md`): these are statements about the C code
linked with the reference `memcpy`; for the unit with an external `memcpy`
the premise remains. The `ready_<jet>` relation theorems, the free functions
and the start-up results of `bitcoin-env/` never depended on `memcpy_model`.

```bash
bash Coq/build-linked.sh          # prerequisite: the linked tree
bash Coq/build-bitcoin-env-linked.sh -j4
bash Coq/audit-bitcoin-env-linked.sh
```

## Receipts

| Commit | Command | Result |
|---|---|---|
