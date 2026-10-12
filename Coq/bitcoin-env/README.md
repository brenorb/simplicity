# The Bitcoin environment builders (`C/bitcoin/env.c`)

The accepted environment-reading jets take the C environment as given: their
relations say, for example, that the cached `tapLeafHash` field holds the
canonical tagged hash. Those are facts the *caller* establishes. This
directory proves them from the code that actually builds the environment.

Unregistered; accepted sources are only read.

## Program

`C/jets_bitcoin_env.v` is clightgen's output (`C/regenerate-bitcoin-env.sh`)
for `C/jet_bitcoin_env_translation_unit.c`: the SHA translation unit followed
by `bitcoin/env.c`. `check-definitions.py` checks that all 495 functions and
globals of the SHA unit have identical generated text in it and that the SHA
unit's composites are a prefix of its composites. New functions:
`sha256_toMidstate`, `hashBuffer`, `copyOutput`, `copyInput`,
`simplicity_bitcoin_mallocTransaction`, `…freeTransaction`,
`simplicity_bitcoin_mallocTapEnv`, `…freeTapEnv`.

`build-bitcoin-env.sh` builds the derived tree `tree/` (ignored by git) in
which `C.jets_sha` is a copy of that program, so every accepted SHA-unit
proof module is recompiled for it unchanged and `sha_ge` is the environment
unit's global environment.

## Proved so far (six inherited assumptions; `memcpy_model` explicit where the SHA code needs it)

| Module | Result |
|---|---|
| `C/jet_env_store_words.v` | consecutive 32-bit stores as one operation (contents, permissions, unchanged memory) |
| `C/jet_bitcoin_env_field_eval.v` (generated) | struct-field evaluation and checked field offsets for the builder structures |
| `C/jet_bitcoin_env_tomidstate.v` | `eval_sha256_toMidstate`: stores the eight big-endian words of 32 bytes |
| `C/jet_bitcoin_env_hashbuffer.v` | `eval_hashBuffer`: writes the SHA-256 state of a raw buffer to any writable midstate |

| `C/jet_bitcoin_env_malloc.v` | `eval_malloc`: the `malloc` call (CompCert's defined `EF_malloc` semantics) |
| `C/jet_bitcoin_env_ctxo.v` | `ctxo`: SHA context whose output midstate is any writable location; `ctxo_init`, `ctxo_hash`, `ctxo_finalize` |
| `C/jet_bitcoin_env_tapenv_prelude.v` | `te_prelude`: statements 1-10 of `mallocTapEnv` (guards, overflow checks, `malloc` of `176 + 32 * pathLen`) |
| `C/jet_bitcoin_env_tapenv_key.v` | `te_key`: statements 11-12 (internal key into the local, `path` pointer) |
| `C/jet_bitcoin_env_tapenv_fill.v` | `te_fill`: statement 13 (compound literal and struct copy to the allocated block) |

| `C/jet_bitcoin_env_tapenv_cmr.v` | `te_cmr`: `sha256_toMidstate(env->scriptCMR.s, rawEnv->scriptCMR)` |
| `C/jet_bitcoin_env_tapenv_loop.v` | `te_loop_exec`: the tap-path loop, by induction over iterations, for every path length |
| `C/jet_bitcoin_env_tapenv_path.v` | `te_path`: `tappathHash` (init, loop, finalize) |
| `C/jet_bitcoin_env_tapenv_tail.v` | `te_tail`: `make_tapleaf` with its struct copy, `tapEnvHash`, `return env` |
| `C/jet_bitcoin_env_tapenv.v` | **`eval_mallocTapEnv`**: the whole function |

### `eval_mallocTapEnv`

For a raw taproot environment whose structure, control block
(`33 + 32 * pathLen` bytes) and script CMR (32 bytes) are readable and whose
`pathLen` is at most 128, the call
`simplicity_bitcoin_mallocTapEnv(rawEnv)` returns a pointer to a fresh block
`bA` such that (`tapenv_built`):

- offset 0: `path` (null for an empty path, else `bA + 176`);
- offset 8: `tapLeafHash` = `make_tapleaf_regs (controlBlock[0] & 0xfe) cmr`;
- offset 40: `tappathHash` = `te_tappath_regs` (the branch hashes absorbed, then padding);
- offset 72: `tapEnvHash` = `te_tapenv_regs` (leaf hash, path hash, internal key absorbed, then padding);
- offset 104: `internalKey`, 136: `scriptCMR` (big-endian words of the raw bytes);
- offset 168: `pathLen`, 169: `leafVersion`; from 176: the path array;

and every load from a block that existed before the call is unchanged.
Premises that are facts about program start-up rather than inputs: the SHA
dispatch pointer, the maximum counter and the "TapLeaf" tag array hold their
initial values (`sha_dispatch_ok`, the `GM` load, `sha_tapleaf_tag_ok`) —
exactly the start-up invariant of `Coq/startup`. `memcpy_model` is an
explicit premise. Six inherited assumptions.

Not covered: the NULL-return paths (null argument, `pathLen > 128`, the
overflow checks, `malloc` failure — CompCert's `malloc` cannot fail).

The step lemmas are continuation-style: `te_restK` names the body after the
statements already executed, and each lemma turns an execution of the
remainder into an execution of the larger statement.

### The cached hashes are the canonical ones (`C/jet_bitcoin_env_tapenv_link.v`)

`C/jet_bitcoin_env_stream.v` expresses `sha_stream` (the hash value used by
the accepted relations) through the integer-level absorbing state. With it:

- `tapleaf_hash_link`: `hash256_reg (tapleaf_hash_of e) = make_tapleaf_regs v cmr`;
- `tappath_hash_link`: `hash256_reg (words_hash_of 5 3 (tappath_of e)) = te_tappath_regs pb n`;
- `tap_env_hash_link`: `hash256_reg (tap_env_hash_of e) = te_tapenv_regs …`

(all three closed under the global context), and

- **`mallocTapEnv_cached_hashes`**: for a logical environment `e` that
  describes the raw data the builder read (`tapenv_describes`: same leaf
  version, script CMR, path and internal key), the block returned by the
  actual C function satisfies `uint32_array_at m' bA 8 (hash256_reg
  (tapleaf_hash_of e))`, `… 40 (… words_hash_of 5 3 (tappath_of e))` and
  `… 72 (… tap_env_hash_of e)` — the taproot part of
  `hash_getter_rep … 8 8 176`, `… 8 40 176`, `… 8 72 176`. Six inherited
  assumptions; `memcpy_model` and the start-up state explicit.

What is still the caller's: making `txEnv.taproot` point at the block
(`simplicity_bitcoin_build_txEnv`, not in this unit) and the transaction
half of the environment.

## Next

1. `tapenv_describes` is a hypothesis about `e`; a constructor of `e` from
   the raw bytes (so that it holds by definition) would close the loop.
2. `simplicity_bitcoin_mallocTransaction` (same toolkit: `eval_hashBuffer`,
   `ctxo`, `eval_malloc`).
3. The same for `elements/env.c`.

## Build

```bash
bash Coq/build-bitcoin-env.sh -j4
```

```bash
bash Coq/audit-bitcoin-env.sh
```

Never `vm_compute` a composite lookup of a late structure (the records carry
large proof terms); use `envu_field_at`.
