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

### Helpers of `mallocTransaction` (proved; six inherited assumptions)

| Module | Result |
|---|---|
| `C/jet_bitcoin_env_ctxo_more.v` | `ctxo_uchar`, `ctxo_u32be`, `ctxo_u64be` |
| `C/jet_bitcoin_env_copyoutput.v` | `eval_copyOutput`: script hash and value of a `sigOutput` |
| `C/jet_bitcoin_env_copyinput_fill.v` | `ci_fill_exec`: the `sigInput` compound literal and its copy; `zsr_exec` (zero runs through any midstate expression) |
| `C/jet_bitcoin_env_copyinput.v` | **`eval_copyInput`**: annex hash (or zeros and `hasAnnex = 0` for a null annex), scriptSig hash, previous txid, output index, spent output, sequence |
| `C/jet_bitcoin_env_tx_arith.v` | size arithmetic: no overflow check fires, both paddings are zero |
| `C/jet_bitcoin_env_tx_prelude.v` | `mt_prelude`: statements 1-21 of `mallocTransaction` (guards, sizes, `malloc`, `tx`/`input`/`output`) |
| `C/jet_bitcoin_env_tx_fill.v` | `mt_fill_exec`: the transaction compound literal and its copy (`mt_filled`); `zsl_exec` |

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

1. (done) `tapenv_describes_exists` (`C/jet_bitcoin_env_tapenv_describe.v`):
   for every raw taproot environment and any transaction-side data there is a
   logical environment satisfying `tapenv_describes`, built from the bytes
   the builder read. The hypothesis of `mallocTapEnv_cached_hashes` is thus a
   definition of the logical environment, not an assumption.
2. `simplicity_bitcoin_mallocTransaction` (3200 lines of Clight). Toolkit in
   place: `eval_malloc`, `eval_sha256_toMidstate`, `eval_hashBuffer`,
   `eval_copyOutput` (`C/jet_bitcoin_env_copyoutput.v`), `ctxo` with
   `ctxo_init/hash/uchar/u32be/u64be/finalize`
   (`C/jet_bitcoin_env_ctxo.v`, `…_ctxo_more.v`), `ctxo_other` to carry the
   other live contexts across an operation, and the continuation-style
   method (`drop_seq`, `te_restK`) used for `mallocTapEnv`. Stages:
   - (done) `copyOutput`, `copyInput`, the prelude (`mt_rest1`), the compound
     literal and copy (`mt_rest2` is the body from `sha256_toMidstate(tx->txid.s, …)`);
   - next: a multi-context invariant (a list of `ctxo` states with pairwise
     distinct context blocks and disjoint 32-byte output fields of the
     allocated block; an operation on one context preserves the others by
     `ctxo_other` and the operation's frame condition) for the two loops;
   - prelude: sizes with two paddings and four overflow checks, `malloc`.
     Layout (computed with `envu_field_offset`): `bitcoinTransaction` —
     `input` 0, `output` 8, then thirteen midstates 32 bytes apart from
     `outputValuesHash` 16 (`outputScriptsHash` 48, `outputsHash` 80,
     `inputOutpointsHash` 112, `inputValuesHash` 144, `inputScriptsHash` 176,
     `inputUTXOsHash` 208, `inputSequencesHash` 240, `inputAnnexesHash` 272,
     `inputScriptSigsHash` 304, `inputsHash` 336, `txHash` 368), `txid` 400,
     `totalInputValue` 432, `totalOutputValue` 440, `numInputs` 448,
     `numOutputs` 456, `version` 464, `lockTime` 472, `isFinal` 480;
     `sigInput` is 160 bytes, `sigOutput` 40, both 8-aligned, so both
     paddings are 0 and the allocation is
     `sizeof(bitcoinTransaction) + 160 * numInputs + 40 * numOutputs`;
   - the transaction compound literal and copy, `toMidstate` of the txid;
   - eight `sha256_init`, the input loop (invariant: eight `ctxo` states on
     disjoint 32-byte fields of the allocated block, `totalInputValue`,
     `isFinal`), six `finalize`, the two derived hashes;
   - three `sha256_init`, the output loop, two `finalize`, `outputsHash`;
   - `txHash`; return; then the links to `input_outpoints_hash_of`,
     `words_hash_of …`, `inputs_hash_of`, `outputs_hash_of`, `tx_hash_of`
     of the accepted modules (`sha_stream_absorb_i` is the bridge).
3. The same for `elements/env.c` (`Coq/elements-env`: the C-side
   `mallocTapEnv` port is generated; links need Elements cached-hash
   relations).

## Build

```bash
bash Coq/build-bitcoin-env.sh -j4
```

```bash
bash Coq/audit-bitcoin-env.sh
```

Never `vm_compute` a composite lookup of a late structure (the records carry
large proof terms); use `envu_field_at`.

## Receipts

| Commit | Command | Result |
|---|---|---|
| `d4e58f00` | `bash Coq/audit-bitcoin-env.sh` | generated module current; no admissions; assumption audit passed: 7 reports within the six inherited assumptions (`eval_sha256_toMidstate`, `eval_hashBuffer`, `eval_malloc`, `ctxo_init`, `ctxo_hash`, `ctxo_finalize`, `eval_mallocTapEnv`); `coqchk` passed for `C.jet_bitcoin_env_tapenv`, `C.jet_bitcoin_env_hashbuffer` and their dependencies; exit 0; 13 min |
| `4b7fa7b8` | `bash Coq/audit-bitcoin-env.sh` | assumption audit passed: 12 reports within the six inherited assumptions (the seven above, `tapleaf_hash_link`, `tappath_hash_link`, `tap_env_hash_link`, `mallocTapEnv_cached_hashes`, `tapenv_describes_exists`); `coqchk` passed for `C.jet_bitcoin_env_tapenv_link` (which requires `C.jet_bitcoin_env_tapenv`), `C.jet_bitcoin_env_tapenv_describe`, `C.jet_bitcoin_env_hashbuffer` and their dependencies; exit 0; 16 min |
