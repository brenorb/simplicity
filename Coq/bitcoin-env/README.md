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
| `C/jet_bitcoin_env_ctxs.v` | `ctxs`: several live contexts writing distinct fields of one block; `ctxs_other`, `ctxs_frame` |
| `C/jet_bitcoin_env_tx_init.v` | `mt_init_step`, `inits_exec`: any run of `ctx_X = sha256_init(tx->X.s)` statements (all twelve of the function) |
| `C/jet_bitcoin_env_ctxs_ops.v`, `…_ctxs_calls.v` | `ctxs_live`, `live_step`, `live_kill`; `live_hash`, `live_u32be`, `live_u64be`, `live_uchar`, `live_finalize` on one of several live contexts |
| `C/jet_bitcoin_env_tx_calls.v` | Clight call wrappers for the context operations, for any context variable |
| `C/jet_bitcoin_env_tx_txid.v`, `…_tx_inblock.v` | the txid step; the input block is `inits_stmt` of eight items followed by `mt_in_tail` |
| `C/jet_bitcoin_env_tx_txhash.v` | `mt_txhash`: the `txHash` block and `return tx` (`mt_rest5`) |
| `C/jet_bitcoin_env_tx_outdefs.v`, `…_tx_outloop.v` | `out_loop`: the output loop for every output count (invariant `out_inv`) |
| `C/jet_bitcoin_env_tx_outblock.v` | `mt_outblock_exec`: the output block (three initialisations, the loop, two finalisations, `outputsHash`) |
| `C/jet_bitcoin_env_ctxs_core.v` | `LS`, `mfrP`: live contexts without overflow flags and separation side conditions; `LS_hash`, `LS_u32be`, `LS_u64be`, `LS_uchar`, `LS_finalize`, `LS_other` |
| `C/jet_bitcoin_env_tx_indefs.v` | per-input data (`in_data`), the six running states, `in_cores`, the stored record `in_rec`, the raw input `raw_in_at` |
| `C/jet_bitcoin_env_tx_inops.v` | `in_ops`: the context operations of one input iteration, with the annex case split (`in_annex`) |
| `C/jet_bitcoin_env_tx_inloop.v` | `in_loop`: the input loop for every input count (invariant `in_inv`) |
| `C/jet_bitcoin_env_tx_inexec.v` | `mt_inblock_exec`: the input block (eight initialisations, the loop, six finalisations, `inputUTXOsHash`, `inputsHash`); `items_wf_sep` |
| `C/jet_bitcoin_env_tx.v` | **`eval_mallocTransaction`**: the whole function |

### `eval_mallocTransaction`

For a raw transaction whose structure, txid (32 bytes), input array
(`numInputs` entries of 64 bytes, with their annexes, previous txids and
script buffers) and output array (`numOutputs` entries of 24 bytes with
their script buffers) are readable, the call
`simplicity_bitcoin_mallocTransaction(rawTx)` returns a pointer to a fresh
block `bA` such that (`tx_built`):

- offsets 0, 8: `input = bA + 488`, `output = bA + 488 + 160 * numInputs`;
- offsets 16, 48, 80: `outputValuesHash`, `outputScriptsHash`, `outputsHash`
  (`out_regsV`, `out_regsS`, `out_regsO`);
- offsets 112 … 336: `inputOutpointsHash`, `inputValuesHash`,
  `inputScriptsHash`, `inputUTXOsHash`, `inputSequencesHash`,
  `inputAnnexesHash`, `inputScriptSigsHash`, `inputsHash`
  (`in_regsP/V/S/U/Q/N/G/I`: the bytes each context absorbed, then padding);
- offset 368: `txHash` (`mt_txhash_regs` of version, lock time, `inputsHash`,
  `outputsHash`, `inputUTXOsHash`); offset 400: `txid` (big-endian words);
- offsets 432 … 480: `totalInputValue`, `totalOutputValue`, `numInputs`,
  `numOutputs`, `version`, `lockTime`, `isFinal` (cleared by any input whose
  sequence is below `0xffffffff`);
- the `sigInput` records (`in_rec`) and the `sigOutput` records;

and every load from a block that existed before the call is unchanged.
Legitimate input requirements: readability of the raw data and the two
array-extent bounds (`ori + 64 * numInputs`, `oro + 24 * numOutputs` inside
the address space). The array pointers are required only for non-empty
arrays, so a null pointer with a zero count is covered. Start-up facts
(`sha_dispatch_ok`, the `GM` load) and `memcpy_model` are explicit premises.
Six inherited assumptions.

Not covered: `malloc` failure (CompCert's `malloc` cannot fail). The size
computation is proved not to overflow for every pair of 32-bit counts.

The loops are proved by invariant and induction on the remaining
iterations; the stages are continuation-style (`mt_rest1 … mt_rest5`).

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

### The transaction's cached hashes are the canonical ones (`C/jet_bitcoin_env_tx_link.v`)

- `fold_link`, `fold_link_count`, `words_link`: a state built by absorbing
  one element's bytes per iteration is `sha256_bytes_of` of the
  concatenation; `pair_link`, `triple_link`, `tx_link_gen` for the derived
  hashes (pure, closed under the global context).
- `tx_describes e …`: the logical environment `e` has the counts, version,
  lock time, per-input scalars/outpoint and per-output value the builder
  read, and its script, script-signature, annex and output-script hashes
  are the `hashBuffer` states of the bytes read.
- **`mallocTransaction_cached_hashes`**: for such an `e` the block returned
  by the actual C function satisfies
  `uint32_array_at m' bA 16 (hash256_reg (words_hash_of 3 5 (output_values_of e)))`,
  `… 48 (… output_scripts_of e)`, `… 80 (outputs_hash_of e)`,
  `… 112 (input_outpoints_hash_of e)`, `… 144 (… input_values_of e)`,
  `… 176 (… input_scripts_of e)`, `… 208 (input_utxos_hash_of e)`,
  `… 240 (… input_sequences_of e)`, `… 272 (input_annexes_hash_of e)`,
  `… 304 (… input_script_sigs_of e)`, `… 336 (inputs_hash_of e)`,
  `… 368 (tx_hash_of e)` — the transaction part of every accepted
  `hash_getter_rep … 0 <offset> 432` relation. Six inherited assumptions.

### Against raw data (`C/jet_bitcoin_env_bytestring.v`, `…_tx_raw.v`, `…_tapenv_raw.v`)

- **`hash_buffer_bytestring`**: `hash_buffer_regs (map byte_int x) =
  hash256_reg (byteStringHash x)` for every byte string below 2^61 bytes —
  the C streaming SHA-256 (blocks absorbed through `SHA256.hash_block`, then
  the C padding `sha_pad`) is the functional SHA-256 of `Digest.v`
  (`process_msg init_registers (generate_and_pad_alt x)`). Pure; only
  functional extensionality (inherited, from VST's `generate_and_pad'_eq`).
- `raw_tx_holds R …` / `raw_tapenv_holds R …`: the memory read by the
  builders holds the *bytes* of the raw environment `R` of the accepted
  `C/jet_bitcoin_raw_env.v`. Then `raw_tx_describes` and
  `raw_tapenv_describes` give `tx_describes` / `tapenv_describes` for
  `project_raw_environment R`, hence
  **`mallocTransaction_raw_cached_hashes`** and
  **`mallocTapEnv_raw_cached_hashes`**: the cached hashes written by the two
  real builders are the canonical hashes of the raw environment; no fact
  about a cached hash is assumed.

### The whole environment (`…_txenv.v`, `…_txenv_link.v`, `…_build.v`, `…_free.v`, `…_lifecycle.v`)

The unit now also contains `C/bitcoin/txEnv.c` (every earlier definition is
textually unchanged; `check-definitions.py`).

- **`eval_build_txEnv`**: the real `simplicity_bitcoin_build_txEnv` (struct
  return through the hidden result pointer) stores the two pointers, the
  index and `sigAllHash`; `sigall_link`: that state is `sig_all_hash_of e`.
- **`build_environment`**: `mallocTransaction`, `mallocTapEnv` and
  `build_txEnv`, run in sequence on memory holding the bytes of a raw
  environment `R` (`tx_readable`, `tap_readable`, `raw_tx_holds`,
  `raw_tapenv_holds`) under the SHA start-up state (`sha_started`), leave
  `env_ready m3 bD oD bT bE (project_raw_environment R) …`: the `txEnv`, its
  transaction block and its taproot block with the data and the canonical
  cached hashes; existing memory is unchanged outside the destination.
- `eval_mallocTransaction` / `eval_mallocTapEnv` also state the size header
  at offset -8 and the `Freeable` permission over `[-8, size)`;
  **`eval_freeTransaction`**, **`eval_freeTapEnv`** and
  **`free_environment`**: the real free functions release exactly the two
  blocks (CompCert's `EF_free`, defined semantics).

### Every accepted Bitcoin environment relation is established (`…_relations.v`, `…_relations_indexed.v`)

For the `txEnv` that `build_environment` leaves (`env_ready`), 50 theorems
`ready_<jet>` prove the environment relation that the accepted jet theorem
takes as a premise: `version`, `lock_time`, `num_inputs`, `num_outputs`,
`total_input_value`, `total_output_value`, `fee`, `tx_is_final`, `lock`,
`check_lock`, `distance`, `current_index`, the sixteen cached-hash getters
and `sig_all_hash`, `internal_key`, `script_cmr`, `tapleaf_version`,
`tappath`, the indexed input relations (`input_sequence`, `input_value`,
`input_prev_outpoint`, `input_script_hash`, `input_script_sig_hash`,
`input_annex_hash`) and their current-input variants, `output_value`,
`output_script_hash`, and the SHA-based `input_hash`, `input_utxo_hash`,
`output_hash` (these three also need `sha_globals_ok`, the start-up state).
The running totals are the sums of the spec (`total_link`), `isFinal` is
`forallb sequence_final` (`final_link`).

Two relations are not unconditional, and both are reported rather than
papered over:

- `ready_tappath` requires a non-empty path: `mallocTapEnv` stores
  `path = NULL` when `pathLen == 0`, while the accepted
  `bitcoin_tappath_env_rep` asks for a pointer unconditionally. The jet
  only reads `path` when `i < pathLen`, so the accepted relation is stronger
  than what the real caller provides for single-leaf trees.
  Resolved additively: `Coq/C/jet_bitcoin_tappath_nullable.v` proves the
  same jet (`bitcoin_tappath_nullable_local_spec`, the accepted proof with
  the pointer load taken inside the in-range branch; same six assumptions)
  under `bitcoin_tappath_env_rep_nullable`, which is implied by the accepted
  relation (`bitcoin_tappath_env_rep_weaken`) and which the built `txEnv`
  satisfies for every path length (`ready_tappath_nullable`,
  `…_relations_tappath.v`).
- `ready_transaction_id` requires that the 32 raw `txid` bytes are the
  transaction id: the builder copies them, and the C library never computes
  `raw_transaction_id R` (a double SHA-256 of the serialisation). This is a
  genuine input requirement.

## Next

1. (done) `tapenv_describes_exists` (`C/jet_bitcoin_env_tapenv_describe.v`):
   for every raw taproot environment and any transaction-side data there is a
   logical environment satisfying `tapenv_describes`, built from the bytes
   the builder read. The hypothesis of `mallocTapEnv_cached_hashes` is thus a
   definition of the logical environment, not an assumption.
2. (done) `simplicity_bitcoin_mallocTransaction`: `eval_mallocTransaction`
   (`C/jet_bitcoin_env_tx.v`), see above. Method notes: in these large
   contexts plain `lia` takes minutes — use `flia` (`zkeep; lia`, defined in
   `…_tx_outloop.v`) and give disequalities explicitly instead of
   `congruence`; work with `LS` (`…_ctxs_core.v`) rather than `ctxs_live`;
   never let a tactic try a wrong field offset (`hoff` computes the index:
   a failed unification of two `envu_field_at` instances unfolds the
   composite environment).
   The links, `build_txEnv`, the free functions, `build_environment` and
   the relation sweeps are done (sections above). Remaining here: relate
   `exec.c`'s driver to `build_environment`; decide with the integration
   owner how the accepted `bitcoin_tappath_env_rep` should treat an empty
   path.
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
| `e22c5eb9` | `bash Coq/audit-bitcoin-env.sh` | assumption audit passed: 18 reports within the six inherited assumptions (the twelve above, `eval_copyOutput`, `eval_copyInput`, `mt_inblock_exec`, `mt_outblock_exec`, `mt_txhash`, `eval_mallocTransaction`); `coqchk` passed for `C.jet_bitcoin_env_tapenv_link`, `C.jet_bitcoin_env_tapenv_describe`, `C.jet_bitcoin_env_hashbuffer`, `C.jet_bitcoin_env_tx` (which requires every `mallocTransaction` stage) and their dependencies; exit 0; 16 min |
| `5d86e8ae` | `bash Coq/audit-bitcoin-env.sh` | assumption audit passed: 23 reports within the six inherited assumptions (the eighteen above, `tx_cached_hashes`, `mallocTransaction_cached_hashes`, `hash_buffer_bytestring`, `raw_tx_describes`, `mallocTransaction_raw_cached_hashes`); `coqchk` passed for `C.jet_bitcoin_env_tapenv_link`, `C.jet_bitcoin_env_tapenv_describe`, `C.jet_bitcoin_env_hashbuffer`, `C.jet_bitcoin_env_tx_raw` (which requires `C.jet_bitcoin_env_tx`, the hash links and the `byteStringHash` equivalence) and their dependencies; exit 0; 16 min |
| `c255a97f` | `bash Coq/audit-bitcoin-env.sh` | unit extended with `bitcoin/txEnv.c`; assumption audit passed: 81 reports within the six inherited assumptions (the 23 above, `raw_tapenv_describes`, `mallocTapEnv_raw_cached_hashes`, `eval_freeTransaction`, `eval_freeTapEnv`, `eval_build_txEnv`, `sigall_link`, `build_environment`, `free_environment` and the 50 `ready_<jet>` theorems); `coqchk` passed for `C.jet_bitcoin_env_tapenv_link`, `C.jet_bitcoin_env_tapenv_describe`, `C.jet_bitcoin_env_hashbuffer`, `C.jet_bitcoin_env_relations_indexed` (which requires the three builders, their raw links, `build_environment` and both relation sweeps), `C.jet_bitcoin_env_lifecycle` and their dependencies; exit 0; 18 min |
