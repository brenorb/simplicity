# Elements jets — continuation record

Branch `claude/shared-obligations` (fork point `a8685146`). Unregistered: no
entry in the shared coverage files; integration is left to the main checkout.
Reserved for this line of work in `../../COORDINATION.md`.

## Foundation

| item | file |
| --- | --- |
| Translation unit (frame helpers, core jets, SHA-256, Elements ops, Elements jets) | `jet_elements_translation_unit.c` → `jets_elements.v` (`regenerate-elements-jets.sh`) |
| Global environment, symbol blocks, field offsets | `jet_elements_linkage.v` |
| 20 verified core frame helpers transported into `elements_ge` | `jet_elements_transport.v` |
| Elements primitive signature and semantics | `jet_elements_prim.v` — **a Coq port of `Haskell/Elements/Simplicity/Elements/{DataTypes,Primitive}.hs` awaiting source review**; `check-elements-prim-port.py` checks constructors, order, types, names and prefix against Haskell (not the semantics clauses) |
| Execution frameworks | `jet_elements_{word_helpers,frame_access,env_read,write32_*,getter32_*,effects,field_eval,wrapper,steps,call,env_load,hash_*,write32s_*,write8_step,index_eval,read_step,indexed_*,current_exec}.v` — mechanical ports of the accepted `jet_bitcoin_*` modules by `port-bitcoin-to-elements.py` plus layout constants |

Remaining external functions of the unit: `memcpy`, `memcmp`, `memset`,
`simplicity_generic_taptweak`, `__assert_fail`.

Layout facts used (computed by `vm_compute` in the proofs): `txEnv` 88 bytes
(tx 0, taproot 8, genesisHash 16, ix 80); `elementsTransaction` 760 (input 0,
output 8, txid 664, numInputs 696, numOutputs 704, version 720, lockTime 728);
`sigInput` 544 (annexHash 0, pegin 32, scriptSigHash 64, prevOutpoint 96,
txo 136, sequence 248, issuance 256, hasAnnex 536, isPegin 537); `sigOutput`
248 (surjectionProofHash 36, rangeProofHash 68, scriptPubKey 180);
`elementsTapEnv` 176 (path 0, internalKey 104, scriptCMR 136, pathLen 168,
leafVersion 169).

## Proved jets (52), each against its specification in `Haskell/Simplicity/Elements/Jets.hs`

| C function | primitive | theorem (module) |
| --- | --- | --- |
| `simplicity_version` | Version | `elements_version_local_spec` (`jet_elements_version_local`) |
| `simplicity_lock_time` | LockTime | `elements_locktime_local_spec` (`jet_elements_locktime_local`) |
| `simplicity_current_index` | CurrentIndex | `elements_current_index_local_spec` (`jet_elements_current_index_local`) |
| `simplicity_script_cmr` | ScriptCMR | `elements_script_cmr_local_spec` (`jet_elements_script_cmr_local`) |
| `simplicity_transaction_id` | TransactionId | `elements_transaction_id_local_spec` (`jet_elements_hash_field_jets`) |
| `simplicity_internal_key` | InternalKey | `elements_internal_key_local_spec` (same) |
| `simplicity_genesis_block_hash` | GenesisBlockHash | `elements_genesis_block_hash_local_spec` (`jet_elements_genesis_hash_local`) |
| `simplicity_tapleaf_version` | TapleafVersion | `elements_tapleaf_version_local_spec` (`jet_elements_tapleaf_version_local`) |
| `simplicity_tappath` | Tappath | `elements_tappath_local_spec` (`jet_elements_tappath_local`) |
| `simplicity_input_sequence` | InputSequence | `elements_input_sequence_local_spec` (`jet_elements_indexed_scalar_jets`) |
| `simplicity_input_prev_outpoint` | InputPrevOutpoint | `elements_input_prev_outpoint_local_spec` (`jet_elements_indexed_ptr_jets`) |
| `simplicity_output_script_hash` | OutputScriptHash | `elements_output_script_hash_local_spec` (same) |
| `simplicity_input_script_sig_hash` | InputScriptSigHash | `elements_input_script_sig_hash_local_spec` (`jet_elements_input_hash_jets`, generated) |
| `simplicity_input_script_hash` | InputScriptHash | `elements_input_script_hash_local_spec` (same) |
| `simplicity_issuance_asset_proof` | IssuanceAssetProof | `elements_issuance_asset_proof_local_spec` (same) |
| `simplicity_issuance_token_proof` | IssuanceTokenProof | `elements_issuance_token_proof_local_spec` (same) |
| `simplicity_output_surjection_proof` | OutputSurjectionProof | `elements_output_surjection_proof_local_spec` (`jet_elements_output_proof_jets`) |
| `simplicity_output_range_proof` | OutputRangeProof | `elements_output_range_proof_local_spec` (same) |
| `simplicity_input_annex_hash` | InputAnnexHash | `elements_input_annex_hash_local_spec` (`jet_elements_annex_local`) |
| `simplicity_input_pegin` | InputPegin | `elements_input_pegin_hash_local_spec` (`jet_elements_pegin_local`, generated) |
| `simplicity_input_asset` | InputAsset | `elements_input_asset_local_spec` (`jet_elements_asset_jets`) |
| `simplicity_output_asset` | OutputAsset | `elements_output_asset_local_spec` (same) |
| `simplicity_output_nonce` | OutputNonce | `elements_output_nonce_local_spec` (same) |
| `simplicity_input_amount` | program `Prog.inputAmount` | `elements_input_amount_local_spec` (`jet_elements_amount_jets`) |
| `simplicity_output_amount` | program `Prog.outputAmount` | `elements_output_amount_local_spec` (same) |
| `simplicity_reissuance_blinding` | ReissuanceBlinding | `elements_reissuance_blinding_local_spec` (`jet_elements_issuance_jets`) |
| `simplicity_new_issuance_contract` | NewIssuanceContract | `elements_new_issuance_contract_local_spec` (same) |
| `simplicity_reissuance_entropy` | ReissuanceEntropy | `elements_reissuance_entropy_local_spec` (same) |
| `simplicity_issuance_asset_amount` | IssuanceAssetAmount | `elements_issuance_asset_amount_local_spec` (`jet_elements_issuance_amount_jets`) |
| `simplicity_current_prev_outpoint` | `CurrentIndex >>> assert InputPrevOutpoint` | `elements_current_prev_outpoint_local_spec` (`jet_elements_current_input_jets`, generated) |
| `simplicity_current_asset` | `CurrentIndex >>> assert InputAsset` | `elements_current_asset_local_spec` (same) |
| `simplicity_current_script_hash` | `CurrentIndex >>> assert InputScriptHash` | `elements_current_script_hash_local_spec` (same) |
| `simplicity_current_script_sig_hash` | `CurrentIndex >>> assert InputScriptSigHash` | `elements_current_script_sig_hash_local_spec` (same) |
| `simplicity_current_issuance_asset_proof` | `CurrentIndex >>> assert IssuanceAssetProof` | `elements_current_issuance_asset_proof_local_spec` (same) |
| `simplicity_current_issuance_token_proof` | `CurrentIndex >>> assert IssuanceTokenProof` | `elements_current_issuance_token_proof_local_spec` (same) |
| `simplicity_current_reissuance_blinding` | `CurrentIndex >>> assert ReissuanceBlinding` | `elements_current_reissuance_blinding_local_spec` (same) |
| `simplicity_current_new_issuance_contract` | `CurrentIndex >>> assert NewIssuanceContract` | `elements_current_new_issuance_contract_local_spec` (same) |
| `simplicity_current_reissuance_entropy` | `CurrentIndex >>> assert ReissuanceEntropy` | `elements_current_reissuance_entropy_local_spec` (same) |
| `simplicity_current_issuance_asset_amount` | `CurrentIndex >>> assert IssuanceAssetAmount` | `elements_current_issuance_asset_amount_local_spec` (same) |
| `simplicity_current_sequence` | `CurrentIndex >>> assert InputSequence` | `elements_current_sequence_local_spec` (`jet_elements_current_jets`, ported) |
| `simplicity_current_amount` | `CurrentIndex >>> assert Prog.inputAmount` | `elements_current_amount_local_spec` (`jet_elements_current_gen_jets`) |
| `simplicity_current_pegin` | `CurrentIndex >>> assert InputPegin` | `elements_current_pegin_local_spec` (same) |
| `simplicity_current_annex_hash` | `CurrentIndex >>> assert InputAnnexHash` | `elements_current_annex_hash_local_spec` (same) |
| `simplicity_tx_is_final` | program `txIsFinal` (loop over input sequences) | `elements_tx_is_final_local_spec` (`jet_elements_is_final_local`, ported) |
| `simplicity_tx_lock_height` | program `txLockHeight` | `elements_tx_lock_height_local_spec` (`jet_elements_lock_local`, ported) |
| `simplicity_tx_lock_time` | program `txLockTime` | `elements_tx_lock_time_local_spec` (same) |
| `simplicity_check_lock_height` | program `checkLockHeight` | `elements_check_lock_height_local_spec` (`jet_elements_check_lock`, ported; partial contract) |
| `simplicity_check_lock_time` | program `checkLockTime` | `elements_check_lock_time_local_spec` (same) |
| `simplicity_num_inputs` | `firstFail word32 (primitive InputScriptHash)` | `elements_num_inputs_local_spec` (`jet_elements_count_local`, ported) |
| `simplicity_num_outputs` | `firstFail word32 (primitive OutputScriptHash)` | `elements_num_outputs_local_spec` (same) |
| `simplicity_issuance_token_amount` | IssuanceTokenAmount | `elements_issuance_token_amount_local_spec` (`forward/proofs/jet_elements_issuance_token_jets`) |
| `simplicity_current_issuance_token_amount` | `CurrentIndex >>> assert IssuanceTokenAmount` | `elements_current_issuance_token_amount_local_spec` (same) |

Contracts are `application_jet_local_spec` / `application_jet_local_spec_sep`
in `elements_ge` over `Elements.env`. Boundaries that apply to all of them:

- The environment relations are initial representation requirements: they
  state that C fields hold the values the primitives denote (for hash
  fields, the SHA-256 of the logical byte string; for `transaction_id`,
  `txid` of the logical transaction). `C/elements/env.c`, which fills those
  fields, is not part of the unit and is not verified.
- `tappath` requires at most 128 path elements in its relation (the Haskell
  `TapEnv` has no explicit bound; the C field is an `unsigned char`).
- The canonical side is the ported `jet_elements_prim.v`, pending review.
- Confidential values: the relations state the C prefix tag (EXPLICIT = 1,
  EVEN_Y = 2, ODD_Y = 3; NONE = 0 for an absent nonce) and the data words;
  an explicit amount is its 64-bit union member. Data words are only
  required where the C code reads them (not for an absent nonce, and for
  issuance fields only when the primitive yields a value).
- `input_amount` / `output_amount` are specified by the two-primitive
  programs of `Programs/Transaction.hs`, written with the core combinators
  in `jet_elements_amount_jets.v` (`elements_amount_pair_spec`).

Supporting modules for these nine: `jet_elements_asset_helper.v` (static
`asset` and `nonce`), `jet_elements_amt_helper.v` (static `amt`, union
access), `jet_elements_issuance_helper.v` (the four tag-dispatched static
issuance helpers as one parametric function), `jet_elements_indexed_gen.v`
(generated: indexed getter over an arbitrary success statement),
`jet_elements_indexed_ptr2.v` (two helper calls on the selected element).
Executability on fresh frames: `jet_elements_executable.v` (first 20),
`jet_elements_executable_conf.v` (these nine) and
`jet_elements_executable_current.v` (the fourteen current-input jets).

Lock-time jets: `Programs/TimeLock.hs` defines `txIsFinal`, `txLockHeight`,
`txLockTime`, `checkLockHeight` and `checkLockTime` with the same text for
Bitcoin and Elements, and the C jets are the same; the proofs are the
Bitcoin-unit modules ported by `port-bitcoin-timelock-to-elements.py`
(layout: `isFinal` at 752, `lockTime` at 728). The relation states that
the cached C `isFinal` byte is `forallb sequence_final inputs` and that
`lockTime` is the logical lock time. The loop over inputs ranges over
Word32, which is why the ported `sigTx` carries the input-count bound of
the accepted `Bitcoin.sigTx` (`sigTxInBounds`). Executability:
`jet_elements_executable_lock.v`. The four `broken_do_not_use_*` distance
jets are not ported: Elements caches the distance in the transaction
record and specifies it by different programs than Bitcoin.

Count jets: ported by `port-bitcoin-count-to-elements.py` from the Bitcoin
count modules, with the searched primitive changed to the script-hash
primitives Elements uses; they need `sigTxOutBounds` as well.
Executability: `jet_elements_executable_count.v`.

Current-input jets (`if (numInputs <= ix) return false; ...; return true`):
the specification is `primitive CurrentIndex >>> assert SPEC` with the
literal `Programs.Bit.assert` (`jet_elements_current_spec.v`, ported from
the Bitcoin unit; one generic lemma `elements_current_sem` evaluates it for
any per-input primitive). The contracts are total: `envIx < length inputs`
is an invariant of `Elements.env` (the check of `primEnv`), and `envIx` is
a 32-bit word as in Haskell (`envIxWord32`, added to the port for this).
`jet_elements_current_ptr.v` / `_ptr_jets.v` are the ported single-helper
theorem, `jet_elements_current_gen.v` its generalization to an arbitrary
tail statement (footprint then includes the re-read environment words).

## No-premise statements

Every proved jet has a statement without memory, frame or environment
premise: for every input and every logical environment there are a memory,
frames and an environment pointer on which the C jet returns the canonical
verdict and leaves the encoding of the canonical result.

- `jet_elements_runs_everywhere.v`: 30 jets over the indexed,
  current-pointer and current-generic relations (`runs_everywhere`).
- `jet_elements_runs_everywhere_rest.v`: the other 20 (record-only
  relations, taproot record, transaction id, genesis hash, scalar input
  relations, annex/pegin arrays); `partial_runs_everywhere` for the two
  lock checks; `elements_tappath_runs_for_bounded_paths` keeps the bound
  its relation states (at most 128 path elements).

The environment relations are discharged by `jet_elements_env_constructible.v`
and `jet_elements_elem_buildable.v` over the generic `jet_env_constructible*.v`.
This shows the relations are satisfiable for every environment; it does not
verify `C/elements/env.c`, which builds the real environment.

## Provenance of the proof modules

`python3 C/check-elements-generated.py` (from `Coq/`) verifies that 32
modules are exact outputs of `port-bitcoin-to-elements.py` on the accepted
Bitcoin-unit modules, that 17 more are exactly what their generators
produce (`gen-elements-*.py`, `port-bitcoin-{timelock,count}-to-elements.py`,
all with asserted substitutions), and that the primitive signature matches
`Primitive.hs`. The remaining modules are written by hand.

## Receipts

- All 50 theorems: `Print Assumptions` = the six inherited assumptions
  (`sig_forall_dec`, `sig_not_dec`, `classic`, `functional_extensionality_dep`,
  `external_functions_sem`, `inline_assembly_sem`); no `admit`/`Admitted`/
  `Axiom`/`Parameter` in `jet_elements_*.v` (2026-10-12).
- `coqchk -silent -o` on the twelve theorem modules present at commit
  `0d5d45e3` (17 jets) and their dependency chains: exit 0 (69 s).
- `coqchk -silent -o` on `jet_elements_{tappath,annex,pegin}_local` and
  their dependency chains at `261b207c`: exit 0 (77 s).
- `coqchk -silent -o C.jet_elements_executable C.jet_elements_executable_conf`
  with dependency chains at `bffd9501` (29 jets): exit 0 (74 s).
- After the `envIxWord32` change every Elements module was rebuilt; `coqchk
  -silent -o C.jet_elements_executable C.jet_elements_executable_conf
  C.jet_elements_executable_current` with dependency chains at `fd4cb95e`
  (all 43 jet theorems and their executability instances): exit 0 (82 s).
- After the `sigTxInBounds`/`sigTxOutBounds` additions every Elements module
  was rebuilt again; `coqchk -silent -o` on the five executability modules
  (`jet_elements_executable{,_conf,_current,_lock,_count}`) with dependency
  chains at `6d556838` (all 50 jet theorems and their executability
  instances): exit 0 (84 s). This pass supersedes the earlier ones.
- `coqchk -silent -o` on the five executability modules and
  `C.jet_elements_runs_everywhere` with dependency chains at `1fe00a21`:
  exit 0 (80 s); `Print Assumptions` of the 30 `_runs_everywhere`
  theorems: the six inherited assumptions each.
- `Print Assumptions` rerun in full for the 30 theorems added on 2026-10-12:
  the same six assumptions each.

## SHA-unit jets of the Elements program

Seventeen further jets (the 14 SHA jets, `annex_hash`,
`build_tapleaf_simplicity`, `build_tapbranch`) are proved for `elements_ge`
in the derived tree `Coq/elements-sha/` (see its README for boundaries and
the receipt). They are not counted in the table above.

## Next (in rough order of reuse)

1. Remaining primitive jet: `output_null_datum` (script parsing). The two
   token-amount jets are in `Coq/forward/` (stack-allocated local in the
   static helper; eight assumptions instead of six, see `forward/README.md`;
   audit and coqchk by `build-elements-forward.sh --check`: 6 theorems
   within the eight inherited assumptions, coqchk exit 0, 96 s).
2. Program-specified jets: `total_fee`, `output_is_fee`, the four distance jets,
   `lbtc_asset`, issuance (`issuance`, `issuance_asset`, `issuance_token`,
   `issuance_entropy`, `calculate_*`), time locks, hash and sig-hash jets. These need the
   Simplicity programs of `Haskell/Core/Simplicity/Programs/Elements*.hs`
   ported and evaluated, as was done for Bitcoin's totals/time locks/hashes.
3. Source review of `jet_elements_prim.v` semantics clauses; a second gate
   for `primSem` would strengthen it.
4. (done) Executability/stability instances for the Elements relations.

## Taproot environment relations established by the real builder (2026-10-13)

- `Coq/C/jet_elements_tappath_nullable.v`: `elements_tappath_nullable_local_spec`,
  the `tappath` jet under `elements_tappath_env_rep_nullable` (path pointer
  required only for a non-empty path; `simplicity_elements_mallocTapEnv`
  stores `path = NULL` otherwise). `elements_tappath_env_rep_weaken`: the
  earlier relation implies it. Same six inherited assumptions.
- `Coq/elements-env/C/jet_elements_env_tapenv_relations.v`: for the block
  returned by the real `simplicity_elements_mallocTapEnv` (`tapenv_built`)
  and a logical taproot environment describing the bytes read
  (`el_tapenv_describes`): `el_ready_script_cmr`, `el_ready_internal_key`,
  `el_ready_tapleaf_version`, `el_ready_tappath` (every path length).

Receipt (`f8fa597c`): `bash Coq/audit-elements-env.sh` — generated ports current; no admissions; assumption audit passed: 8 reports within the six inherited assumptions (`eval_sha256_toMidstate`, `ctxo_hash`, `eval_mallocTapEnv`, `elements_tappath_nullable_local_spec`, `el_ready_script_cmr`, `el_ready_internal_key`, `el_ready_tapleaf_version`, `el_ready_tappath`); `coqchk` passed for `C.jet_elements_env_tapenv`, `C.jet_elements_env_tapenv_relations` (with `C.jet_elements_tappath_nullable`) and their dependencies; exit 0; 19 min.

## Elements environment unit: more of the real callers (2026-10-13)

The Elements environment unit (`Coq/C/jets_elements_env.v`) now also
contains `elements/txEnv.c`; `gen-elements-env-ports.py` additionally ports
the live-context toolkit (`…_ctxs*`, `…_tx_calls`) and the free functions.

- `jet_elements_env_free.v` (generated): `eval_freeTransaction`, `eval_freeTapEnv`.
- `jet_elements_env_txenv.v` (hand-written): `eval_build_txEnv` — the real
  `simplicity_elements_build_txEnv` stores both pointers, a copy of the
  genesis hash, the index and `sigAllHash` (`el_sigall_regs`: genesis hash
  twice, transaction hash, taproot environment hash, big-endian index).
- `jet_elements_env_txenv_relations.v`: `el_ready_genesis_block_hash`,
  `el_ready_current_index` from that result.

Also ported by the generator: `jet_elements_env_hashbuffer.v`
(`eval_hashBuffer`) and `jet_elements_env_bytestring.v`
(`hash_buffer_bytestring`, the `byteStringHash` equivalence).

### Helpers of `simplicity_elements_mallocTransaction` (hand-written)

Groundwork for the Elements transaction builder (`elements/env.c`):

- `jet_elements_env_readbe64.v`: `eval_sha_ReadBE64` (the call returns
  `c_be64` of the eight bytes) and `c_be64_value` (on byte values it is the
  arithmetic big-endian word).
- `jet_elements_env_copyrawamt.v`: `eval_copyRawAmt_null`,
  `eval_copyRawAmt_explicit`, `eval_copyRawAmt_confidential` — the three
  cases of `copyRawAmt`, through the anonymous union of `confAmount`
  (`envu_union_at`, `eval_envu_union_lvalue`).  `amt_parity` is the
  `ODD_Y`/`EVEN_Y` prefix.
- `jet_elements_env_copyrawconf.v`: `eval_copyRawConfidential_null`,
  `eval_copyRawConfidential_raw` — the compound literal is zero-filled in
  its stack block, the prefix (`conf_prefix`) stored, the structure copied
  to `*conf`, the midstate written and both stack blocks freed.
- `jet_elements_env_isfee.v`: `eval_isFee` — the short-circuit conjunction
  returns `is_fee`; a NULL asset or value (`raw_first`) is compared but
  never dereferenced.
- `jet_elements_env_countfee.v`: `eval_countFeeOutputs` — the loop returns
  `fee_count`, the number of fee outputs.

- `jet_elements_env_nulldata_count.v`: `eval_countNullDataCodes` — the
  script scan returns `nd_count`, a functional scanner over the script
  bytes (`nd_skip` decodes the push length, `nd_op` one operation,
  `nd_loop` the scan); every early `return 0` of the C code is a `None` of
  the scanner. `nd_count_bound`.
- `jet_elements_env_nulldata_total.v`: `eval_countTotalNullDataCodes` — the
  loop over the outputs returns `nd_total`, the size of the opcode
  allocation of the builder.

- `jet_elements_env_sumfees.v`: `eval_sumFees` (and `eval_sumFees_zero`)
  — the fee tally against the functional model `sf_step`/`sf_iter` on
  (array of output indices, fee of each output): the call returns the
  number of distinct assets, the front of the pointer array holds the first
  output of each bunch and its `assetFee` the sum of the explicit amounts
  of the bunch; everything outside the array and the `assetFee` fields is
  unchanged (`sf_frame`).  Premises: `memcmp_model`
  (`C/jet_memcmp_model.v`) for the external `memcmp`, and `Hsorted` — the
  array is sorted for the byte order of the asset midstates, the
  precondition the C code states and asserts (the failing branch of
  `simplicity_assert` is never taken).  Establishing `Hsorted` is the job
  of `simplicity_rsort`, not yet proven.

- `jet_elements_env_conf_hash.v`: `eval_sha256_confidential` —
  `simplicity_sha256_confidential` (`elements/ops.c`, shared with the
  Elements hash jets) on a live context of the `LS` layer absorbs
  `conf_bytes`: the prefix byte and, unless the value is NONE, its 32 data
  bytes (the `switch` with its `return`/`break` cases).
- `jet_elements_env_conf_wrap.v`: `eval_sha256_confAsset`,
  `eval_sha256_confNonce` (prefixes 0x0a/0x0b and 0x02/0x03).
- `jet_elements_env_conf_amt.v`: `eval_sha256_confAmt` — the context
  absorbs `amt_bytes` (0x01 and the big-endian explicit amount, or
  0x08/0x09 and the commitment); the prefix NONE, which the C code marks
  unreachable, is excluded by the premise.
- `jet_elements_env_calc.v`: `eval_calculateAsset` —
  `simplicity_calculateAsset` stores at the result pointer
  `calc_asset_regs ent`, the SHA-256 compression of `ent ++ 0^8` from the
  initial state (stack block zero-filled, `memcpy` of the entropy under
  `memcpy_model`, `sha256_iv`, compression through the dispatch pointer
  under `sha_dispatch_ok`, struct return through the hidden pointer).
  `calc_prefix_exec` and `calc_tail_exec` are shared with
  `simplicity_calculateToken`.
- `jet_elements_env_calc_token.v`: `eval_is_confidential` and
  `eval_calculateToken` — the result is `calc_token_regs ent pfx`, the
  compression of `ent ++ token_word pfx ++ 0^7` (0x02000000 for a
  confidential amount prefix, 0x01000000 otherwise).
- `jet_elements_env_le32_write.v` (`eval_WriteLE32`, `le32_byte_value`),
  `jet_elements_env_u32le_exec.v` (`eval_sha256_u32le`, derived from
  `C/jet_sha_u32be_exec.v` by renaming) and `jet_elements_env_ctxo_le.v`
  (`ctxo_u32le`, derived from `ctxo_u32be`): `sha256_u32le`, which the
  SHA unit does not contain, for `simplicity_generateIssuanceEntropy`.
- `jet_elements_env_ctxo_uchars.v`: `ctxo_uchars` — `sha256_uchars` on a
  single context of the `ctxo` layer absorbs a readable byte range (for
  `simplicity_generateIssuanceEntropy` and `parseNullData`).
- `jet_elements_env_entropy.v`: `eval_generateIssuanceEntropy` — the
  result pointer receives `entropy_regs txid ix con`, the compression from
  the initial state of `sha256(sha256(txid bytes ++ le32(ix)))` words
  followed by the contract hash (two local contexts through the `ctxo`
  layer, `memcpy` under `memcpy_model`, then the tail shared with
  `calculateAsset`).

- `jet_elements_env_uchars_null.v`: `eval_sha256_uchars_null` and
  `ctxo_uchars_null` — `sha256_uchars(ctx, NULL, 0)`, the case the accepted
  `eval_sha256_uchars` (non-null array) leaves out and that `hashBuffer`
  reaches for the zero `rawElementsBuffer` hashed in place of an absent
  proof.

- `jet_elements_env_hashbuffer_empty.v`: `eval_hashBuffer_empty` —
  `hashBuffer` on the zero buffer yields `hash_buffer_regs []` (the state
  of the empty string).

- `jet_elements_env_parse_{defs,mem,ops,hash,iter}.v` and
  `jet_elements_env_parse.v`: `eval_parseNullData` — `parseNullData`
  against the functional parser `pn_run alen len bs` (`pn_step`/`pn_loop`
  in `parse_iter.v`; an entry is `(code, optional pushed bytes)` with
  `pn_ent_at` giving the stored code and the SHA-256 words of the pushed
  data).  `None`: `result->op = NULL` and nothing outside the result
  structure and the opcode array changes.  `Some ents`: `result->op` is the
  caller's cursor, `result->len = length ents <= alen`, every entry is in
  the array, `*allocation` is advanced by `36 * length ents` and
  `*allocationLen` reduced by `length ents`.  Input requirements: the
  script bytes are readable, the opcode array of `*allocationLen` entries
  is writable, the result, the cursor cells, the script and the SHA
  globals are in blocks different from the array and from the result
  (facts about the caller's allocations), `memcpy_model`.  The three
  locals (compound literal, two SHA contexts) are allocated and freed in
  the proof.  `pn_iter` and `pn_loop_exec` are the per-iteration and loop
  statements.

The three issuance helpers of `elements/ops.c` are thereby proven as C
functions; relating `entropy_regs`, `calc_asset_regs` and `calc_token_regs`
to the Elements specification of issuance is not done here.

The bytes of a raw asset, nonce or amount and the readability of the raw
transaction are input requirements (what the caller of
`simplicity_elements_mallocTransaction` supplies); nothing about the built
transaction is assumed.

Receipt (`f07749da`): `bash Coq/audit-elements-env.sh` — generated ports
current; no admissions; assumption audit passed: 22 reports within the six
inherited assumptions (the 8 above, `eval_freeTransaction`,
`eval_freeTapEnv`, `eval_build_txEnv`, `el_ready_genesis_block_hash`,
`el_ready_current_index`, `eval_hashBuffer`, `hash_buffer_bytestring`,
`eval_sha_ReadBE64`, `c_be64_value`, the three `eval_copyRawAmt_*`, the two
`eval_copyRawConfidential_*`); `coqchk` passed for
`C.jet_elements_env_tapenv`, `C.jet_elements_env_tapenv_relations`,
`C.jet_elements_env_free`, `C.jet_elements_env_txenv_relations`,
`C.jet_elements_env_bytestring`, `C.jet_elements_env_copyrawconf` and their
dependencies; exit 0; 20 min.  (An earlier run at `4bf3bbdf` passed with 11
reports, exit 0, 31 min.)

Receipt (`29958320`): `bash Coq/audit-elements-env.sh` — 26 reports within
the six inherited assumptions (adds `eval_isFee`, `eval_countFeeOutputs`,
`eval_countNullDataCodes`, `eval_countTotalNullDataCodes`); `coqchk` passed
for the listed modules and their dependencies; exit 0; 17 min.

Receipt (`85765375`): `bash Coq/audit-elements-env.sh` — 32 reports within
the six inherited assumptions (adds `eval_sumFees`, `eval_sumFees_zero`,
`eval_sha256_confidential`, `eval_sha256_confAsset`,
`eval_sha256_confNonce`, `eval_sha256_confAmt`); `coqchk` passed for the
listed modules and their dependencies; exit 0; 17 min.

Receipt (`1f953251`): `bash Coq/audit-elements-env.sh` — 46 reports within
the six inherited assumptions (adds the issuance helpers, `ctxo_u32le`,
`ctxo_uchars`, the `uchars`/`hashBuffer` NULL cases, `pn_iter`,
`pn_loop_exec`, `eval_parseNullData`); `coqchk` passed for the listed
modules (now including `C.jet_elements_env_parse`) and their dependencies;
exit 0; 17 min.

Open for Elements: the rest of `simplicity_elements_mallocTransaction`
(`copyInput`, `copyOutput`, the external
`simplicity_rsort`, the main body) and
the links of the Elements cached hashes to specification values.
