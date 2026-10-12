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

## Proved jets (20), each against `primitive Prim.X` as in `Haskell/Simplicity/Elements/Jets.hs`

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

## Receipts

- All 20 theorems: `Print Assumptions` = the six inherited assumptions
  (`sig_forall_dec`, `sig_not_dec`, `classic`, `functional_extensionality_dep`,
  `external_functions_sem`, `inline_assembly_sem`); no `admit`/`Admitted`/
  `Axiom`/`Parameter` in `jet_elements_*.v` (2026-10-12).
- `coqchk -silent -o` on the twelve theorem modules present at commit
  `0d5d45e3` (17 jets) and their dependency chains: exit 0 (69 s).
- Kernel check of `jet_elements_{tappath,annex,pegin}_local`: see the dated
  entry appended below when it completes.

## Next (in rough order of reuse)

1. Remaining primitive jets: `input_asset`, `input_amount`, `output_asset`,
   `output_amount`, `output_nonce` (confidential encodings: new payload
   shape), `reissuance_blinding`, `new_issuance_contract`,
   `reissuance_entropy`, `issuance_asset_amount`, `issuance_token_amount`
   (branch on issuance type), `output_null_datum`.
2. Program-specified jets (72): `current_*`, `num_inputs`, `num_outputs`,
   `total_fee`, issuance, time locks, hash and sig-hash jets. These need the
   Simplicity programs of `Haskell/Core/Simplicity/Programs/Elements*.hs`
   ported and evaluated, as was done for Bitcoin's totals/time locks/hashes.
3. Source review of `jet_elements_prim.v` semantics clauses; a second gate
   for `primSem` would strengthen it.
4. Executability/stability instances for the Elements relations (the generic
   theorems of `jet_frame_constructible_app.v` apply unchanged).
