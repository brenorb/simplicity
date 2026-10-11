(** The environment-reading hash jets over the startup invariant: the accepted
    application contracts (same function, logical environment, representation
    relation, footprint and canonical specification) with [sha_startup_state]
    carried from the initial to the final memory. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_application_sep.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_output_layout_step C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_wide C.jet_complement_wide_layout.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep.
Require Import C.jet_sha_uchars_exec C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_ctx8_finalize_jet.
Require Import C.jet_sha_tapdata_prep C.jet_sha_tapdata_jet.
Require Import C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_tagged_ctx C.jet_sha_hash_io.
Require Import C.jet_bitcoin_make_tapleaf_exec.
Require Import C.jet_bitcoin_effects C.jet_bitcoin_env_load.
Require Import C.jet_sha_indexed_exec C.jet_sha_index_eval C.jet_sha_steps.
Require Import C.jet_forWhile_seq C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_vh_hash_prep.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_vh_hash_prep C.jet_bitcoin_output_hash_jet.
Require Import C.jet_bitcoin_input_utxo_hash_jet.
Require Import C.jet_sha_u32be_exec C.jet_sha_ctxi_u32 C.jet_bitcoin_ctx_hash_spec C.jet_bitcoin_tx_hash.
Require Import C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_input_hash_spec.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_word32_chunks C.jet_readBit_layout.
Require Import C.jet_bitcoin_output_hash_jet C.jet_bitcoin_input_utxo_hash_jet C.jet_bitcoin_input_hash_jet.
Require Import JetStartup.jet_sha_startup_state.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Theorem bitcoin_output_hash_startup_spec : memcpy_model ->
  sha_startup_application_spec f_simplicity_bitcoin_output_hash ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) output_hash_rep
    (fun a e => @vh_hash_spec (BitcoinFull.Base Bitcoin.OutputValue)
      (BitcoinFull.Base Bitcoin.OutputScriptHash) fullalg a e).
Proof.
  intros Hmodel. apply sha_startup_application_from_sep; [vm_compute; reflexivity|exact (bitcoin_output_hash_local_spec Hmodel)].
Qed.

Theorem bitcoin_input_utxo_hash_startup_spec : memcpy_model ->
  sha_startup_application_spec f_simplicity_bitcoin_input_utxo_hash ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) input_utxo_hash_rep
    (fun a e => @vh_hash_spec (BitcoinFull.Base Bitcoin.InputValue)
      (BitcoinFull.Ext BitcoinExt.InputScriptHash) fullalg a e).
Proof.
  intros Hmodel. apply sha_startup_application_from_sep; [vm_compute; reflexivity|exact (bitcoin_input_utxo_hash_local_spec Hmodel)].
Qed.

Theorem bitcoin_input_hash_startup_spec : memcpy_model ->
  sha_startup_application_spec f_simplicity_bitcoin_input_hash ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) input_hash_rep
    (fun a e => @input_hash_spec fullalg a e).
Proof.
  intros Hmodel. apply sha_startup_application_from_sep; [vm_compute; reflexivity|exact (bitcoin_input_hash_local_spec Hmodel)].
Qed.
