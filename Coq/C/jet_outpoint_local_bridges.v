(** Original 36-byte local layout: frame copy, function entry and free-list adapters. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_partial.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_bitmachine_rep.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks C.jet_uint32_array_init.
Require Import C.jet_wide C.jet_wide_spec.
Require Import C.jet_write_sha256_context_layout.
Require Import C.jet_read_sha256_counter C.jet_read_sha256_overflow C.jet_sha256_counter_representation.
Require C.jets.
Require Import C.jets_elements C.jet_elements_support_sha_linkage C.jet_elements_support_sha_transport C.jet_elements_support_sha_compress_call C.jet_elements_support_sha_block_local.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_uchars_loop C.jet_elements_support_sha_uchars_exec.
Require Import C.jet_elements_support_sha_read_context_layout C.jet_elements_support_sha_ctx8_bridge.
Require Import C.jet_elements_support_sha_add_n_init C.jet_elements_support_sha_add_n_calls C.jet_elements_support_sha_add_n_exec.
Require Import C.jet_elements_support_sha_finalize_exec.
Require Import C.jet_elements_support_sha_tapdata_prep.
Require Import C.jet_elements_support_sha_uchar_exec C.jet_elements_support_sha_ctx_abs.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.


Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_nonce_context_spec C.jet_nonce_context_shape C.jet_nonce_exec_effects.
Local Opaque elements_ge.

Require Import C.jet_nonce_local_common C.jet_asset_local_buffer C.jet_asset_local_context_hashes.
Require Import C.jet_outpoint_exec_shape C.jet_outpoint_middle_common C.jet_outpoint_middle_middle C.jet_outpoint_local_spec C.jet_outpoint_local_counter.

Lemma op_source_copy m mc bl bm bb bx bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (op_env bl bm bb bx) le m (Sassign (Evar _src nc_fr) (Etempvar _src nc_fr)) E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)). rewrite HA; exact HS.
    + intros _. change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Lemma op_entry_sha env m m1 m2 m3 m4 bl bm bb bx bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) ->
  Mem.alloc m2 0 36 = (m3, bb) -> Mem.alloc m3 0 88 = (m4, bx) ->
  function_entry2 sha_ge f_simplicity_outpoint_hash
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (op_env bl bm bb bx) (op_temps env bd dbase bs sbase) m4.
Proof. rewrite elements_sha_genv. apply op_entry. Qed.
Lemma op_blocks_sha bl bm bb bx :
  blocks_of_env sha_ge (op_env bl bm bb bx) = [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bb, 0, 36)].
Proof. rewrite elements_sha_genv. apply op_blocks. Qed.
