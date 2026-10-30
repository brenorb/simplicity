(** Run the original verifier from the original x-only parser result. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import
 C.jet_readBit_layout C.jet_sx_mem C.jet_clight_forward
 C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_rescale_literal C.jet_secp_odd_table_literal_walk
 C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_generator_globals C.jet_secp_split_constants C.jet_secp_beta_global
 C.jet_secp_ecmult_general C.jet_secp_table_affine_nonzero C.jet_secp_curve_literal
 C.jet_secp_literal_add_program C.jet_secp_strauss_complete_program C.jet_secp_literal_gej_predicate
 C.jet_secp_even_x_test C.jet_secp_modinfo_fe_caller C.jet_ctz_model
 C.jet_memset_model C.jet_secp_root_chain_owned C.jet_secp_schnorr_after_mult
 C.jet_secp_scalar_table_literal C.jet_secp_canonical_zero C.jet_secp_field_read_preservation
 C.jet_secp_modinfo_fe_transport C.jet_secp_schnorr_mult_return C.jet_secp_literal_add_numeric
 C.jet_secp_generator_pair_general C.jet_secp_scalar_add_reader_support C.jet_clight_internal_frame
 C.jet_secp_gej_set_ge_owned C.jet_secp_closed_helpers C.jet_clight_internal_preserve
 C.jet_secp_generator_main C.jet_secp_point_set_bit C.jet_secp_beta_state.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_off_curve_linear_combination_1 literal_gej_is_infinity
 rescale_field_output literal_scalar_table5 canonical_fe_is_zero.
Require Import C.jet_secp_schnorr_gej_mult_return C.jet_secp_scalar_negate_canonical
 C.jet_secp_scalar_writer_storage C.jet_secp_scalar_writer_run C.jet_secp_scalar_reader_lifecycle
 C.jet_secp_scalar_negate_writer_identity C.jet_secp_canonical_scalar_negate
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_limb_bridge C.jet_toZ
 C.jet_word_repr C.jet_secp_scalar_read_write C.jet_sx_state C.jet_sx_rep.
Require Import C.jet_secp_schnorr_negate_return C.jet_secp_schnorr_challenge_literal
 C.jet_secp_schnorr_challenge_hash C.jet_secp_schnorr_challenge_absorb
 C.jet_secp_sha_startup C.jet_memcpy_model C.jet_secp_point_verify_literal
 C.jet_secp_schnorr_group_predicate.
Require Import C.jet_secp_schnorr_challenge_return C.jet_secp_schnorr_check_predicate
 C.jet_secp_schnorr_verify_literal C.jet_secp_decompress_literal C.jet_secp_canonical_normalize
 C.jet_secp_affine_word_valid.
Require Import C.jet_secp_schnorr_checked_return C.jet_secp_b32_owned C.jet_secp_b32_exec
 C.jet_secp_multiply_input_input C.jet_secp_even_decompress.
Require Import C.jet_secp_word_bytes_codec.
Require Import C.jet_secp_schnorr_serialize_return C.jet_secp_pubkey_load_coordinates
 C.jet_secp_affine_storage C.jet_secp_storage_numeric.
Require Import C.jet_secp_statement_prefix C.jet_read8s_layout C.jet_secp_schnorr_signature_read C.jet_secp_schnorr_r_read C.jet_secp_schnorr_scalar_read C.jet_secp_xonly_parse_field C.jet_secp_schnorr_keyload_return C.jet_secp_table_decode C.jet_clight_internal_permissions.
Require Import C.jet_secp_schnorr_signature_return C.jet_secp_schnorr_signature_guards C.jet_secp_set_b32_owned_frame C.jet_secp_scalar_set_flag.
Require Import C.jet_secp_schnorr_verify_entry C.jet_secp_schnorr_verify_checks C.jet_secp_schnorr_signature_ranges C.jet_secp_xonly_parse_control.
Require Import C.jet_secp_schnorr_verify_function C.jet_secp_xonly_parse_result C.jet_secp_xonly_parse_control.
Lemma xonly_parsed_result_framed (pk:Ty.tySem (Word 8)) m mf bkey P:
 xonly_parsed_result pk m bkey ->lframe P m mf ->(forall pos,P bkey pos) ->
 xonly_parsed_result pk mf bkey.
Proof.
 intros Parsed Frame Outside Bound ax ay Decode;destruct (Parsed Bound ax ay Decode) as (w & Storage & X & Y).
 exists w;split;[|split;assumption];eapply affine_storage_readable_lframe;[exact Storage|exact Frame|exact Outside].
Qed.
Theorem eval_schnorrsig_verify_parsed (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk msg r s:Ty.tySem (Word 8)) m bsig bmsg bkey:
 bsig<>bmsg ->bsig<>bkey ->Mem.range_perm m bsig 0 64 Cur Freeable ->
 uint8_array_at m bsig 0 (map Int.repr (xonly_input_bytes r)) ->
 uint8_array_at m bsig 32 (map Int.repr (xonly_input_bytes s)) ->
 schnorr_bytes_at m bmsg Ptrofs.zero (schnorr_word_bytes msg) ->
 xonly_parse_result pk=Int.one ->xonly_parsed_result pk m bkey ->
 secp_sha_startup m ->(forall h,generator_table_state h m) ->split_constants_ready m ->beta_initialized m ->modinfo_fe_state m ->
 exists mf,Clight2.eval_funcall secp_ge m (Internal f_secp256k1_schnorrsig_verify)
 [Vptr bsig Ptrofs.zero;Vptr bmsg Ptrofs.zero;Vlong (Int64.repr 32);Vptr bkey Ptrofs.zero] E0 mf
 (Vint (bit_int (Simplicity.Bit.toBool (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))))) /\
 Mem.range_perm mf bsig 0 64 Cur Freeable /\lframe (fun b _=>b<>bsig) m mf /\mem_forward m mf.
Proof.
 intros SigMsg SigKey SigFree RInput SInput MsgBytes Success Parsed Startup Tables Split Beta Ready.
 destruct (proj1 (xonly_parse_success_iff pk) Success) as (Bound & ax & ay & Decode).
 destruct (Parsed Bound ax ay Decode) as (w & KeyInput & KeyX & KeyY).
 destruct (secp_even_decompress_properties pk ax ay Decode) as (AX & _).
 assert (XValue:@toZ (WordToZ 8) ax=@toZ (WordToZ 8) pk).
 { rewrite AX,canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model;apply Z.mod_small.
   split;[exact (proj1 (word_toZ_range 8 pk))|exact Bound]. }
 rewrite XValue in KeyX.
 exact (eval_schnorrsig_verify_owned Copy Clear Count pk msg r s ax ay w m bsig bmsg bkey
  SigMsg SigKey SigFree RInput SInput MsgBytes KeyInput KeyX KeyY Bound Decode Startup Tables Split Beta Ready).
Qed.
