(** Native save representation derived from successful original decompression. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_memcpy_model C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_b32_exec C.jet_secp_square_columns
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_point_write_field C.jet_secp_point_field_bridge C.jet_secp_write_fe_numeric
 C.jet_secp_write_fe_wide_exec C.jet_secp_field_negate_values C.jet_secp_field_negate_storage
 C.jet_secp_fe_inv_prefix C.jet_secp_affine_storage C.jet_secp_storage_numeric
 C.jet_secp_decompress_literal C.jet_secp_decompress_numeric C.jet_secp_decompress_output C.jet_secp_decompress_body
 C.jet_secp_root_chain_numeric C.jet_secp_root_check C.jet_secp_rescale_literal
 C.jet_secp_pubkey_save_function C.jet_secp_ge_storage_body C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_decompress.
Definition native_field_words f:=rho5 (pf0 f) (pf1 f) (pf2 f) (pf3 f) (pf4 f).
Lemma native_field_words_limbs f:words5 (native_field_words f)=point_field_limbs f.
Proof. reflexivity. Qed.
Lemma native_field_words_value f:fe_inv_value (native_field_words f)=@toZ (WordToZ 8) (point_field_output f).
Proof.
 unfold point_field_output;rewrite wide_fe_output_value;unfold fe_inv_value;rewrite radix_value_matches_normalizer;reflexivity.
Qed.
Lemma native_canonical_square_bounds value:0<=value<2^256 ->
 square_input_bounds (native_field_words (point_canonical_field value)).
Proof.
 intro V;pose proof (proj1 (fe_limbs_of_ok value V)) as (B0 & B1 & B2 & B3 & B4).
 intros i Bound;destruct i as [|[|[|[|[|i]]]]];try lia;
 cbn [native_field_words point_canonical_field pf0 pf1 pf2 pf3 pf4 rho5 List.nth Nat.eqb];
 rewrite limb_rho_unsigned by exact V;cbn [fe_limbs_of List.nth];lia.
Qed.
Lemma native_negative_square_bounds value:0<=value<2^256 ->
 square_input_bounds (native_field_words (point_negative_field value)).
Proof.
 intro V;pose proof (proj1 (point_reader_limb_model value V)) as (B0 & B1 & B2 & B3 & B4).
 intros i Bound;destruct i as [|[|[|[|[|i]]]]];try lia;
 cbn [native_field_words point_negative_field pf0 pf1 pf2 pf3 pf4 rho5 List.nth Nat.eqb];
 rewrite negate_value_unsigned by (try lia;cbn [Nat.eqb];lia);
 cbn [negate_mask];pose proof (Int64.unsigned_range (limb_rho value 0%nat));
 pose proof (Int64.unsigned_range (limb_rho value 1%nat));
 pose proof (Int64.unsigned_range (limb_rho value 2%nat));
 pose proof (Int64.unsigned_range (limb_rho value 3%nat));
 pose proof (Int64.unsigned_range (limb_rho value 4%nat));lia.
Qed.
Theorem eval_decompressed_native_save (Model:memcpy_model) w
 (pk:Ty.tySem (Word 8)) (odd:Ty.tySem Bit) (ax ay:Ty.tySem (Word 8)) m bin bout:
 root_words_match w pk ->@literal_decompress Simplicity.Alg.CoreFunSem (odd,pk)=inr (ax,ay) ->
 fe_at m bin 0 (words5 w) ->
 fe_at m bin 40 (point_field_limbs (decompress_y_field w (Bit.toBool odd))) ->
 Mem.range_perm m bout 0 64 Cur Freeable ->exists mf storage,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_xonly_pubkey_save)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf Vundef /\
 affine_storage_readable mf bout 0 storage /\
 field_storage_value storage=@toZ (WordToZ 8) ax /\
 field_storage_value (fun i=>storage (4+i)%nat)=@toZ (WordToZ 8) ay /\
 Mem.range_perm mf bout 0 64 Cur Freeable /\lframe (fun b _=>b<>bout) m mf /\readonly_preserved m mf.
Proof.
 intros Match Literal InputX InputY Free.
 pose proof (eq_trans (decompress_machine_matches_literal w pk odd Match) Literal) as Machine.
 assert (Root:root_check_flag (decompress_root_words w)=Datatypes.true).
 { unfold decompress_machine_result in Machine;destruct (root_check_flag (decompress_root_words w));[reflexivity|discriminate]. }
 assert (Coordinates:point_field_output (decompress_input_field w)=ax /\
  point_field_output (decompress_y_field w (Bit.toBool odd))=ay).
 { unfold decompress_machine_result in Machine;rewrite Root in Machine;inversion Machine;auto. }
 destruct Coordinates as [X Y].
 set (wy:=native_field_words (decompress_y_field w (Bit.toBool odd))).
 assert (BoundsY:square_input_bounds wy).
 { unfold wy,decompress_y_field;rewrite Root;unfold decompress_parity_field.
   destruct (xorb (Z.testbit (decompress_body_value w) 0) (Bit.toBool odd));
   [apply native_negative_square_bounds|apply native_canonical_square_bounds];
   unfold decompress_body_value;apply field_mod_256_range. }
 rewrite <-native_field_words_limbs in InputY;fold wy in InputY.
 destruct (eval_xonly_pubkey_save Model w wy m bin bout (proj1 Match) BoundsY InputX InputY Free)
 as (mf & Save & Storage & FreeF & Frame & Read).
 exists mf,(ge_storage_words w wy);split;[exact Save|];split;[exact Storage|].
 destruct (ge_storage_words_values w wy) as [VX VY].
 split.
 - rewrite VX,<-X;change (fe_inv_value (native_field_words (decompress_input_field w))=
    @toZ (WordToZ 8) (point_field_output (decompress_input_field w))).
   apply native_field_words_value.
 - split.
   + rewrite VY;unfold wy;rewrite native_field_words_value,Y;reflexivity.
   + split;[exact FreeF|];split;assumption.
Qed.
