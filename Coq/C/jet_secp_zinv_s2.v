(** Original final S2 multiplication by the local az field, not point Z. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_field_pair_multiply
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_curve_statements
 C.jet_secp_zinv_shared_preparation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge field_pair_product.

Definition zinv_s2_az_statement := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address _s2;curve_local_address _s2;curve_local_address _az].
Definition zinv_after_s2_az := zinv_statement_drop 1 zinv_after_shared_preparation.
Lemma zinv_s2_az_source : zinv_after_shared_preparation=Ssequence zinv_s2_az_statement zinv_after_s2_az.
Proof. reflexivity. Qed.

Theorem exec_zinv_s2_az_from_owned a z e le m bs bz :
 e!_s2=Some (bs,curve_fe_type) -> e!_az=Some (bz,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
 square_input_bounds a -> square_input_bounds z -> bs<>bz ->
 fe_at m bs 0 (words5 a) -> fe_at m bz 0 (words5 z) ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_s2_az_statement E0 le mf Out_normal /\
 fe_at mf bs 0 (words5 (field_pair_product a z)) /\ fe_at mf bz 0 (words5 z) /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
 radix_value (field_pair_product a z) mod feP=(radix_value a*radix_value z) mod feP /\
 mul_small_input_bounds (field_pair_product a z) /\ lframe (fun bx _=>bx<>bs /\ bx<>bz) m mf.
Proof.
 intros ES EZ EM BA BZ Separate A Z SF ZF.
 destruct (eval_field_pair_multiply a z m bs bz BA BZ Separate A Z SF ZF)
   as (mf & Call & SOut & ZOut & SFree & ZFree & Value & Bound & Tight & Frame).
 exists mf;split.
 - unfold zinv_s2_az_statement;eapply exec_curve_call with
   (vargs:=[Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero;Vptr bz Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat (first [left;reflexivity|right]).
   + exact EM.
   + eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact EZ|reflexivity|constructor].
   + exact Call.
 - split;[exact SOut|];split;[exact ZOut|];split;[exact SFree|];split;[exact ZFree|];
   split;[exact Value|];split;[intros i Index;exact (proj2 (Tight i Index))|exact Frame].
Qed.
