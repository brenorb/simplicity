(** Original az/z12 assignment execution, with the actual operand order.
    Prefix support only: flags, later arithmetic and the complete function
    call remain separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_statements C.jet_secp_double_statements
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_square_columns C.jet_secp_field_mul_small.
Require Import C.jet_secp_zinv_z_product.
Require Import C.jet_secp_square_point_x C.jet_secp_square_execution C.jet_secp_square_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition zinv_az_statement := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address _az;double_point_address _a _z;Etempvar _bzinv (tptr curve_fe_type)].
Definition zinv_finite_suffix := match fn_body f_secp256k1_gej_add_zinv_var with
 | Ssequence _ (Ssequence _ rest)=>rest | _=>Sskip end.
Definition zinv_after_az := match zinv_finite_suffix with Ssequence _ rest=>rest | _=>Sskip end.
Lemma zinv_az_source : zinv_finite_suffix=Ssequence zinv_az_statement zinv_after_az.
Proof. reflexivity. Qed.

Definition zinv_z12_statement := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [curve_local_address _z12;curve_local_address _az].
Definition zinv_after_z12 := match zinv_after_az with Ssequence _ rest=>rest | _=>Sskip end.
Lemma zinv_z12_source : zinv_after_az=Ssequence zinv_z12_statement zinv_after_z12.
Proof. reflexivity. Qed.

Theorem exec_zinv_z12_from_owned w e le m bo bi :
 e!_z12=Some (bo,curve_fe_type) -> e!_az=Some (bi,curve_fe_type) -> e!_secp256k1_fe_sqr=None ->
 square_input_bounds w -> Mem.range_perm m bo 0 40 Cur Freeable ->
 fe_at m bi 0 (words5 w) -> Mem.range_perm m bi 0 40 Cur Freeable -> bo<>bi -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_z12_statement E0 le mf Out_normal /\
 fe_at mf bo 0 (words5 (square_words w)) /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
 fe_at mf bi 0 (words5 w) /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 lframe (square_two_ranges bo bi) m mf.
Proof.
 intros EO EI ES Bounds Owned W Input Separate.
 destruct (eval_square_separate_precise w m bo bi Bounds Owned W Input Separate) as (mf & Call & Rest).
 exists mf;split;[|exact Rest].
 unfold zinv_z12_statement;eapply exec_curve_call with
   (vargs:=[Vptr bo Ptrofs.zero;Vptr bi Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - exact ES.
 - eapply eval_Econs;[apply eval_curve_local;exact EO|reflexivity|].
   eapply eval_Econs;[apply eval_curve_local;exact EI|reflexivity|constructor].
 - exact Call.
Qed.

Theorem exec_zinv_az_from_owned a b e le m bo ba bb :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_bzinv=Some (Vptr bb Ptrofs.zero) ->
 e!_az=Some (bo,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
 square_input_bounds a -> square_input_bounds b -> bo<>ba -> bo<>bb -> ba<>bb ->
 Mem.range_perm m bo 0 40 Cur Freeable -> fe_at m ba 80 (words5 a) -> Mem.range_perm m ba 0 128 Cur Freeable ->
 fe_at m bb 0 (words5 b) -> Mem.range_perm m bb 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_az_statement E0 le mf Out_normal /\
 fe_at mf bo 0 (words5 (point_mul_words a b)) /\ fe_at mf ba 80 (words5 a) /\ fe_at mf bb 0 (words5 b) /\
 Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
 mul_small_input_bounds (point_mul_words a b) /\
 lframe (fun bx pos=>bx<>bo /\ (bx<>ba \/ pos<80 \/ 120<=pos) /\ bx<>bb) m mf.
Proof.
 intros HA HB EO EM BA BB SepA SepB Separate Owned A AOwned B BOwned.
 destruct (eval_zinv_z_product_owned a b m bo ba bb BA BB SepA SepB Separate Owned A AOwned B BOwned)
   as (mf & Call & Rest).
 exists mf;split;[|exact Rest].
 unfold zinv_az_statement;eapply exec_curve_call with
   (vargs:=[Vptr bo Ptrofs.zero;Vptr ba (Ptrofs.repr 80);Vptr bb Ptrofs.zero]) (v:=Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - exact EM.
 - eapply eval_Econs;[apply eval_curve_local;exact EO|reflexivity|].
   eapply eval_Econs;[apply eval_double_point_address;[right;right;left;reflexivity|exact HA]|reflexivity|].
   eapply eval_Econs;[apply eval_Etempvar;exact HB|reflexivity|constructor].
 - exact Call.
Qed.
