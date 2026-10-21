(** Two actual coordinate arithmetic calls of the projective checker, retaining
    the full point allocation and a precise frame for its other coordinates. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp C.jet_secp_fe_math.
Require Import C.jet_secp_point_write_run C.jet_secp_point_write_preservation
  C.jet_secp_point_square_coordinate C.jet_secp_field_point_multiply C.jet_secp_curve_frame.
Require Import C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_mul_storage
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Lemma coordinate_frame_other k j w m mf bout bin :
  k<>j -> bout<>bin -> fe_at m bin (point_coordinate_offset j) (words5 w) ->
  lframe (point_square_coordinate_frame k bout bin) m mf ->
  fe_at mf bin (point_coordinate_offset j) (words5 w).
Proof.
  intros HCoords HBlocks HF HL.
  eapply curve_keep_field_range;[reflexivity|exact HF|exact HL|].
  intros pos HPos;unfold point_square_coordinate_frame;intros [[HE _]|[_ HP]].
  - congruence.
  - pose proof (point_coordinate_disjoint k j HCoords);lia.
Qed.

Lemma coordinate_frame_blocks k bout bin m mf :
  lframe (point_square_coordinate_frame k bout bin) m mf ->
  lframe (fun bx _ => bx<>bout /\ bx<>bin) m mf.
Proof.
  intro HL;eapply lframe_implies;[exact HL|].
  intros bx pos [HO HI] HV;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence.
Qed.

Theorem coordinate_square_cube_calls k rho m bout bin :
  square_input_bounds rho -> bout<>bin ->
  Mem.range_perm m bout 0 40 Cur Freeable ->
  fe_at m bin (point_coordinate_offset k) (words5 rho) -> Mem.range_perm m bin 0 128 Cur Freeable ->
  exists m1 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (point_coordinate_offset k))] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_mul)
    [Vptr bout Ptrofs.zero;Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (point_coordinate_offset k))] E0 mf Vundef /\
  fe_at mf bout 0 (words5 (point_mul_words (square_words rho) rho)) /\ Mem.range_perm mf bout 0 40 Cur Freeable /\
  fe_at mf bin (point_coordinate_offset k) (words5 rho) /\ Mem.range_perm mf bin 0 128 Cur Freeable /\
  radix_value (point_mul_words (square_words rho) rho) mod feP=
    (radix_value rho*radix_value rho*radix_value rho) mod feP /\
  square_input_bounds (point_mul_words (square_words rho) rho) /\
  (forall i, (i<5)%nat -> Int64.unsigned (point_mul_words (square_words rho) rho i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
  lframe (point_square_coordinate_frame k bout bin) m mf.
Proof.
  intros HB HNe HO HI HF.
  destruct (eval_point_square_coordinate k rho m bout bin HB HO HI HF HNe)
    as (m1 & C1 & O1 & OF1 & I1 & IF1 & V1 & B1 & BT1 & F1).
  destruct (eval_field_point_mul_numeric k (square_words rho) rho m1 bout bin B1 HB HNe O1 OF1 I1 IF1)
    as (mf & C2 & O2 & OF2 & I2 & IF2 & V2 & B2 & BT2 & F2).
  assert (HV : radix_value (point_mul_words (square_words rho) rho) mod feP=
    (radix_value rho*radix_value rho*radix_value rho) mod feP).
  { change (radix_value (square_words rho) mod feP=(radix_value rho*radix_value rho) mod feP) in V1.
    rewrite V2,Z.mul_mod by (unfold feP,feR;lia).
    rewrite V1,<- Z.mul_mod by (unfold feP,feR;lia);reflexivity. }
  exists m1,mf;split;[exact C1|]. split;[exact C2|]. split;[exact O2|]. split;[exact OF2|].
  split;[exact I2|]. split;[exact IF2|]. split;[exact HV|]. split;[exact B2|]. split;[exact BT2|].
  eapply lframe_trans;[exact F1|exact F2].
Qed.
