(** Reuse the original square/multiply helpers for the two factor layouts
    encountered by table construction: a private field or a point's Z field.
    The supplied factor is arbitrary, including zero. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_square_columns
 C.jet_secp_point_square_coordinate C.jet_secp_gej_curve_coordinate C.jet_secp_point_write_run
 C.jet_secp_square_separate_caller C.jet_secp_square_numeric C.jet_secp_curve_frame
 C.jet_secp_gej_z_product C.jet_secp_field_product_owned C.jet_secp_point_mul_storage
 C.jet_secp_field_sum_bounds C.jet_secp_multiply_normalize_bridge.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ge_zinv_factor_offset (point:bool) : Z := if point then 80 else 0.
Definition ge_zinv_factor_size (point:bool) : Z := if point then 128 else 40.

Theorem eval_ge_zinv_factor_square point zi m bo bf :
 square_input_bounds zi -> bo<>bf -> Mem.range_perm m bo 0 40 Cur Freeable ->
 fe_at m bf (ge_zinv_factor_offset point) (words5 zi) ->
 Mem.range_perm m bf 0 (ge_zinv_factor_size point) Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
  [Vptr bo Ptrofs.zero;Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point))] E0 mf Vundef /\
 fe_at mf bo 0 (words5 (square_words zi)) /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
 fe_at mf bf (ge_zinv_factor_offset point) (words5 zi) /\
 Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable /\
 square_input_bounds (square_words zi) /\ lframe (fun b _=>b<>bo /\ b<>bf) m mf.
Proof.
 intros Bound Separate FreeO Factor FreeF;destruct point;cbn [ge_zinv_factor_offset ge_zinv_factor_size] in *.
 - destruct (eval_point_square_coordinate PointZ zi m bo bf Bound FreeO Factor FreeF Separate)
    as (mf & Call & Out & OF & FF & FP & Value & Bounds & Tight & Frame).
   exists mf;split;[exact Call|];split;[exact Out|];split;[exact OF|];
    split;[exact FF|];split;[exact FP|];split;[exact Bounds|].
   exact (coordinate_frame_blocks PointZ bo bf m mf Frame).
 - destruct (eval_square_separate_from_storage zi m bo bf Bound FreeO Factor FreeF Separate)
    as (mf & Call & Out & OF & FF & FP & Value & Bounds & Frame).
   exists mf;split;[exact Call|];split;[exact Out|];split;[exact OF|];
    split;[exact FF|];split;[exact FP|];split;assumption.
Qed.

Theorem eval_ge_zinv_factor_cube point a zi m bo ba bf :
 square_input_bounds a -> square_input_bounds zi -> bo<>ba -> bo<>bf -> ba<>bf ->
 Mem.range_perm m bo 0 40 Cur Freeable ->
 fe_at m ba 0 (words5 a) -> Mem.range_perm m ba 0 40 Cur Freeable ->
 fe_at m bf (ge_zinv_factor_offset point) (words5 zi) ->
 Mem.range_perm m bf 0 (ge_zinv_factor_size point) Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr bo Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bf (Ptrofs.repr (ge_zinv_factor_offset point))] E0 mf Vundef /\
 fe_at mf bo 0 (words5 (point_mul_words a zi)) /\
 fe_at mf ba 0 (words5 a) /\ fe_at mf bf (ge_zinv_factor_offset point) (words5 zi) /\
 Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf ba 0 40 Cur Freeable /\
 Mem.range_perm mf bf 0 (ge_zinv_factor_size point) Cur Freeable /\
 square_input_bounds (point_mul_words a zi) /\ lframe (fun b _=>b<>bo /\ b<>ba /\ b<>bf) m mf.
Proof.
 intros BA BZI OA OF AF FreeO A FreeA Factor FreeF;destruct point;cbn [ge_zinv_factor_offset ge_zinv_factor_size] in *.
 - destruct (eval_gej_z_product_owned a zi m bo ba bf BA BZI OA OF AF FreeO A FreeA Factor FreeF)
    as (mf & Call & Out & AP & FF & OP & AFP & FFP & Value & Bounds & Frame).
   exists mf;split;[exact Call|];split;[exact Out|];split;[exact AP|];split;[exact FF|];
    split;[exact OP|];split;[exact AFP|];split;[exact FFP|];split.
   + exact (field_scaled_loose 1 _ ltac:(lia) (field_tight_scaled _ Bounds)).
   + eapply lframe_implies;[exact Frame|];intros b pos (NO & NA & NF) Valid;repeat split;try assumption;left;exact NF.
 - destruct (eval_field_product_owned a zi m bo ba bf BA BZI OA OF AF FreeO A FreeA Factor FreeF)
    as (mf & Call & Out & AP & FF & OP & AFP & FFP & Value & Bounds & Frame).
   exists mf;split;[exact Call|];split;[exact Out|];split;[exact AP|];split;[exact FF|];
    split;[exact OP|];split;[exact AFP|];split;[exact FFP|];split.
   + exact (field_scaled_loose 1 _ ltac:(lia) (field_tight_scaled _ Bounds)).
   + exact Frame.
Qed.
