(** Fresh private products from a projective X/Y coordinate. Retain the full
    128-byte owner using the existing affine-coordinate product proof's frame. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_square C.jet_secp_point_mul_storage C.jet_secp_mixed_affine_product
 C.jet_secp_curve_statements C.jet_secp_double_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Theorem eval_gej_fresh_product y a b m bo bp bf :
 square_input_bounds a -> square_input_bounds b -> bo<>bp -> bo<>bf -> bp<>bf ->
 Mem.range_perm m bo 0 40 Cur Freeable ->
 fe_at m bp (curve_square_offset y) (words5 a) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 fe_at m bf 0 (words5 b) -> Mem.range_perm m bf 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
  [Vptr bo Ptrofs.zero;Vptr bp (Ptrofs.repr (curve_square_offset y));Vptr bf Ptrofs.zero] E0 mf Vundef /\
 fe_at mf bo 0 (words5 (point_mul_words a b)) /\ fe_at mf bp (curve_square_offset y) (words5 a) /\
 fe_at mf bf 0 (words5 b) /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bf 0 40 Cur Freeable /\
 radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
 square_input_bounds (point_mul_words a b) /\
 lframe (fun bx pos=>bx<>bo /\ bx<>bf /\ (bx<>bp \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos)) m mf.
Proof.
 intros BA BB OP OF PF FreeO A FreeP B FreeF.
 assert (Free88 : Mem.range_perm m bp 0 88 Cur Freeable) by (intros pos Pos;apply FreeP;lia).
 destruct (eval_mixed_affine_product y a b m bo bp bf BA BB OP OF PF FreeO A Free88 B FreeF)
   as (mf & Call & Out & AP & BF & FOF & FP88 & FFF & Value & Bounds & Frame).
 assert (FPF : Mem.range_perm mf bp 0 128 Cur Freeable).
 { intros pos Pos;destruct (Z_lt_ge_dec pos 88).
   - apply FP88;lia.
   - apply (proj1 (proj2 Frame)).
     * eapply Mem.perm_valid_block;apply (FreeP 0);lia.
     * split;[congruence|];split;[exact PF|right;right;destruct y;cbn [curve_square_offset];lia].
     * apply FreeP;exact Pos. }
 exists mf;split;[exact Call|];split;[exact Out|];split;[exact AP|];split;[exact BF|];
   split;[exact FOF|];split;[exact FPF|];split;[exact FFF|];split;[exact Value|];split;assumption.
Qed.

Definition gej_fresh_product_stmt (y : bool) dst point factor :=
 curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address dst;double_point_address point (if y then _y else _x);curve_local_address factor].

Theorem exec_gej_fresh_product y dst point factor a b e le m bo bp bf :
 e!dst=Some (bo,curve_fe_type) -> le!point=Some (Vptr bp Ptrofs.zero) ->
 e!factor=Some (bf,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
 square_input_bounds a -> square_input_bounds b -> bo<>bp -> bo<>bf -> bp<>bf ->
 Mem.range_perm m bo 0 40 Cur Freeable ->
 fe_at m bp (curve_square_offset y) (words5 a) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 fe_at m bf 0 (words5 b) -> Mem.range_perm m bf 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (gej_fresh_product_stmt y dst point factor) E0 le mf Out_normal /\
 fe_at mf bo 0 (words5 (point_mul_words a b)) /\ fe_at mf bp (curve_square_offset y) (words5 a) /\
 fe_at mf bf 0 (words5 b) /\ Mem.range_perm mf bo 0 40 Cur Freeable /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bf 0 40 Cur Freeable /\
 radix_value (point_mul_words a b) mod feP=(radix_value a*radix_value b) mod feP /\
 square_input_bounds (point_mul_words a b) /\
 lframe (fun bx pos=>bx<>bo /\ bx<>bf /\ (bx<>bp \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos)) m mf.
Proof.
 intros Dest Point Factor Global BA BB OP OF PF FreeO A FreeP B FreeF.
 destruct (eval_gej_fresh_product y a b m bo bp bf BA BB OP OF PF FreeO A FreeP B FreeF)
   as (mf & Call & Out & AP & BF & FOF & FPF & FFF & Value & Bounds & Frame).
 exists mf;split.
 - unfold gej_fresh_product_stmt;eapply exec_curve_call with
    (vargs:=[Vptr bo Ptrofs.zero;Vptr bp (Ptrofs.repr (curve_square_offset y));Vptr bf Ptrofs.zero]) (v:=Vundef).
   + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   + exact Global.
   + eapply eval_Econs;[apply eval_curve_local;exact Dest|reflexivity|].
     eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr (curve_square_offset y))).
     * apply eval_double_point_address;[destruct y;cbn [curve_square_offset In];tauto|exact Point].
     * reflexivity.
     * eapply eval_Econs;[apply eval_curve_local;exact Factor|reflexivity|constructor].
   + exact Call.
 - split;[exact Out|];split;[exact AP|];split;[exact BF|];split;[exact FOF|];
   split;[exact FPF|];split;[exact FFF|];split;[exact Value|];split;assumption.
Qed.
