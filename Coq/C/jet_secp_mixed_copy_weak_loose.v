(** Original mixed-addition copy/weak-normalization on loose input limbs.
    The changed temporary is retained, and the original point is preserved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_double_statements C.jet_secp_mixed_finite_start
 C.jet_secp_field_copy_owned C.jet_secp_field_weak_loose C.jet_secp_field_mul_small
 C.jet_secp_mixed_copy_weak C.jet_secp_curve_frame C.jet_secp_field_read_preservation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge weak_loose_words.

Theorem exec_mixed_copy_weak_loose e le m ba bu (y : bool) w :
 le!_a=Some (Vptr ba Ptrofs.zero) -> e!(if y then _s1 else _u1)=Some (bu,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> ba<>bu ->
 (forall i,(i<5)%nat -> Int64.unsigned (w i)<=2^60) ->
 fe_at m ba (if y then 40 else 0) (words5 w) ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable -> exists mc mf,
 Clight2.exec_stmt secp_ge e le m (mixed_copy_coordinate y) E0 le mc Out_normal /\
 Clight2.exec_stmt secp_ge e le mc (mixed_weak_coordinate y) E0 le mf Out_normal /\
 fe_at mf bu 0 (words5 (weak_loose_words w)) /\ Mem.range_perm mf bu 0 40 Cur Freeable /\
 fe_at mf ba (if y then 40 else 0) (words5 w) /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 radix_value (weak_loose_words w) mod feP=radix_value w mod feP /\
 mul_small_input_bounds (weak_loose_words w) /\ lframe (fun b _=>b<>bu) m mf.
Proof.
 intros HA HU HE Sep Bound Field PFree TFree.
 destruct (exec_field_copy_owned e le m
  (double_point_field _a (if y then _y else _x) curve_fe_type)
  (Evar (if y then _s1 else _u1) curve_fe_type)
  ba (if y then 40 else 0) bu 0 w eq_refl eq_refl
  ltac:(eapply eval_Elvalue;[apply eval_mixed_a_copy_field;exact HA|apply deref_loc_copy;reflexivity])
  ltac:(apply eval_Evar_local;exact HU) Sep Field ltac:(lia) ltac:(exists 0;reflexivity)
  ltac:(change (40<=18446744073709551615);lia) TFree) as (mc & Copy & Copied & Perms & FrameC).
 assert (FreeC : Mem.range_perm mc bu 0 40 Cur Freeable).
 { intros pos HP;apply (proj2 (Perms bu pos Cur Freeable));apply TFree;exact HP. }
 destruct (eval_field_weak_loose w mc bu Bound Copied FreeC)
  as (mf & Weak & Result & FreeF & Value & Tight & FrameW).
 assert (Frame : lframe (fun b _=>b<>bu) m mf).
 { eapply lframe_trans;[|exact FrameW].
   eapply lframe_implies;[exact FrameC|];intros b pos HN HV;left;exact HN. }
 exists mc,mf;split;[exact Copy|];split.
 - unfold mixed_weak_coordinate;eapply exec_curve_call with (vargs:=[Vptr bu Ptrofs.zero]) (v:=Vundef).
   + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   + exact HE.
   + eapply eval_Econs;[apply eval_curve_local;exact HU|reflexivity|constructor].
   + exact Weak.
 - split;[exact Result|];split;[exact FreeF|];split.
   + eapply field_at_lframe;[exact Field|exact Frame|];intros;exact Sep.
   + split;[eapply curve_keep_free;[lia|exact PFree|exact Frame|intros;exact Sep]|].
     split;[exact Value|];split;assumption.
Qed.
