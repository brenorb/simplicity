(** Original in-place affine negation on loose limbs, including decompressor
    outputs. Weak normalization and negation are executed, not assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_field_weak_loose
 C.jet_secp_field_negate_separate C.jet_secp_field_slice_weak C.jet_clight_internal_permissions
 C.jet_secp_affine_self_copy C.jet_secp_affine_y_tail C.jet_secp_affine_negate_call
 C.jet_secp_affine_negate_words.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge weak_loose_words.

Theorem eval_affine_negate_loose_point y m b xlimbs flag :
 (forall i,(i<5)%nat -> Int64.unsigned (y i)<=2^60) -> length xlimbs=5%nat ->
 fe_at m b 0 xlimbs -> fe_at m b 40 (words5 y) ->
 Mem.range_perm m b 0 88 Cur Freeable -> Mem.load Mint32 m b 80=Some (Vint flag) ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_neg)
  [Vptr b Ptrofs.zero;Vptr b Ptrofs.zero] E0 mf Vundef /\
 fe_at mf b 0 xlimbs /\ fe_at mf b 40 (words5 (negate_sep_words (weak_loose_words y))) /\
 Mem.range_perm mf b 0 88 Cur Freeable /\ Mem.load Mint32 mf b 80=Some (Vint flag) /\
 radix_value (negate_sep_words (weak_loose_words y)) mod feP=(-radix_value y) mod feP /\
 square_input_bounds (negate_sep_words (weak_loose_words y)) /\ lframe (fun bx _=>bx<>b) m mf.
Proof.
 intros Bound Length X Y Free Flag.
 pose (le:=affine_negate_helper_temps b).
 destruct (exec_affine_negate_self_copy_owned le m b eq_refl eq_refl Free)
  as (mc & Copy & Unchanged & FreeC).
 assert (FrameC:lframe (fun _ _=>True) m mc) by (apply lframe_unchanged;exact Unchanged).
 assert (XC:fe_at mc b 0 xlimbs) by (eapply field_at_lframe;[exact X|exact FrameC|intros;exact I]).
 assert (YC:fe_at mc b 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameC|intros;exact I]).
 assert (Valid:Mem.valid_block m b) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 assert (FlagC:Mem.load Mint32 mc b 80=Some (Vint flag)).
 { rewrite (proj1 FrameC Mint32 b 80 Valid ltac:(intros;exact I));exact Flag. }
 destruct (eval_field_slice_weak y mc b 40 Bound YC)
  as (mw & Weak & YW & ValueW & BoundsW & PermW & FrameW & ReadW).
 assert (FreeW:Mem.range_perm mw b 0 88 Cur Freeable) by (intros pos Range;apply PermW;apply FreeC;exact Range).
 destruct (eval_affine_y_negate_words (weak_loose_words y) mw b YW FreeW)
  as (mf & Neg & YF & FreeF & FrameN).
 assert (FrameY:lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) mc mf).
 { eapply lframe_trans;[|exact FrameN].
   eapply lframe_implies;[exact FrameW|intros bx pos Outside ValidC;exact Outside]. }
 assert (XF:fe_at mf b 0 xlimbs).
 { eapply curve_keep_field_range;[exact Length|exact XC|exact FrameY|].
   intros pos Range;right;left;lia. }
 assert (ValidC:Mem.valid_block mc b) by (eapply Mem.perm_valid_block;apply (FreeC 0);lia).
 assert (FlagF:Mem.load Mint32 mf b 80=Some (Vint flag)).
 { rewrite (proj1 FrameY Mint32 b 80 ValidC);[exact FlagC|].
   intros pos Range;right;right;change (80<=pos<84) in Range;lia. }
 destruct (weak_loose_numeric y Bound) as [WeakValue Small].
 destruct (negate_sep_numeric (weak_loose_words y) Small) as [NegValue NegBounds].
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le)
    (m1:=m) (m2:=mf) (out:=Out_normal).
   + apply affine_negate_helper_entry.
   + rewrite affine_negate_helper_body;
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mc) (le1:=le);[exact Copy|].
     eapply exec_affine_negate_y_tail_from_calls;[reflexivity|exact Weak|exact Neg].
   + reflexivity.
   + reflexivity.
 - split;[exact XF|];split;[exact YF|];split;[exact FreeF|];split;[exact FlagF|];split.
   + rewrite NegValue,Zminus_mod,Z.mul_mod,Z.mod_same,Z.mul_0_r,Z.mod_0_l,WeakValue
       by (unfold feP,feR;lia).
     transitivity ((0 mod feP-radix_value y mod feP) mod feP).
     * rewrite Z.mod_0_l by (unfold feP,feR;lia);reflexivity.
     * rewrite <-Zminus_mod,Z.sub_0_l;reflexivity.
   + split;[exact NegBounds|].
     eapply lframe_trans.
     * eapply lframe_implies;[exact FrameC|intros;exact I].
     * eapply lframe_implies;[exact FrameY|intros bx pos Other ValidM;left;exact Other].
Qed.
