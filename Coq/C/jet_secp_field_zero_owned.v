(** Original variable-time zero-mod-p test from a private owned field. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_local_regions C.jet_secp_curve_weak
  C.jet_secp_curve_zero C.jet_secp_curve_frame C.jet_secp_field_add_initial
  C.jet_secp_owned_slice_fields C.jet_secp_field_weak_tight C.jet_secp_point_mul_numeric
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition field_zero_result w := if Z.eqb (radix_value w mod feP) 0 then Int.one else Int.zero.

Theorem eval_field_zero_owned w m b :
  square_input_bounds w -> fe_at m b 0 (words5 w) -> Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr b Ptrofs.zero] E0 mf (Vint (field_zero_result w)) /\
  fe_at mf b 0 (words5 w) /\ Mem.range_perm mf b 0 40 Cur Freeable /\
  lframe (fun bx _=>bx<>b) m mf.
Proof.
  intros HB HF HP.
  assert (HB60 : forall n, (1<=n<=5)%nat -> Int64.unsigned (weak_shift_words w n)<=2^60).
  { intros [|n] HN;[lia|];cbn [weak_shift_words].
    pose proof (HB n ltac:(lia)) as HBi;destruct (Nat.eqb n 4);
      change (2^60) with 1152921504606846976;lia. }
  assert (HR : rep (weak_shift_words w) [(b,0)] local_write_initial_regs m).
  { apply curve_weak_initial_rep;[rewrite weak_shift_values;exact HF|exact HP]. }
  destruct (eval_curve_zero_numeric (weak_shift_words w) [(b,0)] m HR HB60)
    as (mf & HC & HO & HL).
  change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalizes_to_zero_var)
    [Vptr b Ptrofs.zero] E0 mf
    (Vint (if Z.eqb (fe_val (Int64.unsigned (w 0%nat)) (Int64.unsigned (w 1%nat))
      (Int64.unsigned (w 2%nat)) (Int64.unsigned (w 3%nat)) (Int64.unsigned (w 4%nat)) mod feP) 0
      then Int.one else Int.zero))) in HC.
  rewrite <-radix_value_as_fe_val in HC.
  pose proof (rep_region _ _ _ mf 0 _ HO eq_refl) as H0.
  destruct (rep_free_region _ _ _ _ 0 40 HO ltac:(change (0<1)%nat;lia) eq_refl) as [_ HFree].
  assert (HField : fe_at mf b 0 (words5 w)).
  { eapply owned_region_field_slice with (rho:=weak_shift_words w) (beta:=[(b,0)])
      (r:=0%nat) (exprs:=vars5 1) (size:=40).
    - exact H0.
    - lia.
    - exists 0;reflexivity.
    - lia.
    - change (40<=18446744073709551615);lia.
    - reflexivity.
    - reflexivity.
    - intros c HC';exact HC'.
    - reflexivity. }
  exists mf;split;[exact HC|];split;[exact HField|];split;[exact HFree|].
  apply curve_frame_one with (regs:=local_write_initial_regs);[reflexivity|exact HL].
Qed.
