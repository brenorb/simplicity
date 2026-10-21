(** First two actual calls of gej_eq_x_var, derived from caller storage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv.
Require Import C.jet_secp_field_read_preservation C.jet_secp_curve_frame.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_multiply_checkpoint_columns C.jet_secp_square_columns C.jet_secp_square_numeric.
Require Import C.jet_secp_point_square_z C.jet_secp_field_pair_multiply.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words field_pair_product.

Theorem x_equiv_square_multiply_calls q x z m bp bq br :
  square_input_bounds q -> square_input_bounds z -> bp<>bq -> br<>bp -> br<>bq ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 80 (words5 z) -> fe_at m bq 0 (words5 q) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bq 0 40 Cur Freeable ->
  Mem.range_perm m br 0 40 Cur Freeable ->
  exists ms mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
      [Vptr br Ptrofs.zero;Vptr bp (Ptrofs.repr 80)] E0 ms Vundef /\
    Clight2.eval_funcall secp_ge ms (Internal f_secp256k1_fe_mul)
      [Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bq Ptrofs.zero] E0 mf Vundef /\
    fe_at mf br 0 (words5 (field_pair_product (square_words z) q)) /\
    fe_at mf bq 0 (words5 q) /\ fe_at mf bp 0 (words5 x) /\
    Mem.range_perm mf br 0 40 Cur Freeable /\ Mem.range_perm mf bq 0 40 Cur Freeable /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\
    radix_value (field_pair_product (square_words z) q) mod field_prime =
      (radix_value z * radix_value z * radix_value q) mod field_prime /\
    (forall i, (i<5)%nat -> 0<=Int64.unsigned (field_pair_product (square_words z) q i)<
      if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
    lframe (fun b _ => b<>bp /\ b<>bq /\ b<>br) m mf.
Proof.
  intros BQ BZ HPQ HRP HRQ HX HZ HQ HFP HFQ HFR.
  destruct (eval_point_square_z_from_storage z m br bp BZ HFR HZ HFP HRP)
    as (ms & CS & RS & RFS & ZS & PFS & VS & BS & FS).
  pose proof (curve_frame_two point_square_z_regs br bp m ms eq_refl FS) as ES.
  pose proof (field_at_lframe m ms bq 0 (words5 q) _ HQ ES
    ltac:(intro pos;split;congruence)) as QS.
  pose proof (curve_keep_free _ m ms bq 40 ltac:(lia) HFQ ES
    ltac:(intro pos;split;congruence)) as QFS.
  assert (XS : fe_at ms bp 0 (words5 x)).
  { eapply curve_keep_field_range; [reflexivity|exact HX|exact FS|].
    intros pos HPos HFoot. destruct (point_square_z_foot br bp bp pos HFoot) as [[HE _]|[_ HR]].
    - congruence.
    - lia. }
  destruct (eval_field_pair_multiply (square_words z) q ms br bq BS BQ HRQ RS QS RFS QFS)
    as (mf & CM & RF & QF & RFF & QFF & VM & BM & BT & FM).
  pose proof (field_at_lframe ms mf bp 0 (words5 x) _ XS FM
    ltac:(intro pos;split;congruence)) as XF.
  pose proof (curve_keep_free _ ms mf bp 128 ltac:(lia) PFS FM
    ltac:(intro pos;split;congruence)) as PFF.
  assert (HV : radix_value (field_pair_product (square_words z) q) mod field_prime =
      (radix_value z*radix_value z*radix_value q) mod field_prime).
  { rewrite VM, Z.mul_mod by (unfold field_prime,field_c;lia).
    rewrite VS, <- Z.mul_mod by (unfold field_prime,field_c;lia);reflexivity. }
  exists ms,mf. split; [exact CS|]. split; [exact CM|]. split; [exact RF|].
  split; [exact QF|]. split; [exact XF|]. split; [exact RFF|].
  split; [exact QFF|]. split; [exact PFF|]. split; [exact HV|]. split; [exact BT|].
  eapply lframe_trans.
  - eapply lframe_implies; [exact ES|]. intros b pos (HNP & HNQ & HNR) HVB;split;assumption.
  - eapply lframe_implies; [exact FM|]. intros b pos (HNP & HNQ & HNR) HVB;split;assumption.
Qed.
Print Assumptions x_equiv_square_multiply_calls.
