(** Actual +7, weak normalization and field comparison, in curve-check order. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_field_add_initial.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_field_read_preservation C.jet_secp_field_add7 C.jet_secp_curve_weak C.jet_secp_curve_weak_math.
Require Import C.jet_secp_curve_equal C.jet_secp_curve_frame C.jet_secp_curve_tail_values.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge add7_words curve_weak_words.

Theorem curve_tail_calls a b m ba bb : ba<>bb ->
  (forall i, (i < 5)%nat -> Int64.unsigned (a i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  (forall i, (i < 5)%nat -> Int64.unsigned (b i) <
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists m1 m2 mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_add_int)
    [Vptr bb Ptrofs.zero;Vint (Int.repr 7)] E0 m1 Vundef /\
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_normalize_weak)
    [Vptr bb Ptrofs.zero] E0 m2 Vundef /\
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_equal_var)
    [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf
    (Vint (if Z.eqb (radix_value a mod feP) ((radix_value b+7) mod feP) then Int.one else Int.zero)) /\
  Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
  lframe (fun bx _ => bx<>ba /\ bx<>bb) m mf.
Proof.
  intros HNe BA BB HA HB HFA HFB.
  destruct (eval_field_add7_small b m bb HB HFB BB)
    as (m1 & C1 & B1 & V7 & B7 & BF1 & F1).
  pose proof (curve_frame_one add7_regs bb m m1 eq_refl F1) as E1.
  pose proof (field_at_lframe m m1 ba 0 (words5 a) _ HA E1 ltac:(intro pos; exact HNe)) as A1.
  pose proof (curve_keep_free _ m m1 ba 40 ltac:(lia) HFA E1 ltac:(intro pos; exact HNe)) as AF1.
  assert (BW : forall n, (1 <= n <= 5)%nat -> Int64.unsigned (curve_shift_words (add7_words b) n) <= 2^60).
  { intros n HN. unfold curve_shift_words. apply B7; lia. }
  assert (HInitial : fe_at m1 bb 0 (field_values (curve_shift_words (add7_words b)) 1)).
  { rewrite curve_shift_field. exact B1. }
  destruct (eval_curve_weak_numeric (curve_shift_words (add7_words b)) m1 bb HInitial BF1 BW)
    as (m2 & r0 & r1 & r2 & r3 & r4 & C2 & B2 & VW & BR & BF2 & F2).
  destruct BR as (BR0 & BR1 & BR2 & BR3 & BR4).
  destruct (curve_weak_words_value r0 r1 r2 r3 r4 BR0 BR1 BR2 BR3 BR4) as [HVW HBW].
  rewrite <- curve_weak_field in B2.
  pose proof (curve_frame_one local_write_initial_regs bb m1 m2 eq_refl F2) as E2.
  pose proof (field_at_lframe m1 m2 ba 0 (words5 a) _ A1 E2 ltac:(intro pos; exact HNe)) as A2.
  pose proof (curve_keep_free _ m1 m2 ba 40 ltac:(lia) AF1 E2 ltac:(intro pos; exact HNe)) as AF2.
  assert (HWeakValue : radix_value (curve_weak_words r0 r1 r2 r3 r4) mod feP = (radix_value b+7) mod feP).
  { rewrite HVW, VW.
    change (fe_val (Int64.unsigned (add7_words b 0%nat))
      (Int64.unsigned (add7_words b 1%nat)) (Int64.unsigned (add7_words b 2%nat))
      (Int64.unsigned (add7_words b 3%nat)) (Int64.unsigned (add7_words b 4%nat)) mod feP =
      (radix_value b+7) mod feP).
    rewrite <- radix_value_matches_normalizer, V7. reflexivity. }
  pose proof (curve_equal_initial a (curve_weak_words r0 r1 r2 r3 r4) m2 ba bb HNe A2 B2 AF2 BF2) as HR.
  pose proof (curve_equal_inputs_bounded a (curve_weak_words r0 r1 r2 r3 r4) BA HBW) as HBounds.
  destruct (eval_curve_equal_numeric (curve_equal_rho a (curve_weak_words r0 r1 r2 r3 r4))
    [(ba,0);(bb,0)] m2 HR HBounds) as (mf & C3 & HFinal & F3).
  rewrite curve_equal_first_value, curve_equal_second_value, HWeakValue in C3.
  destruct (rep_free_region _ _ _ _ 0 40 HFinal ltac:(change (0<2)%nat; lia) eq_refl) as [_ AF3].
  destruct (rep_free_region _ _ _ _ 1 40 HFinal ltac:(change (1<2)%nat; lia) eq_refl) as [_ BF3].
  pose proof (curve_frame_two curve_equal_regs ba bb m2 mf eq_refl F3) as E3.
  exists m1,m2,mf. split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  split; [exact AF3|]. split; [exact BF3|].
  eapply lframe_trans.
  - eapply lframe_implies; [exact E1|]. intros bx pos [_ HNotB] HV; exact HNotB.
  - eapply lframe_trans.
    + eapply lframe_implies; [exact E2|]. intros bx pos [_ HNotB] HV; exact HNotB.
    + exact E3.
Qed.
