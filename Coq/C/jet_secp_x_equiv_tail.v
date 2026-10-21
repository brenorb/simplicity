(** Original weak-normalize and comparison calls, with no +7 operation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_field_add_initial.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_field_read_preservation C.jet_secp_curve_weak C.jet_secp_curve_weak_math.
Require Import C.jet_secp_curve_equal C.jet_secp_curve_frame C.jet_secp_curve_tail_values.
Require Import C.jet_secp_square_columns.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge curve_weak_words.

Theorem x_equiv_normalize_equal_calls a b m ba bb :
  ba<>bb ->
  (forall i, (i<5)%nat -> Int64.unsigned (a i)<
    if Nat.eqb i 4 then 562949953421312 else 4503599627370496) ->
  square_input_bounds b ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mn mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_normalize_weak)
      [Vptr bb Ptrofs.zero] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_secp256k1_fe_equal_var)
      [Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf
      (Vint (if Z.eqb (radix_value a mod feP) (radix_value b mod feP) then Int.one else Int.zero)) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
    lframe (fun bx _ => bx<>ba /\ bx<>bb) m mf.
Proof.
  intros HNe BA BB HA HB HFA HFB.
  assert (BW : forall n, (1<=n<=5)%nat -> Int64.unsigned (curve_shift_words b n)<=2^60).
  { intros n HN. unfold curve_shift_words. pose proof (BB (n-1)%nat ltac:(lia)).
    destruct (Nat.eqb (n-1)%nat 4); lia. }
  assert (HInitial : fe_at m bb 0 (field_values (curve_shift_words b) 1)).
  { rewrite curve_shift_field; exact HB. }
  destruct (eval_curve_weak_numeric (curve_shift_words b) m bb HInitial HFB BW)
    as (mn & r0 & r1 & r2 & r3 & r4 & CN & BN & VN & BR & BFN & FN).
  destruct BR as (B0 & B1 & B2 & B3 & B4).
  destruct (curve_weak_words_value r0 r1 r2 r3 r4 B0 B1 B2 B3 B4) as (HVW & HBW).
  rewrite <- curve_weak_field in BN.
  pose proof (curve_frame_one local_write_initial_regs bb m mn eq_refl FN) as EN.
  pose proof (field_at_lframe m mn ba 0 (words5 a) _ HA EN ltac:(intro pos;exact HNe)) as AN.
  pose proof (curve_keep_free _ m mn ba 40 ltac:(lia) HFA EN ltac:(intro pos;exact HNe)) as AFN.
  assert (HWeakValue : radix_value (curve_weak_words r0 r1 r2 r3 r4) mod feP = radix_value b mod feP).
  { rewrite HVW, VN.
    change (fe_val (Int64.unsigned (b 0%nat)) (Int64.unsigned (b 1%nat))
      (Int64.unsigned (b 2%nat)) (Int64.unsigned (b 3%nat)) (Int64.unsigned (b 4%nat)) mod feP =
      radix_value b mod feP).
    rewrite <- radix_value_matches_normalizer; reflexivity. }
  pose proof (curve_equal_initial a (curve_weak_words r0 r1 r2 r3 r4) mn ba bb HNe AN BN AFN BFN) as HR.
  pose proof (curve_equal_inputs_bounded a (curve_weak_words r0 r1 r2 r3 r4) BA HBW) as HBnd.
  destruct (eval_curve_equal_numeric (curve_equal_rho a (curve_weak_words r0 r1 r2 r3 r4))
    [(ba,0);(bb,0)] mn HR HBnd) as (mf & CE & HP & FE).
  rewrite curve_equal_first_value, curve_equal_second_value, HWeakValue in CE.
  destruct (rep_free_region _ _ _ _ 0 40 HP ltac:(change (0<2)%nat;lia) eq_refl) as [_ AFF].
  destruct (rep_free_region _ _ _ _ 1 40 HP ltac:(change (1<2)%nat;lia) eq_refl) as [_ BFF].
  pose proof (curve_frame_two curve_equal_regs ba bb mn mf eq_refl FE) as EE.
  exists mn,mf. split; [exact CN|]. split; [exact CE|].
  split; [exact AFF|]. split; [exact BFF|].
  eapply lframe_trans; [|exact EE]. eapply lframe_implies; [exact EN|].
  intros b0 pos [_ HNotB] HV; exact HNotB.
Qed.
Print Assumptions x_equiv_normalize_equal_calls.
