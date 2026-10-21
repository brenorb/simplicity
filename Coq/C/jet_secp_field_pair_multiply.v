(** Storage adapter for the selected original in-place field multiplier.
    Both 40-byte caller objects remain owned; square outputs need not be
    canonical. No alternate multiplication implementation is introduced. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_field_add_initial C.jet_sx_revalue_cells.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_first_arithmetic.
Require Import C.jet_secp_multiply_call_call C.jet_secp_multiply_wrapper_call.
Require Import C.jet_secp_multiply_finish_execute C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_checkpoint_columns.
Require Import C.jet_secp_square_columns C.jet_secp_b32_exec C.jet_secp_curve_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge original_finish_words.

Definition field_pair_valuation (a b : nat -> int64) (n : nat) :=
  nth n (words5 a ++ words5 b) Int64.zero.
Definition field_pair_product a b := original_finish_words (field_pair_valuation a b).
Lemma field_pair_left a b : field_values (field_pair_valuation a b) 0 = words5 a.
Proof. reflexivity. Qed.
Lemma field_pair_right a b : field_values (field_pair_valuation a b) 5 = words5 b.
Proof. reflexivity. Qed.
Lemma field_pair_radix_left a b : radix_value (field_pair_valuation a b) = radix_value a.
Proof. reflexivity. Qed.
Lemma field_pair_radix_right a b : radix_value (second_input (field_pair_valuation a b)) = radix_value b.
Proof. reflexivity. Qed.

Lemma field_pair_input_bounds a b : square_input_bounds a -> square_input_bounds b ->
  field_input_bounds (field_pair_valuation a b).
Proof.
  intros BA BB n HN.
  pose proof (BA 0%nat ltac:(lia)); pose proof (BA 1%nat ltac:(lia));
  pose proof (BA 2%nat ltac:(lia)); pose proof (BA 3%nat ltac:(lia));
  pose proof (BA 4%nat ltac:(lia)); pose proof (BB 0%nat ltac:(lia));
  pose proof (BB 1%nat ltac:(lia)); pose proof (BB 2%nat ltac:(lia));
  pose proof (BB 3%nat ltac:(lia)); pose proof (BB 4%nat ltac:(lia)).
  cbn [Nat.eqb] in *.
  do 10 (destruct n as [|n];
    [cbn [field_pair_valuation words5 nth app Nat.eqb orb];lia|]). lia.
Qed.
Lemma field_pair_initial a b m ba bb : ba<>bb ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  rep (field_pair_valuation a b) [(ba,0);(bb,0)] field_mul_regs m.
Proof.
  intros HNe HA HB HFA HFB. apply two_region_rep_separate; [reflexivity|exact HNe| |].
  - apply (region_with_freeable _ _ _ _ (fe_reg (vars5 0)) 40).
    + apply field_region_from_values; rewrite field_pair_left; exact HA.
    + reflexivity.
    + reflexivity.
    + exact HFA.
    + apply field_region_storage_size.
  - apply (region_with_freeable _ _ _ _ (fe_reg (vars5 5)) 40).
    + apply field_region_from_values; rewrite field_pair_right; exact HB.
    + reflexivity.
    + reflexivity.
    + exact HFB.
    + apply field_region_storage_size.
Qed.

Lemma field_pair_output a b m ba bb :
  rep (field_pair_valuation a b) [(ba,0);(bb,0)]
    (field_output_regs (field_pair_valuation a b)) m ->
  fe_at m ba 0 (words5 (field_pair_product a b)) /\
  fe_at m bb 0 (words5 b) /\
  Mem.range_perm m ba 0 40 Cur Freeable /\ Mem.range_perm m bb 0 40 Cur Freeable.
Proof.
  intro HR.
  pose proof (rep_region _ _ _ m 0 _ HR eq_refl) as H0.
  pose proof (rep_region _ _ _ m 1 _ HR eq_refl) as H1.
  pose proof H0 as (_ & _ & _ & _ & _ & _ & HFA & _).
  pose proof H1 as (_ & _ & _ & _ & _ & _ & HFB & _).
  split.
  - exact (u64_region_fe_at (field_pair_valuation a b) [(ba,0);(bb,0)] m 0
      (field_pair_product a b) (Some 40) H0).
  - split; [|split;assumption].
    exact (u64_region_fe_at (field_pair_valuation a b) [(ba,0);(bb,0)] m 1 b (Some 40) H1).
Qed.

Theorem eval_field_pair_multiply a b m ba bb :
  square_input_bounds a -> square_input_bounds b -> ba<>bb ->
  fe_at m ba 0 (words5 a) -> fe_at m bb 0 (words5 b) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
      [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef /\
    fe_at mf ba 0 (words5 (field_pair_product a b)) /\ fe_at mf bb 0 (words5 b) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
    radix_value (field_pair_product a b) mod field_prime = (radix_value a * radix_value b) mod field_prime /\
    square_input_bounds (field_pair_product a b) /\
    (forall i, (i<5)%nat -> 0<=Int64.unsigned (field_pair_product a b i)<
      if Nat.eqb i 4 then 562949953421312 else 4503599627370496) /\
    lframe (fun bx _ => bx<>ba /\ bx<>bb) m mf.
Proof.
  intros BA BB HNe HA HB HFA HFB.
  destruct (eval_original_field_mul_wrapper_product (field_pair_valuation a b) [(ba,0);(bb,0)] m
    (field_pair_input_bounds a b BA BB) (field_pair_initial a b m ba bb HNe HA HB HFA HFB))
    as (mf & HC & HR & HL & HV & HBnd & HF).
  destruct (field_pair_output a b mf ba bb HR) as (HA' & HB' & HFA' & HFB').
  rewrite field_pair_radix_left, field_pair_radix_right in HV.
  exists mf. split; [exact HC|]. split; [exact HA'|]. split; [exact HB'|].
  split; [exact HFA'|]. split; [exact HFB'|]. split; [exact HV|]. split.
  - intros i HI. unfold field_pair_product. pose proof (HBnd i HI); destruct (Nat.eqb i 4);lia.
  - split; [exact HBnd|]. exact (curve_frame_two field_mul_regs ba bb m mf eq_refl HF).
Qed.
Print Assumptions eval_field_pair_multiply.
