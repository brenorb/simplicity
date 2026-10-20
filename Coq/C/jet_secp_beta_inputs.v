(** Derive the borrowed multiplier's real input relation from reader storage
    and the original initialized beta global. No extra input-range restriction. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Values Memory.
Require Import Simplicity.Word.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_b32_exec C.jet_secp_local_regions C.jet_secp_fe_math C.jet_secp_fe_nv.
Require Import C.jet_secp_multiply_run_run C.jet_secp_multiply_first_arithmetic
  C.jet_secp_multiply_finish_product C.jet_secp_multiply_input_input.
Require Import C.jet_borrowed_region C.jet_secp_multiply_borrowed_call C.jet_secp_beta_global.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque beta_block.

Definition beta_mixed_rho (rho : nat -> int64) i :=
  if (i <? 5)%nat then rho i else beta_digits (i - 5)%nat.
Definition beta_input_rho (x : Ty.tySem (Word 8)) :=
  beta_mixed_rho (limb_rho (normalized_value x)).

Lemma beta_mixed_left rho i : (i < 5)%nat -> beta_mixed_rho rho i = rho i.
Proof. intro HI; unfold beta_mixed_rho; rewrite (proj2 (Nat.ltb_lt i 5) HI); reflexivity. Qed.
Lemma beta_mixed_right rho i : beta_mixed_rho rho (i + 5)%nat = beta_digits i.
Proof.
  unfold beta_mixed_rho; rewrite (proj2 (Nat.ltb_ge (i+5) 5) ltac:(lia)), Nat.add_sub; reflexivity.
Qed.
Lemma beta_rhs_nth i x : nth_error (vars5 5) i = Some x ->
  (i < 5)%nat /\ x = XLv (i + 5)%nat.
Proof. intro H; destruct (vars5_offset_nth 5 i x H) as [HI ->]; split; [exact HI|f_equal; lia]. Qed.

Theorem beta_borrowed_region rho layout m r :
  lay layout r = (beta_block, 0) -> beta_global_rep m ->
  region_ok (beta_mixed_rho rho) layout m r
    (borrowed_region (mkreg (u64_cells 0 (vars5 5)) true (Some 40))).
Proof.
  intros HE (HV & HP & HL).
  assert (EB : blk layout r = beta_block) by (unfold blk; rewrite HE; reflexivity).
  assert (ES : bas layout r = 0) by (unfold bas; rewrite HE; reflexivity).
  unfold borrowed_region; apply region_u64.
  - rewrite ES; lia.
  - rewrite ES; exists 0; reflexivity.
  - rewrite ES; change (40 <= 18446744073709551615); lia.
  - rewrite EB; exact HV.
  - rewrite EB, ES; change (Mem.range_perm m beta_block 0 40 Cur Readable); exact HP.
  - intros i x HN; rewrite EB, ES, Z.add_0_l.
    destruct (beta_rhs_nth i x HN) as [HI ->]; split; [|reflexivity].
    change (Mem.load Mint64 m beta_block (8 * Z.of_nat i) =
      Some (Vlong (beta_mixed_rho rho (i + 5)%nat))).
    rewrite beta_mixed_right; apply HL; apply nth_error_nth'; rewrite beta_words_count; exact HI.
Qed.

Lemma beta_not_freeable m ba : beta_readonly_bounds m ->
  Mem.range_perm m ba 0 40 Cur Freeable -> ba <> beta_block.
Proof.
  intros HB HF HE; subst ba.
  destruct (proj1 (HB 0 Cur Freeable) (HF 0 ltac:(lia))) as [_ HO]. inversion HO.
Qed.

Theorem beta_inputs_from_storage x m ba :
  fe_at m ba 0 (map Int64.repr (fe_limbs_of (normalized_value x))) ->
  Mem.range_perm m ba 0 40 Cur Freeable -> ba <> beta_block -> beta_global_rep m ->
  rep (beta_input_rho x) [(ba,0);(beta_block,0)] borrowed_mul_regs m.
Proof.
  intros HA HF HD HG; apply two_region_rep_separate; [reflexivity|exact HD| |].
  - apply (owned_field_region _ _ _ _ 0 (normalized_value x));
      [reflexivity|exact HA|exact HF|].
    intros i HI; rewrite Nat.add_0_l; apply beta_mixed_left; exact HI.
  - apply beta_borrowed_region; [reflexivity|exact HG].
Qed.

Lemma beta_input_bounds x : field_input_bounds (beta_input_rho x).
Proof.
  intros i HI; unfold beta_input_rho, beta_mixed_rho; destruct (i <? 5)%nat eqn:EI.
  - pose proof (limb_rho_bound (normalized_value x) (normalized_value_range x) i) as HB.
    change (0 <= Int64.unsigned (limb_rho (normalized_value x) i) <= 4503599627370495) in HB.
    destruct ((Nat.eqb i 4 || Nat.eqb i 9)%bool); lia.
  - apply Nat.ltb_ge in EI; pose proof (beta_limb_bounds (i-5)%nat ltac:(lia)).
    destruct (Nat.eqb (i-5) 4), ((Nat.eqb i 4 || Nat.eqb i 9)%bool); lia.
Qed.
Lemma beta_input_left_value x : radix_value (beta_input_rho x) = normalized_value x.
Proof.
  unfold radix_value, beta_input_rho; rewrite !beta_mixed_left by lia.
  apply (radix_limb_rho _ (normalized_value_range x)).
Qed.
Lemma beta_input_right_value x : radix_value (second_input (beta_input_rho x)) = beta_value.
Proof.
  unfold radix_value, second_input, beta_input_rho; rewrite !beta_mixed_right.
  exact beta_radix_value.
Qed.
