(** Original initialization establishes the checked loop's actual starting state. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_fg_prefix C.jet_secp_modinv_fg_prefix_numeric.
Require Import C.jet_secp_modinv_fg_iteration_prefix C.jet_secp_modinv_fg_iteration_numeric.
Require Import C.jet_secp_modinv_fg_iteration_arith C.jet_secp_modinv_fg_loop C.jet_secp_modinv_fg_loop_numeric.
Require Import C.jet_secp_i128_shift62 C.jet_secp_i128_shift62_numeric.
Require Import C.jet_sx_u64_transport C.jet_secp_multiply_second_temps.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition fg_start_carry (rho : nat->int64) (high : bool) :=
 let u:=if high then 12%nat else 10%nat in
 let v:=if high then 13%nat else 11%nat in
 (i128_shift62_low (fg_row_low rho u v) (fg_row_high rho u v),
  i128_shift62_high (fg_row_high rho u v)).
Definition fg_start_rho (rho : nat->int64) n := match n with
 | 15%nat=>fst (fg_start_carry rho false) | 16%nat=>snd (fg_start_carry rho false)
 | 17%nat=>fst (fg_start_carry rho true) | 18%nat=>snd (fg_start_carry rho true)
 | _=>rho n end.
Definition fg_input_bounds rho : Prop :=
 (forall high,Z.abs (Int64.signed (fg_iter_u rho high))+Z.abs (Int64.signed (fg_iter_v rho high))<=2^62) /\
 (forall high j,(j<5)%nat -> Z.abs (Int64.signed (fg_array_word rho high j))<=2^62).

Lemma fg_start_input rho high : fg_iter_input (fg_start_rho rho) high=fg_start_carry rho high.
Proof. destruct high;reflexivity. Qed.
Lemma fg_start_array rho high j : (j<5)%nat ->
 fg_array_word (fg_start_rho rho) high j=fg_array_word rho high j.
Proof. destruct high;destruct j as [|[|[|[|[|j]]]]];intro J;try lia;reflexivity. Qed.
Lemma fg_start_row rho high : fg_iter_u (fg_start_rho rho) high=fg_iter_u rho high /\
 fg_iter_v (fg_start_rho rho) high=fg_iter_v rho high.
Proof. destruct high;split;reflexivity. Qed.

Lemma fg_start_carry_value rho high : fg_input_bounds rho ->
 fg_pair_value (fg_start_carry rho high)=fg_combination rho high 0/2^62.
Proof.
 intros (Rows & Limbs);destruct high;
 apply fg_row_numeric;apply fg_row_range;exact (Rows true) || exact (Rows false).
Qed.
Lemma fg_start_carry_bound rho high : fg_input_bounds rho -> Z.abs (fg_pair_value (fg_start_carry rho high))<=2^62.
Proof.
 intro Bounds;pose proof Bounds as (Rows & Limbs);rewrite fg_start_carry_value by exact Bounds.
 pose proof (Rows high) as Row.
 pose proof (Limbs false 0%nat ltac:(lia)) as F;pose proof (Limbs true 0%nat ltac:(lia)) as G.
 assert (UF : Z.abs (Int64.signed (fg_iter_u rho high)*Int64.signed (rho 0%nat))<=
  Z.abs (Int64.signed (fg_iter_u rho high))*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact F]. }
 assert (VG : Z.abs (Int64.signed (fg_iter_v rho high)*Int64.signed (rho 5%nat))<=
  Z.abs (Int64.signed (fg_iter_v rho high))*2^62).
 { rewrite Z.abs_mul;apply Z.mul_le_mono_nonneg_l;[apply Z.abs_nonneg|exact G]. }
 pose proof (Z.abs_triangle (Int64.signed (fg_iter_u rho high)*Int64.signed (rho 0%nat))
  (Int64.signed (fg_iter_v rho high)*Int64.signed (rho 5%nat))) as Triangle.
 assert (Sum : Z.abs (fg_combination rho high 0)<=2^124).
 { unfold fg_combination;change (Z.abs (Int64.signed (fg_iter_u rho high)*Int64.signed (rho 0%nat)+
    Int64.signed (fg_iter_v rho high)*Int64.signed (rho 5%nat))<=2^124).
   eapply Z.le_trans;[exact Triangle|].
   eapply Z.le_trans;[exact (Z.add_le_mono _ _ _ _ UF VG)|].
   rewrite <-Z.mul_add_distr_r;change (2^124) with (2^62*2^62).
   apply Z.mul_le_mono_nonneg_r;[lia|exact Row]. }
 apply Z.abs_le in Sum;apply Z.abs_le;split;
 [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia.
Qed.
Lemma fg_start_state_bounds rho : fg_input_bounds rho -> fg_state_bounds (fg_start_rho rho).
Proof.
 intro Bounds;pose proof Bounds as (Rows & Limbs);split.
 - intro high;rewrite fg_start_input;destruct (fg_start_row rho high) as (U & V);rewrite U,V.
   split;[pose proof (fg_start_carry_bound rho high Bounds);lia|apply Rows].
 - intros high j J;rewrite fg_start_array by exact J;apply Limbs;exact J.
Qed.
Lemma fg_start_carry_fits64 rho high : fg_input_bounds rho ->
 Int64.min_signed<=fg_pair_value (fg_iter_input (fg_start_rho rho) high)<=Int64.max_signed.
Proof.
 intro Bounds;rewrite fg_start_input;pose proof (fg_start_carry_bound rho high Bounds) as Bound.
 apply Z.abs_le in Bound;change Int64.min_signed with (-2^63);change Int64.max_signed with (2^63-1);lia.
Qed.

Lemma fg_start_rep rho beta m : rep rho beta fg_prefix_out m -> rep (fg_start_rho rho) beta fg_iter_regs m.
Proof.
 intros (Len & Sep & Regions);split;[exact Len|];split.
 - eapply rsep_shape with (regs:=fg_prefix_out);[reflexivity|exact Sep].
 - intros r reg Entry.
   assert (R : (r<length fg_iter_regs)%nat) by (apply nth_error_Some;congruence).
   change (r<5)%nat in R;destruct r as [|[|[|[|[|r]]]]];try lia.
   all: cbn [fg_iter_regs fg_regs app nth_error] in Entry;injection Entry as <-.
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=0%nat)
      (xs:=[XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]) (ys:=[XLv 0;XLv 1;XLv 2;XLv 3;XLv 4]);
      try reflexivity;exact (Regions 0%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=1%nat)
      (xs:=[XLv 5;XLv 6;XLv 7;XLv 8;XLv 9]) (ys:=[XLv 5;XLv 6;XLv 7;XLv 8;XLv 9]);
      try reflexivity;exact (Regions 1%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat)
      (xs:=[XLv 10;XLv 11;XLv 12;XLv 13]) (ys:=[XLv 10;XLv 11;XLv 12;XLv 13]);
      try reflexivity;exact (Regions 2%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=3%nat)
      (xs:=fg_shifted_row (XLv 10) (XLv 11)) (ys:=[XLv 15;XLv 16]);
      try reflexivity;exact (Regions 3%nat _ eq_refl).
   + eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=4%nat)
      (xs:=fg_shifted_row (XLv 12) (XLv 13)) (ys:=[XLv 17;XLv 18]);
      try reflexivity;exact (Regions 4%nat _ eq_refl).
Qed.

Lemma fg_start_temps rho beta le :
 tmatch rho beta (stemps (fst (rsel rho (lay beta) fg_prefix_tree))) le ->
 tmatch (fg_start_rho rho) beta (fg_iter_temps 1) (PTree.set _i (Vint Int.one) le).
Proof.
 intro Temps;rewrite fg_fixed_initial;apply tmatch_set;apply tmatch_bindings.
 assert (Fixed : Forall (binding_actual rho beta le) fg_fixed_bindings).
 { eapply Forall_impl;[|exact (fg_prefix_live_kept rho (lay beta))].
   intros [id x] Kept;exact (Temps id x Kept). }
 assert (Eq : binding_values (fg_start_rho rho) beta fg_fixed_bindings=binding_values rho beta fg_fixed_bindings)
  by reflexivity.
 assert (Values : Forall (fun p=>le!(fst p)=Some (snd p)) (binding_values rho beta fg_fixed_bindings)).
 { unfold binding_values;rewrite Forall_map;exact Fixed. }
 rewrite <-Eq in Values;unfold binding_values in Values;rewrite Forall_map in Values;exact Values.
Qed.
