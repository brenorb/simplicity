(** Third checkpoint constructed from the actual checked second-fold postcondition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Maps Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jets_secp.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_sx_forget_cells C.jet_secp_scalar_reduce512_run
  C.jet_secp_reduce512_typed_stage C.jet_secp_reduce512_typed_atomic
  C.jet_secp_reduce512_typed_value C.jet_secp_reduce512_typed_exec
  C.jet_secp_reduce512_checkpoint C.jet_secp_reduce512_fold_bounds
  C.jet_secp_reduce512_third_stage C.jet_secp_reduce512_third_atomic
  C.jet_secp_reduce512_third_value C.jet_secp_reduce512_wide
  C.jet_secp_scalar_mul512_symbolic C.jet_secp_scalar_mul512_accumulate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition second_checkpoint_digits (rho : nat -> int64) n :=
  match n with
  | 0%nat => wlo (stage_ma0 (first_checkpoint_digits rho))
  | 1%nat => wlo (stage_ma1 (first_checkpoint_digits rho))
  | 2%nat => wlo (stage_ma2 (first_checkpoint_digits rho) (first_checkpoint_m6 rho))
  | 3%nat => wlo (stage_ma3 (first_checkpoint_digits rho) (first_checkpoint_m6 rho))
  | _ => Int64.zero end.
Definition second_checkpoint_p4 rho := Int64.loword
  (Int64.add (whi (stage_ma3 (first_checkpoint_digits rho) (first_checkpoint_m6 rho)))
    (stage_ma_m6 (first_checkpoint_m6 rho))).
Lemma second_checkpoint_p4_value rho : Int.unsigned (second_checkpoint_p4 rho) =
  stage_p4_integer (first_checkpoint_digits rho) (first_checkpoint_m6 rho).
Proof.
  pose proof (stage_p4_unsigned (first_checkpoint_digits rho) (first_checkpoint_m6 rho)
    (proj2 (first_checkpoint_m6_bound rho))
    ltac:(rewrite (proj2 (first_checkpoint_values rho)); exact (proj2 (first_high256_bound rho)))) as H.
  change (Int64.unsigned (stage_ma_m6 (second_checkpoint_p4 rho)) =
    stage_p4_integer (first_checkpoint_digits rho) (first_checkpoint_m6 rho)) in H.
  rewrite stage_m6_unsigned in H; exact H.
Qed.
Lemma second_checkpoint_p4_bound rho : 0 <= Int.unsigned (second_checkpoint_p4 rho) <= 2.
Proof. rewrite second_checkpoint_p4_value; apply first_checkpoint_p4_bound. Qed.
Lemma second_checkpoint_split rho :
  third_input_low (second_checkpoint_digits rho) + reduce512_radix * Int.unsigned (second_checkpoint_p4 rho) =
    second_fold_bridge_value rho.
Proof.
  pose proof (first_checkpoint_second_value rho) as H.
  change (column_words_value (stage_prefix (first_checkpoint_digits rho) (first_checkpoint_m6 rho) ++
    [stage_ma_m6 (second_checkpoint_p4 rho)]) = second_fold_bridge_value rho) in H.
  rewrite column_words_append in H.
  change (third_input_low (second_checkpoint_digits rho) + reduce512_radix *
    (Int64.unsigned (stage_ma_m6 (second_checkpoint_p4 rho)) + Int64.modulus * 0) =
    second_fold_bridge_value rho) in H.
  rewrite stage_m6_unsigned,Z.mul_0_r,Z.add_0_r in H; exact H.
Qed.
Lemma second_checkpoint_third_modulo rho :
  third_fold_value (second_checkpoint_digits rho) (second_checkpoint_p4 rho) mod canonical_group_order =
    second_fold_bridge_value rho mod canonical_group_order.
Proof.
  rewrite <- second_checkpoint_split.
  unfold third_fold_value; rewrite reduce512_delta_order.
  replace (third_input_low (second_checkpoint_digits rho) +
    reduce512_radix * Int.unsigned (second_checkpoint_p4 rho)) with
    ((third_input_low (second_checkpoint_digits rho) + Int.unsigned (second_checkpoint_p4 rho) *
      (reduce512_radix - canonical_group_order)) +
      Int.unsigned (second_checkpoint_p4 rho) * canonical_group_order) by ring.
  rewrite Z.mod_add by (unfold canonical_group_order; discriminate); reflexivity.
Qed.
Lemma second_checkpoint_forget_stack digits p4 :
  forget_after 2 (sregs (reduce512_typed_stage_state digits p4)) =
    scalar_reduce512_initial_regs ++ fst reduce512_allocated.
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma second_checkpoint_param_sources digits p4 :
  (stemps (reduce512_typed_stage_state digits p4))!_r = Some (XP 0 0) /\
  (stemps (reduce512_typed_stage_state digits p4))!_l = Some (XP 1 0).
Proof. Timeout 10 (split; reflexivity). Qed.
Local Opaque reduce512_typed_stage_state.
Theorem second_checkpoint_tmatch rho beta le :
  tmatch rho beta (stemps (reduce512_typed_stage_state
    (first_checkpoint_digits rho) (first_checkpoint_m6 rho))) le ->
  tmatch rho beta (reduce512_third_temps (second_checkpoint_digits rho) (second_checkpoint_p4 rho)) le.
Proof.
  intro HT.
  destruct (second_checkpoint_param_sources (first_checkpoint_digits rho) (first_checkpoint_m6 rho)) as [SR SL].
  destruct (typed_stage_raw_temps (first_checkpoint_digits rho) (first_checkpoint_m6 rho))
    as (S0 & S1 & S2 & S3 & S4).
  destruct (stage_columns_rep (first_checkpoint_digits rho) (first_checkpoint_m6 rho) rho (lay beta))
    as [[D0 _] [[D1 _] [[D2 _] [D3 [DH _]]]]].
  pose proof (HT _ _ SR) as LR; pose proof (HT _ _ SL) as LL.
  pose proof (HT _ _ S0) as L0; rewrite D0 in L0.
  pose proof (HT _ _ S1) as L1; rewrite D1 in L1.
  pose proof (HT _ _ S2) as L2; rewrite D2 in L2.
  pose proof (HT _ _ S3) as L3; rewrite D3 in L3.
  pose proof (HT _ _ S4) as L4.
  assert (DS : den rho (lay beta) (XLb Badd
      (sc_hi (stage_sy3 (first_checkpoint_digits rho) (first_checkpoint_m6 rho)))
      (stage_sy_m6 (first_checkpoint_m6 rho))) =
    Vlong (Int64.add (whi (stage_ma3 (first_checkpoint_digits rho) (first_checkpoint_m6 rho)))
      (stage_ma_m6 (first_checkpoint_m6 rho)))) by
    (apply column_ladd_den; [exact DH|apply stage_m6_den]).
  change (le!_p4 = Some (Vint (Int64.loword (il (den rho (lay beta)
    (XLb Badd (sc_hi (stage_sy3 (first_checkpoint_digits rho) (first_checkpoint_m6 rho)))
      (stage_sy_m6 (first_checkpoint_m6 rho)))))))) in L4.
  rewrite DS in L4.
  unfold reduce512_third_temps.
  apply tmatch_checkpoint_set; [|exact L4].
  apply tmatch_checkpoint_set; [|exact L3].
  apply tmatch_checkpoint_set; [|exact L2].
  apply tmatch_checkpoint_set; [|exact L1].
  apply tmatch_checkpoint_set; [|exact L0].
  apply tmatch_checkpoint_set; [|exact LL].
  apply tmatch_checkpoint_set; [|exact LR].
  intros id x HX; rewrite PTree.gempty in HX; discriminate.
Qed.
