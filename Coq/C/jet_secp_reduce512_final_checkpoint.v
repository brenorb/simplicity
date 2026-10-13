(** Preserve initialized output while checkpointing the final suffix. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Maps Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem C.jets_secp
  C.jet_secp_scalar_overflow_numeric C.jet_secp_scalar_reduce_numeric.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_sx_forget_cells C.jet_sx_revalue_cells
  C.jet_secp_scalar_reduce512_run C.jet_secp_reduce512_typed_stage
  C.jet_secp_reduce512_checkpoint C.jet_secp_reduce512_third_stage
  C.jet_secp_reduce512_third_atomic C.jet_secp_reduce512_third_exec
  C.jet_secp_reduce512_third_value C.jet_secp_reduce512_wide
  C.jet_secp_reduce512_final_stage C.jet_secp_reduce512_final_atomic
  C.jet_secp_reduce512_final_value C.jet_secp_scalar_mul512_accumulate
  C.jet_secp_scalar_mul512_symbolic C.jet_secp_reduce512_fold_bounds.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition third_checkpoint_digits (digits : nat -> int64) p4 n :=
  match n with
  | 0%nat => wlo (third_ma0 digits p4) | 1%nat => wlo (third_ma1 digits p4)
  | 2%nat => wlo (third_ma2 digits p4) | 3%nat => wlo (third_ma3 digits p4)
  | _ => Int64.zero end.
Definition third_checkpoint_c digits p4 := whi (third_ma3 digits p4).
Lemma third_checkpoint_limb_value digits p4 :
  scalar_limb_value (third_checkpoint_digits digits p4) = column_words_value (third_machine_outputs digits p4).
Proof.
  unfold scalar_limb_value,third_machine_outputs; cbn [third_checkpoint_digits column_words_value].
  change Int64.modulus with 18446744073709551616.
  change (2 ^ 64) with 18446744073709551616.
  change (2 ^ 128) with 340282366920938463463374607431768211456.
  change (2 ^ 192) with 6277101735386680763835789423207666416102355444464034512896.
  ring.
Qed.
Lemma third_checkpoint_value digits p4 : Int.unsigned p4 <= 2 ->
  final_untruncated (third_checkpoint_digits digits p4) (third_checkpoint_c digits p4) = third_fold_value digits p4.
Proof.
  intro H; unfold final_untruncated; rewrite third_checkpoint_limb_value; apply third_reconstruction; exact H.
Qed.
Lemma third_checkpoint_final_numeric digits p4 rho beta : Int.unsigned p4 <= 2 ->
  final_output_value (third_checkpoint_digits digits p4) (third_checkpoint_c digits p4) rho beta =
    third_fold_value digits p4 mod canonical_group_order.
Proof.
  intro H; rewrite final_suffix_numeric.
  - rewrite third_checkpoint_value by exact H; reflexivity.
  - exact (proj2 (third_c_bound digits p4 H)).
  - rewrite third_checkpoint_value by exact H; exact (proj2 (third_fold_bound digits p4 H)).
Qed.
Lemma third_checkpoint_forget_stack digits p4 :
  forget_after 2 (sregs (reduce512_third_state digits p4)) =
    mkreg (u64_cells 0 (reduce512_third_limbs digits p4)) true (Some 32) ::
      (tl scalar_reduce512_initial_regs ++ fst reduce512_allocated).
Proof. Timeout 10 vm_compute; reflexivity. Qed.
Lemma third_checkpoint_param_sources digits p4 :
  (stemps (reduce512_third_state digits p4))!_r = Some (XP 0 0) /\
  (stemps (reduce512_third_state digits p4))!_l = Some (XP 1 0).
Proof. Timeout 10 (split; reflexivity). Qed.
Local Opaque reduce512_third_state reduce512_allocated.
Theorem third_checkpoint_rep digits p4 rho beta m :
  rep rho beta (sregs (reduce512_third_state digits p4)) m ->
  rep rho beta (reduce512_final_regs (third_checkpoint_digits digits p4)) m.
Proof.
  intro HR; pose proof (rep_forget_after rho beta _ m 2 HR) as HF.
  rewrite third_checkpoint_forget_stack in HF.
  pose proof (rep_region rho beta _ m 0 _ HF eq_refl) as HO.
  pose proof (region_ok_revalue_u64 rho beta m 0 (reduce512_third_limbs digits p4) true (Some 32)
    HO (reduce512_third_limb_kinds digits p4)) as Hnew.
  pose proof (revalue_region_shape (revalue_u64 rho beta)
    (mkreg (u64_cells 0 (reduce512_third_limbs digits p4)) true (Some 32))) as HS.
  unfold revalue_region in HS; cbn [rcells rw rfree] in HS; rewrite revalue_u64_cells in HS.
  pose proof (rep_change_head rho beta _ _ _ m HS Hnew HF) as Hresult.
  destruct (third_outputs_machine digits p4 rho (lay beta)) as [HM _].
  rewrite (revalue_u64_machine_map rho beta _ _ HM) in Hresult.
  exact Hresult.
Qed.
Theorem third_checkpoint_tmatch digits p4 rho beta le :
  tmatch rho beta (stemps (reduce512_third_state digits p4)) le ->
  tmatch rho beta (reduce512_final_temps (third_checkpoint_c digits p4)) le.
Proof.
  intro HT; destruct (third_checkpoint_param_sources digits p4) as [SR SL].
  pose proof (HT _ _ SR) as LR; pose proof (HT _ _ SL) as LL.
  pose proof (HT _ _ (third_raw_c digits p4)) as LC.
  destruct (third_columns_rep digits p4 rho (lay beta)) as (_ & _ & _ & _ & HC & _); rewrite HC in LC.
  unfold reduce512_final_temps.
  apply tmatch_checkpoint_set; [|exact LC].
  apply tmatch_checkpoint_set; [|exact LL].
  apply tmatch_checkpoint_set; [|exact LR].
  intros id x HX; rewrite PTree.gempty in HX; discriminate.
Qed.
