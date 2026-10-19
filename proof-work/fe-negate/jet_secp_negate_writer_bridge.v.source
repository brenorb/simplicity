(** Adapters from real negation storage to the shared original writer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep.
Require Import C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_local_regions.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_field_negate_values C.jet_secp_field_negate_normalize.
Require Import C.jet_secp_canonical_negate C.jet_secp_canonical_normalize.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma wide_field_initial_rep t0 t1 t2 t3 t4 rc m b :
  fe_at m b 0 [t0;t1;t2;t3;t4] -> Mem.range_perm m b 0 40 Cur Freeable ->
  rep (wide_fe_rho t0 t1 t2 t3 t4 rc) [(b,0)] local_write_initial_regs m.
Proof.
  intros (HB & HA & HM & HP & HL) HF.
  apply (rep_add _ [] [] m b 0); [apply rep_nil|cbn; tauto|].
  apply region_with_freeable.
  - apply region_u64; cbn [blk bas lay nth fst snd]; try assumption.
    + eapply Mem.perm_valid_block. apply (HP 0). lia.
    + intros i x HN. destruct (vars5_one_nth i x HN) as [HI ->].
      split; [|reflexivity].
      change (Mem.load Mint64 m b (0 + 8 * Z.of_nat i) =
        Some (Vlong (nth i [t0;t1;t2;t3;t4] Int64.zero))).
      apply HL. apply nth_error_nth'. exact HI.
  - reflexivity.
  - reflexivity.
  - exact HF.
  - apply field_cells_storage_size.
Qed.

Lemma wide_local_final_freeable rho b m bd base :
  rep rho [(b,0)]
    (sregs (fst (rsel rho (lay [(b,0)]) (local_write_result bd base)))) m ->
  Mem.range_perm m b 0 40 Cur Freeable.
Proof.
  intro HR.
  destruct (local_write_selected_storage rho (lay [(b,0)]) bd base) as [HL HF].
  destruct (rep_free_region rho [(b,0)] _ m 0 40 HR ltac:(rewrite HL; lia) HF)
    as [_ HFree]. exact HFree.
Qed.

Lemma wide_negate_output rho (x : Ty.tySem (Word 8)) :
  fe_limbs_ok (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)) ->
  fe_val (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat))
    (Int64.unsigned (rho 5%nat)) = @toZ (WordToZ 8) x ->
  @toZ (WordToZ 8) x < feP ->
  wide_fe_output (negate_value rho 0) (negate_value rho 1) (negate_value rho 2)
    (negate_value rho 3) (negate_value rho 4) = @canonical_fe_negate Alg.CoreFunSem x.
Proof.
  intros Hok HV Hlt. assert (HB := Hok). unfold fe_limbs_ok in HB.
  apply (toZ_injective (WordToZ 8)).
  rewrite wide_fe_output_value, canonical_fe_negate_numeric,
    canonical_field_order_matches_limb_model.
  rewrite (negate_value_unsigned rho 0 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 1 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 2 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 3 ltac:(lia) ltac:(cbn; lia)),
    (negate_value_unsigned rho 4 ltac:(lia) ltac:(cbn; lia)).
  match goal with |- _ = ?rhs =>
    change (fe_val (4 * (2^52 - feR) - Int64.unsigned (rho 1%nat))
      (4 * (2^52 - 1) - Int64.unsigned (rho 2%nat))
      (4 * (2^52 - 1) - Int64.unsigned (rho 3%nat))
      (4 * (2^52 - 1) - Int64.unsigned (rho 4%nat))
      (4 * (2^48 - 1) - Int64.unsigned (rho 5%nat)) mod feP = rhs)
  end.
  rewrite fe_negate_mod.
  - rewrite HV. reflexivity.
  - pose proof (fe_val_bound _ _ _ _ _ Hok). rewrite HV in *. lia.
Qed.
Print Assumptions wide_negate_output.
