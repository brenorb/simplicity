(** Actual third-stage execution and current-memory output loads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame.
Require Import C.jet_secp_compact_stmt_shift64 C.jet_secp_scalar_reduce512_run
  C.jet_secp_reduce512_typed_stage C.jet_secp_reduce512_third_stage
  C.jet_secp_reduce512_third_atomic C.jet_secp_reduce512_wide
  C.jet_secp_scalar_mul512_symbolic.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Section TYPED.
Variable digits : nat -> int64.
Variable p4 : int.
Lemma third_output_region :
  nth_error (sregs (reduce512_third_state digits p4)) 0 =
    Some (mkreg (u64_cells 0 (reduce512_third_limbs digits p4)) true (Some 32)).
Proof. Timeout 10 reflexivity. Qed.
Lemma third_raw_c : (stemps (reduce512_third_state digits p4))!_c = Some (sc_hi (third_sy3 digits p4)).
Proof. Timeout 10 reflexivity. Qed.
Local Opaque reduce512_third_state reduce512_allocated reduce512_third_stage.
Theorem exec_typed_third_stage rho beta e le m :
  rep rho beta (sregs (reduce512_third_initial digits p4)) m ->
  tmatch rho beta (reduce512_third_temps digits p4) le ->
  ematch beta (snd reduce512_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m reduce512_third_stage E0 le' mf Out_normal /\
    rep rho beta (sregs (reduce512_third_state digits p4)) mf /\
    (forall i x, nth_error (third_machine_outputs digits p4) i = Some x ->
      Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8 * Z.of_nat i) = Some (Vlong x)) /\
    le'!_c = Some (Vlong (whi (third_ma3 digits p4))) /\
    tmatch rho beta (stemps (reduce512_third_state digits p4)) le' /\
    lframe (fun b ofs => ~ foot beta
      (map rshape (sregs (reduce512_third_initial digits p4))) b ofs) m mf.
Proof.
  intros HR HT HE.
  destruct (compact_stmt_shift64_normal 300 (snd reduce512_allocated)
    (reduce512_third_initial digits p4) reduce512_third_stage
    (reduce512_third_state digits p4) (reduce512_third_run_eq digits p4)
    rho beta e le m HR HT HE) as (le' & mf & Hex & Hrep & Htm & Hshape & Hframe).
  destruct (third_columns_rep digits p4 rho (lay beta)) as (_ & _ & _ & _ & HC & _).
  pose proof (Htm _ _ third_raw_c) as LC; rewrite HC in LC.
  pose proof (rep_region rho beta _ mf 0 _ Hrep third_output_region) as Hregion.
  destruct (third_outputs_machine digits p4 rho (lay beta)) as [HM _].
  exists le',mf; split; [exact Hex|]. split; [exact Hrep|]. split.
  - intros i x HX.
    pose proof (f_equal (fun xs => nth_error xs i) HM) as HI.
    change (nth_error (map (den rho (lay beta)) (reduce512_third_limbs digits p4)) i =
      nth_error (map Vlong (third_machine_outputs digits p4)) i) in HI.
    rewrite !nth_error_map,HX in HI; cbn [option_map] in HI.
    destruct (nth_error (reduce512_third_limbs digits p4) i) as [sy|] eqn:HS; [|discriminate].
    cbn [option_map] in HI; injection HI as HD.
    pose proof (u64_cells_nth _ 0 i sy HS) as Hcell; rewrite Z.add_0_l in Hcell.
    pose proof (region_load rho beta mf 0 _ (8 * Z.of_nat i) Mint64 sy Hregion Hcell) as HL.
    rewrite HD in HL; exact HL.
  - split; [exact LC|]. split; [exact Htm|exact Hframe].
Qed.
End TYPED.
