(** Actual final overflow/reduction calls and current-memory result loads. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_frame.
Require Import C.jet_secp_compact_stmt_shift64 C.jet_secp_reduce512_typed_stage
  C.jet_secp_reduce512_final_stage.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Section TYPED.
Variable digits : nat -> int64.
Variable carry : int64.
Lemma final_output_region :
  nth_error (sregs (reduce512_final_state digits carry)) 0 =
    Some (mkreg (u64_cells 0 (reduce512_final_limbs digits carry)) true (Some 32)).
Proof. Timeout 10 reflexivity. Qed.
Local Opaque reduce512_final_state reduce512_allocated reduce512_final_suffix.
Theorem exec_typed_final_suffix rho beta e le m :
  rep rho beta (sregs (reduce512_final_initial digits carry)) m ->
  tmatch rho beta (reduce512_final_temps carry) le ->
  ematch beta (snd reduce512_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m reduce512_final_suffix E0 le' mf Out_normal /\
    rep rho beta (sregs (reduce512_final_state digits carry)) mf /\
    (forall i sy, nth_error (reduce512_final_limbs digits carry) i = Some sy ->
      Mem.load Mint64 mf (blk beta 0) (bas beta 0 + 8 * Z.of_nat i) = Some (den rho (lay beta) sy)) /\
    tmatch rho beta (stemps (reduce512_final_state digits carry)) le' /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs (reduce512_final_initial digits carry))) b ofs) m mf.
Proof.
  intros HR HT HE.
  destruct (compact_stmt_shift64_normal 300 (snd reduce512_allocated)
    (reduce512_final_initial digits carry) reduce512_final_suffix
    (reduce512_final_state digits carry) (reduce512_final_run_eq digits carry)
    rho beta e le m HR HT HE) as (le' & mf & Hex & Hrep & Htm & Hshape & Hframe).
  pose proof (rep_region rho beta _ mf 0 _ Hrep final_output_region) as Hregion.
  exists le',mf; split; [exact Hex|]. split; [exact Hrep|]. split.
  - intros i sy HS; pose proof (u64_cells_nth _ 0 i sy HS) as Hcell; rewrite Z.add_0_l in Hcell.
    exact (region_load rho beta mf 0 _ (8 * Z.of_nat i) Mint64 sy Hregion Hcell).
  - split; [exact Htm|exact Hframe].
Qed.
End TYPED.
