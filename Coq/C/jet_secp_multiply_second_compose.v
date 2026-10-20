(** Compose the original first two slices with every boundary premise derived. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage.
Require Import C.jet_secp_statement_prefix.
Require Import C.jet_secp_multiply_checkpoint_prefix C.jet_secp_multiply_checkpoint_atomic C.jet_secp_multiply_checkpoint_bridge.
Require Import C.jet_secp_multiply_second_state C.jet_secp_multiply_second_entry C.jet_secp_multiply_second_machine.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma second_initial_shape digits c d t3 :
  map rshape (sregs (second_initial digits c d t3)) = map rshape (sregs prefix_initial).
Proof. Timeout 10 reflexivity. Qed.

Definition composed_second_state rho := second_state rho (first_final_c_machine rho)
  (first_final_d_machine rho) (first_t3_machine rho).
Definition composed_second_observations rho beta le m := second_observations rho (first_final_c_machine rho)
  (first_final_d_machine rho) (first_t3_machine rho) beta le m.

Local Opaque xstmt prefix_state prefix_initial second_state.
Theorem exec_original_through_second rho beta e le m :
  rep rho beta (sregs prefix_initial) m -> tmatch rho beta (stemps prefix_initial) le ->
  ematch beta (snd mul_allocated) e ->
  exists le' mf,
    Clight2.exec_stmt secp_ge e le m through_second E0 le' mf Out_normal /\
    composed_second_observations rho beta le' mf /\
    rep rho beta (sregs (atomic_state rho beta (composed_second_state rho))) mf /\
    tmatch rho beta (stemps (atomic_state rho beta (composed_second_state rho))) le' /\
    lframe (fun b ofs => ~ foot beta (map rshape (sregs prefix_initial)) b ofs) m mf.
Proof.
  intros HR HT HE.
  destruct (exec_first_machine_atomic rho beta e le m HR HT HE)
    as (le1 & m1 & HX1 & HM1 & HR1 & HT1 & HF1).
  assert (HR2 : rep rho beta (sregs (second_initial rho (first_final_c_machine rho)
      (first_final_d_machine rho) (first_t3_machine rho))) m1).
  { change (rep rho beta (second_regs rho (first_final_c_machine rho) (first_final_d_machine rho)) m1).
    rewrite <- (first_atomic_regs_exact rho beta); exact HR1. }
  assert (HT2 : tmatch rho beta (stemps (second_initial rho (first_final_c_machine rho)
      (first_final_d_machine rho) (first_t3_machine rho))) le1).
  { apply first_to_second_tmatch; exact HT1. }
  destruct (exec_second_machine_atomic rho (first_final_c_machine rho) (first_final_d_machine rho)
      (first_t3_machine rho) rho beta e le1 m1 HR2 HT2 HE)
    as (le2 & m2 & HX2 & HM2 & HR3 & HT3 & HF2).
  exists le2, m2; split.
  - rewrite <- first_second_source.
    eapply exec_statement_prefix_then_last; [exact HX1|exact HX2].
  - split; [exact HM2|]; split; [exact HR3|]; split; [exact HT3|].
    eapply lframe_trans; [exact HF1|]. rewrite second_initial_shape in HF2; exact HF2.
Qed.
