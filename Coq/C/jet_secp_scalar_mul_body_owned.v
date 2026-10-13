(** Retain b's real post-product ownership through the actual reduction. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Values Memory Events Maps.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_eval.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_mul512_run C.jet_secp_scalar_mul512_fresh
  C.jet_secp_scalar_mul_caller_body C.jet_secp_product_reduce_bridge
  C.jet_secp_scalar_mul512_low C.jet_secp_scalar_reduce512_run
  C.jet_secp_reduce512_function_numeric C.jet_secp_reduce512_body_numeric
  C.jet_secp_reduce512_final_atomic.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_mul_second_disjoint rho beta m :
  rep rho beta (sregs scalar_mul512_state) m ->
  blk beta 2 <> blk beta 0 /\ blk beta 2 <> blk beta 1.
Proof.
  intro HR. rewrite scalar_mul512_output in HR. destruct HR as (_ & HS & _).
  pose proof (HS 2%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl) as H20.
  pose proof (HS 2%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl) as H21.
  destruct H20 as [H20|[H20 _]]; [|discriminate].
  destruct H21 as [H21|[H21 _]]; [|discriminate].
  exact (conj H20 H21).
Qed.

Lemma scalar_mul_second_after_reduce rho beta mp mf :
  rep rho beta (sregs scalar_mul512_state) mp ->
  lframe (fun b ofs => ~ foot (product_reduce_layout beta)
    (map rshape scalar_reduce512_initial_regs) b ofs) mp mf ->
  Mem.range_perm mf (blk beta 2) 0 32 Cur Freeable.
Proof.
  intros HR HF. destruct (scalar_mul_second_disjoint rho beta mp HR) as (H20 & H21).
  rewrite scalar_mul512_output in HR.
  pose proof (rep_region rho beta _ mp 2 _ HR eq_refl) as (_ & HV & _ & _ & HO).
  destruct HO as (_ & _ & HP & _).
  intros ofs HOfs. eapply (proj1 (proj2 HF)); [exact HV| |apply HP; exact HOfs].
  intros (r & sh & d & ch & HN & HI & HB & HT).
  destruct r as [|[|r]].
  - apply H21. exact HB.
  - apply H20. exact HB.
  - cbn [scalar_reduce512_initial_regs map nth_error] in HN. destruct r; discriminate.
Qed.

Theorem exec_scalar_mul_body_second_owned rho beta le m :
  rep rho beta scalar_mul512_fresh_regs m ->
  le!_r = Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
  le!_a = Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
  le!_b = Some (Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))) ->
  exists mf,
    Clight2.exec_stmt secp_ge (scalar_mul_caller_env beta) le m
      (fn_body f_secp256k1_scalar_mul) E0 le mf Out_normal /\
    rep (product_reduce_rho rho) (product_reduce_layout beta)
      (reduce512_numeric_owned_regs (product_reduce_rho rho)) mf /\
    final_output_value (reduce512_body_digits (product_reduce_rho rho))
      (reduce512_body_carry (product_reduce_rho rho))
      (product_reduce_rho rho) (lay (product_reduce_layout beta)) =
      (scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4) mod canonical_group_order /\
    Mem.range_perm mf (blk beta 2) 0 32 Cur Freeable /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul512_fresh_regs) b ofs) m mf.
Proof.
  intros HR LR LA LB.
  pose proof (rep_region rho beta _ m 0 _ HR eq_refl) as (_ & _ & _ & _ & HOwned).
  destruct HOwned as (Hbase & _).
  destruct (eval_scalar_mul512_fresh rho beta m HR) as (mp & HP & HRP & HFP).
  pose proof (product_reduce_entry_rep rho beta mp HRP) as HE.
  destruct (eval_reduce512_numeric_owned (product_reduce_rho rho)
    (product_reduce_layout beta) mp HE) as (mf & HC & Hout & Hvalue & HFR).
  pose proof (scalar_mul_second_after_reduce rho beta mp mf HRP HFR) as HSecond.
  rewrite product_reduce_integer in Hvalue.
  exists mf; split.
  - rewrite scalar_mul_caller_source.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mp).
    + eapply exec_scalar_mul_product_call; eassumption.
    + eapply exec_scalar_mul_reduction_call; eassumption.
  - split; [exact Hout|]. split; [exact Hvalue|]. split; [exact HSecond|].
    eapply lframe_trans; [exact HFP|].
    eapply lframe_implies; [exact HFR|].
    intros b ofs HF Hv Hfoot. apply HF. eapply product_reduce_foot_embed; exact Hfoot.
Qed.
