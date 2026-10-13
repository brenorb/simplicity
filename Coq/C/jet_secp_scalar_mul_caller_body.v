(** Whole original scalar_mul body with the public multiply jet's r=a alias.
    Call executions and product-to-reduction representation are discharged. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Maps Memory Events Globalenvs.
From compcert Require Import Clightdefs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_mul512_fresh C.jet_secp_scalar_mul512_low
  C.jet_secp_product_reduce_bridge C.jet_secp_reduce512_function_numeric
  C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_body_numeric.
Require Import C.jet_secp_scalar_reduce512_run.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition scalar_mul_caller_env beta : env :=
  PTree.set _l (blk beta 0, tarray tulong 8) empty_env.
Definition scalar_mul_product_stmt :=
  match fn_body f_secp256k1_scalar_mul with Ssequence a _ => a | _ => Sskip end.
Definition scalar_mul_reduction_stmt :=
  match fn_body f_secp256k1_scalar_mul with Ssequence _ b => b | _ => Sskip end.
Lemma scalar_mul_caller_source : fn_body f_secp256k1_scalar_mul =
  Ssequence scalar_mul_product_stmt scalar_mul_reduction_stmt.
Proof. reflexivity. Qed.
Lemma scalar_mul_product_linkage :
  Genv.find_symbol secp_ge _secp256k1_scalar_mul_512 = Some (secp_symbol_block _secp256k1_scalar_mul_512) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_scalar_mul_512) Ptrofs.zero) =
    Some (Internal f_secp256k1_scalar_mul_512).
Proof. Timeout 10 (vm_compute; split; reflexivity). Qed.
Lemma scalar_mul_reduction_linkage :
  Genv.find_symbol secp_ge _secp256k1_scalar_reduce_512 = Some (secp_symbol_block _secp256k1_scalar_reduce_512) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_scalar_reduce_512) Ptrofs.zero) =
    Some (Internal f_secp256k1_scalar_reduce_512).
Proof. Timeout 10 (vm_compute; split; reflexivity). Qed.
Local Opaque secp_ge.
Lemma exec_scalar_mul_product_call beta le m mf :
  le!_a = Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
  le!_b = Some (Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))) ->
  bas beta 0 = 0 ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul_512)
    [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
     Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
     Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (scalar_mul_caller_env beta) le m scalar_mul_product_stmt E0 le mf Out_normal.
Proof.
  intros HA HB H0 HC; destruct scalar_mul_product_linkage as [HS HF].
  rewrite H0 in HC.
  eapply exec_Scall with (vf := Vptr (secp_symbol_block _secp256k1_scalar_mul_512) Ptrofs.zero)
    (vargs := [Vptr (blk beta 0) Ptrofs.zero;
      Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
      Vptr (blk beta 2) (Ptrofs.repr (bas beta 2))])
    (f := Internal f_secp256k1_scalar_mul_512) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Elvalue.
      * eapply eval_Evar_local; reflexivity.
      * apply deref_loc_reference; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Etempvar; exact HA.
      * reflexivity.
      * eapply eval_Econs.
        -- apply eval_Etempvar; exact HB.
        -- reflexivity.
        -- apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.
Lemma exec_scalar_mul_reduction_call beta le m mf :
  le!_r = Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
  bas beta 0 = 0 ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_reduce_512)
    [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1));
     Vptr (blk beta 0) (Ptrofs.repr (bas beta 0))] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (scalar_mul_caller_env beta) le m scalar_mul_reduction_stmt E0 le mf Out_normal.
Proof.
  intros HR H0 HC; destruct scalar_mul_reduction_linkage as [HS HF].
  rewrite H0 in HC.
  eapply exec_Scall with (vf := Vptr (secp_symbol_block _secp256k1_scalar_reduce_512) Ptrofs.zero)
    (vargs := [Vptr (blk beta 1) (Ptrofs.repr (bas beta 1)); Vptr (blk beta 0) Ptrofs.zero])
    (f := Internal f_secp256k1_scalar_reduce_512) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HR.
    + reflexivity.
    + eapply eval_Econs.
      * eapply eval_Elvalue.
        -- eapply eval_Evar_local; reflexivity.
        -- apply deref_loc_reference; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HC.
Qed.
Theorem exec_scalar_mul_caller_body_inplace rho beta le m :
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
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul512_fresh_regs) b ofs) m mf.
Proof.
  intros HR LR LA LB.
  pose proof (rep_region rho beta _ m 0 _ HR eq_refl) as H0.
  destruct H0 as (_ & _ & _ & _ & Hfree); destruct Hfree as (Hbase & _).
  destruct (eval_product_then_reduce rho beta m HR) as (mp & mf & HP & HC & Hout & Hvalue & HFP & HFR).
  exists mf; split.
  - rewrite scalar_mul_caller_source.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mp).
    + eapply exec_scalar_mul_product_call; eassumption.
    + eapply exec_scalar_mul_reduction_call; eassumption.
  - split; [exact Hout|]. split; [exact Hvalue|].
    eapply lframe_trans; [exact HFP|].
    eapply lframe_implies; [exact HFR|].
    intros b ofs Houtfoot Hv Hinfoot; apply Houtfoot; eapply product_reduce_foot_embed; exact Hinfoot.
Qed.
