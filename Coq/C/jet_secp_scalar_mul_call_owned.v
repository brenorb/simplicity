(** Complete original scalar_mul function, including r=a entry, fresh stack and free. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
From compcert Require Import Clightdefs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar.
Require Import C.jet_secp_scalar_mul512_run C.jet_secp_scalar_mul512_fresh
  C.jet_secp_scalar_mul_caller_body C.jet_secp_product_reduce_bridge
  C.jet_secp_reduce512_function_numeric C.jet_secp_reduce512_body_numeric
  C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_final_stage
  C.jet_secp_scalar_reduce512_run C.jet_secp_scalar_mul512_low.
Require Import C.jet_secp_scalar_mul_caller_alloc.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Require Import C.jet_secp_scalar_mul_caller_function C.jet_secp_scalar_mul_body_owned.

Theorem eval_scalar_mul_call_second_owned rho beta m :
  rep rho beta scalar_mul_caller_inputs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    rep (product_reduce_rho rho) [lay beta 0] (scalar_mul_caller_output rho) mf /\
    final_output_value (reduce512_body_digits (product_reduce_rho rho))
      (reduce512_body_carry (product_reduce_rho rho)) (product_reduce_rho rho)
      (lay [lay beta 0]) =
      (scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4) mod canonical_group_order /\
    Mem.range_perm mf (blk beta 1) 0 32 Cur Freeable /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul_caller_inputs) b ofs) m mf.
Proof.
  intro HR. destruct (Mem.alloc m 0 64) as [ma bl] eqn:HA.
  pose proof (scalar_mul_caller_allocates rho beta m ma bl HR HA) as HRa.
  destruct (scalar_mul_caller_params_match beta bl) as (LR & LA & LB).
  destruct (exec_scalar_mul_body_second_owned rho (scalar_mul_stack_layout beta bl)
    (scalar_mul_caller_temps beta) ma HRa LR LA LB) as (mb & HB & HRb & HV & HSecond & HFb).
  pose proof (rep_region (product_reduce_rho rho) _ _ mb 1 _ HRb eq_refl)
    as (_ & _ & _ & _ & Howned).
  assert (HPfree : Mem.range_perm mb bl 0 64 Cur Freeable) by exact (proj1 (proj2 (proj2 Howned))).
  destruct (free_list_exists [(bl,0,64)] mb) as (mf & Hfree & HUF).
  { constructor; [cbn; tauto|constructor]. }
  { intros b lo hi [E|[]]. inversion E; subst; exact HPfree. }
  assert (Hfresh : ~ Mem.valid_block m bl) by (eapply Mem.fresh_block_alloc; exact HA).
  assert (Hneq : blk beta 0 <> bl).
  { intro E. apply Hfresh. rewrite <- E.
    apply (scalar_mul_inputs_valid rho beta m HR).
    apply blk_in. destruct HR as (HL & _). change (length beta = 2%nat) in HL. lia. }
  assert (Hneq1 : blk beta 1 <> bl).
  { intro E. apply Hfresh. rewrite <- E.
    apply (scalar_mul_inputs_valid rho beta m HR).
    apply blk_in. destruct HR as (HL & _). change (length beta = 2%nat) in HL. lia. }
  assert (HSecondFinal : Mem.range_perm mf (blk beta 1) 0 32 Cur Freeable).
  { intros ofs HOfs. eapply Mem.perm_unchanged_on; [exact HUF| |exact (HSecond ofs HOfs)].
    intros [E|[]]. apply Hneq1. symmetry. exact E. }
  assert (HRprefix : rep (product_reduce_rho rho) [lay beta 0] (scalar_mul_caller_output rho) mb).
  { eapply rep_prefix with (βN := [(bl,0)])
      (regsN := tl scalar_reduce512_initial_regs).
    - exact HRb.
    - reflexivity. }
  assert (HRfinal : rep (product_reduce_rho rho) [lay beta 0] (scalar_mul_caller_output rho) mf).
  { eapply rep_mem; [|exact HRprefix].
    eapply Mem.unchanged_on_implies; [exact HUF|].
    intros b ofs Hin Hv [E|[]]. cbn [map In] in Hin.
    destruct Hin as [Eb|[]]. subst b. apply Hneq. symmetry. exact E. }
  exists mf; split.
  - eapply eval_funcall_internal.
    + apply scalar_mul_caller_entry. exact HA.
    + exact HB.
    + constructor.
    + rewrite scalar_mul_caller_env_blocks. exact Hfree.
  - split; [exact HRfinal|]. split.
    + rewrite <- (scalar_mul_output_layout_indep
        (reduce512_body_digits (product_reduce_rho rho))
        (reduce512_body_carry (product_reduce_rho rho)) (product_reduce_rho rho)
        (lay (product_reduce_layout (scalar_mul_stack_layout beta bl))) (lay [lay beta 0])).
      exact HV.
    + split; [exact HSecondFinal|].
      eapply lframe_implies with (P := fun b ofs => Mem.valid_block m b /\
        ~ foot beta (map rshape scalar_mul_caller_inputs) b ofs).
      2: { intros b ofs Hf Hvb; split; assumption. }
      eapply lframe_trans.
      { apply lframe_unchanged. eapply Mem.unchanged_on_implies;
          [eapply Mem.alloc_unchanged_on; exact HA|]. intros; exact I. }
      eapply lframe_trans.
      { eapply lframe_implies; [exact HFb|].
        intros b ofs (Hvb & Hf) HvA Hfoot.
        destruct (scalar_mul_stack_foot_cases beta bl b ofs Hfoot) as [E|Hin].
        - subst b. exact (Hfresh Hvb).
        - exact (Hf Hin). }
      apply lframe_unchanged. eapply Mem.unchanged_on_implies; [exact HUF|].
      intros b ofs (Hvb & Hf) HvB [E|[]]. subst b. exact (Hfresh Hvb).
Qed.
