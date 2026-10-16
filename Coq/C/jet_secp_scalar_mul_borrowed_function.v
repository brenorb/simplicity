(** Complete original scalar_mul r=a call, with a non-owned readable rhs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem
  C.jet_secp_linkage C.jets_secp C.jet_secp_canonical_scalar
  C.jet_secp_scalar_mul_caller_alloc C.jet_secp_scalar_mul_caller_body
  C.jet_secp_scalar_mul_caller_function C.jet_secp_product_reduce_bridge
  C.jet_secp_scalar_mul512_low C.jet_secp_scalar_reduce512_run
  C.jet_secp_reduce512_function_numeric C.jet_secp_reduce512_body_numeric
  C.jet_secp_reduce512_final_atomic C.jet_secp_reduce512_final_stage C.jet_sx_u64_transport.
Require Import C.jet_secp_scalar_mul512_borrowed C.jet_secp_scalar_mul_borrowed_body
  C.jet_secp_scalar_mul_borrowed_alloc.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition scalar_mul_borrowed_rhs := mkreg (u64_cells 0 [XLv 4;XLv 5;XLv 6;XLv 7]) false None.
Lemma borrowed_stack_foot_cases beta bl b ofs :
  foot (scalar_mul_stack_layout beta bl) (map rshape scalar_mul512_borrowed_regs) b ofs ->
  b = bl \/ foot beta (map rshape scalar_mul_borrowed_inputs) b ofs.
Proof.
  intros (r & sh & d & ch & HS & Hin & HB & Hr); destruct r as [|r].
  - left; exact HB.
  - right; exists r,sh,d,ch; exact (conj HS (conj Hin (conj HB Hr))).
Qed.
Lemma borrowed_rhs_unstack rho beta bl m :
  region_ok rho (scalar_mul_stack_layout beta bl) m 2 scalar_mul_borrowed_rhs ->
  region_ok rho beta m 1 scalar_mul_borrowed_rhs.
Proof.
  intro HR; eapply region_u64_transport with (rho := rho)
    (beta := scalar_mul_stack_layout beta bl) (r := 2%nat)
    (xs := [XLv 4;XLv 5;XLv 6;XLv 7]) (ys := [XLv 4;XLv 5;XLv 6;XLv 7])
    (w := false) (owned := None).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - exact HR.
Qed.

Theorem eval_scalar_mul_borrowed_inplace rho beta m :
  rep rho beta scalar_mul_borrowed_inputs m ->
  exists mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
      [Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 0) (Ptrofs.repr (bas beta 0));
       Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))] E0 mf Vundef /\
    rep (product_reduce_rho rho) [lay beta 0] (scalar_mul_caller_output rho) mf /\
    final_output_value (reduce512_body_digits (product_reduce_rho rho))
      (reduce512_body_carry (product_reduce_rho rho)) (product_reduce_rho rho) (lay [lay beta 0]) =
      (scalar_mul512_input_value rho 0 * scalar_mul512_input_value rho 4) mod canonical_group_order /\
    region_ok rho beta mf 1 scalar_mul_borrowed_rhs /\
    lframe (fun b ofs => ~ foot beta (map rshape scalar_mul_borrowed_inputs) b ofs) m mf.
Proof.
  intro HR; destruct (Mem.alloc m 0 64) as [ma bl] eqn:HA.
  pose proof (scalar_mul_borrowed_allocates rho beta m ma bl HR HA) as HRa.
  destruct (scalar_mul_caller_params_match beta bl) as (LR & LA & LB).
  destruct (exec_scalar_mul_borrowed_body rho (scalar_mul_stack_layout beta bl)
    (scalar_mul_caller_temps beta) ma HRa LR LA LB) as (mb & HB & HRb & HV & HBR & HFb).
  pose proof (rep_region (product_reduce_rho rho) _ _ mb 1 _ HRb eq_refl)
    as (_ & _ & _ & _ & Howned).
  assert (HPfree : Mem.range_perm mb bl 0 64 Cur Freeable) by exact (proj1 (proj2 (proj2 Howned))).
  destruct (free_list_exists [(bl,0,64)] mb) as (mf & Hfree & HUF).
  { constructor; [cbn; tauto|constructor]. }
  { intros b lo hi [E|[]]; inversion E; subst; exact HPfree. }
  assert (Hfresh : ~ Mem.valid_block m bl) by (eapply Mem.fresh_block_alloc; exact HA).
  assert (Hneq : forall r, (r < 2)%nat -> blk beta r <> bl).
  { intros r Hr E; apply Hfresh; rewrite <- E.
    apply (scalar_mul_borrowed_inputs_valid rho beta m HR); apply blk_in.
    destruct HR as (HL & _); change (length beta = 2%nat) in HL; lia. }
  assert (HRprefix : rep (product_reduce_rho rho) [lay beta 0] (scalar_mul_caller_output rho) mb).
  { eapply rep_prefix with (βN := [(bl,0)]) (regsN := tl scalar_reduce512_initial_regs).
    - exact HRb.
    - reflexivity. }
  assert (HRfinal : rep (product_reduce_rho rho) [lay beta 0] (scalar_mul_caller_output rho) mf).
  { eapply rep_mem; [|exact HRprefix]; eapply Mem.unchanged_on_implies; [exact HUF|].
    intros b ofs Hin Hv [E|[]]; cbn [map In] in Hin; destruct Hin as [Eb|[]]; subst b.
    apply (Hneq 0%nat ltac:(lia)); symmetry; exact E. }
  assert (HBRfinal : region_ok rho beta mf 1 scalar_mul_borrowed_rhs).
  { apply (borrowed_rhs_unstack rho beta bl mf).
    eapply region_ok_mem; [|exact HBR]; eapply Mem.unchanged_on_implies; [exact HUF|].
    intros b ofs E Hv [H|[]]; subst b.
    apply (Hneq 1%nat ltac:(lia)); symmetry; exact H. }
  exists mf; split.
  - eapply eval_funcall_internal.
    + apply scalar_mul_caller_entry; exact HA.
    + exact HB.
    + constructor.
    + rewrite scalar_mul_caller_env_blocks; exact Hfree.
  - split; [exact HRfinal|]. split.
    + rewrite <- (scalar_mul_output_layout_indep (reduce512_body_digits (product_reduce_rho rho))
        (reduce512_body_carry (product_reduce_rho rho)) (product_reduce_rho rho)
        (lay (product_reduce_layout (scalar_mul_stack_layout beta bl))) (lay [lay beta 0])); exact HV.
    + split; [exact HBRfinal|].
      eapply lframe_implies with (P := fun b ofs => Mem.valid_block m b /\
        ~ foot beta (map rshape scalar_mul_borrowed_inputs) b ofs).
      2: { intros b ofs Hf Hvb; split; assumption. }
      eapply lframe_trans.
      { apply lframe_unchanged; eapply Mem.unchanged_on_implies;
          [eapply Mem.alloc_unchanged_on; exact HA|]; intros; exact I. }
      eapply lframe_trans.
      { eapply lframe_implies; [exact HFb|].
        intros b ofs (Hvb & Hf) HvA Hfoot.
        destruct (borrowed_stack_foot_cases beta bl b ofs Hfoot) as [E|Hin].
        - subst b; exact (Hfresh Hvb).
        - exact (Hf Hin). }
      apply lframe_unchanged; eapply Mem.unchanged_on_implies; [exact HUF|].
      intros b ofs (Hvb & Hf) HvB [E|[]]; subst b; exact (Hfresh Hvb).
Qed.
