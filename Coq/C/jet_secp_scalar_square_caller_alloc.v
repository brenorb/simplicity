(** The real 64-byte scalar_mul stack allocation, from one owned scalar. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep
  Maps Memory Events Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem
  C.jet_secp_linkage C.jets_secp C.jet_secp_scalar_mul512_run
  C.jet_secp_scalar_mul512_fresh C.jet_secp_scalar_mul_caller_alloc
  C.jet_sx_u64_transport.
Require Import C.jet_secp_scalar_square512_run.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_square_caller_inputs :=
  [mkreg (u64_cells 0 [XLv 0; XLv 1; XLv 2; XLv 3]) true (Some 32)].

Lemma scalar_square_inputs_valid rho beta m :
  rep rho beta scalar_square_caller_inputs m ->
  forall b, In b (map fst beta) -> Mem.valid_block m b.
Proof.
  intros HR b Hin.
  assert (HL : length beta = 1%nat) by (destruct HR as (HL & _); exact HL).
  destruct beta as [|pa [|pb rest]]; cbn in HL; try discriminate.
  cbn [map In] in Hin; destruct Hin as [<-|[]].
  pose proof (rep_region rho _ _ m 0 _ HR eq_refl) as (_ & HV & _); exact HV.
Qed.

Lemma scalar_square_stack_rotate rho beta m bl :
  rep rho (beta ++ [(bl,0)])
    (scalar_square_caller_inputs ++ [mkreg scalar_mul_stack_cells true (Some 64)]) m ->
  length beta = 1%nat ->
  rep rho (scalar_mul_stack_layout beta bl) scalar_square512_regs m.
Proof.
  intros HR HL; destruct beta as [|pa [|pb rest]]; cbn in HL; try discriminate.
  destruct HR as (_ & HS & HC).
  unfold rep; split; [reflexivity|]. split.
  - intros r1 r2 reg1 reg2 Hne E1 E2.
    destruct r1 as [|[|r1]], r2 as [|[|r2]];
      cbn [scalar_square512_regs scalar_mul512_fresh_regs scalar_mul512_initial_regs
        nth_error hd tl] in E1,E2;
      try (destruct r1; discriminate E1); try (destruct r2; discriminate E2);
      try (exfalso; apply Hne; reflexivity); inversion E1; inversion E2; subst.
    + exact (HS 1%nat 0%nat _ _ ltac:(discriminate) eq_refl eq_refl).
    + exact (HS 0%nat 1%nat _ _ ltac:(discriminate) eq_refl eq_refl).
  - intros r reg E; destruct r as [|[|r]];
      cbn [scalar_square512_regs scalar_mul512_fresh_regs scalar_mul512_initial_regs
        nth_error hd tl] in E; try (destruct r; discriminate E); inversion E; subst reg.
    + apply scalar_mul_stack_cell_reindex with (beta := [pa;(bl,0)]) (r := 1%nat).
      * reflexivity.
      * exact (HC 1%nat _ eq_refl).
    + eapply region_u64_transport with (beta := [pa;(bl,0)]) (r := 0%nat)
        (rho := rho) (rho' := rho) (xs := [XLv 0;XLv 1;XLv 2;XLv 3])
        (ys := [XLv 0;XLv 1;XLv 2;XLv 3]) (w := true) (owned := Some 32).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * exact (HC 0%nat _ eq_refl).
Qed.

Theorem scalar_square_caller_allocates rho beta m ma bl :
  rep rho beta scalar_square_caller_inputs m ->
  Mem.alloc m 0 64 = (ma,bl) ->
  rep rho (scalar_mul_stack_layout beta bl) scalar_square512_regs ma.
Proof.
  intros HR HA.
  assert (HL : length beta = 1%nat) by (destruct HR as (HL & _); exact HL).
  assert (Hnew : ~ In bl (map fst beta)).
  { intro Hin. apply (Mem.fresh_block_alloc _ _ _ _ _ HA).
    exact (scalar_square_inputs_valid rho beta m HR bl Hin). }
  assert (HRA : rep rho beta scalar_square_caller_inputs ma).
  { eapply rep_mem; [|exact HR].
    eapply Mem.unchanged_on_implies; [eapply Mem.alloc_unchanged_on; exact HA|].
    intros; exact I. }
  apply scalar_square_stack_rotate; [|exact HL].
  apply rep_snoc; [exact HRA|exact Hnew| | |exact (proj1 scalar_mul_stack_cells_ok)|
    exact (proj2 scalar_mul_stack_cells_ok)|].
  - eapply Mem.valid_new_block; exact HA.
  - intros ofs Ho. eapply Mem.perm_alloc_2; [exact HA|exact Ho].
  - change (64 <= 18446744073709551615); lia.
Qed.
