(** Forgetting initialized values without losing ownership or permissions. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition forget_cell c := mkcell (cofs c) (cchunk c) None.
Definition forget_region reg := mkreg (map forget_cell (rcells reg)) (rw reg) (rfree reg).
Lemma forget_cells_sorted cs lo : cells_sorted lo (map forget_cell cs) = cells_sorted lo cs.
Proof. revert lo; induction cs; intro lo; cbn [map cells_sorted forget_cell cofs cchunk]; [reflexivity|rewrite IHcs; reflexivity]. Qed.
Lemma forget_region_shape reg : rshape (forget_region reg) = rshape reg.
Proof.
  unfold rshape,forget_region; cbn [rcells rw rfree]; rewrite map_map.
  assert (HS : map (fun x => cshape (forget_cell x)) (rcells reg) = map cshape (rcells reg))
    by (apply map_ext; intro x; reflexivity).
  rewrite HS.
  reflexivity.
Qed.
Fixpoint forget_after (n : nat) (regs : list region) : list region :=
  match regs,n with
  | [],_ => []
  | h::t,0%nat => forget_region h :: forget_after 0 t
  | h::t,S k => h :: forget_after k t end.
Lemma forget_after_length regs : forall n, length (forget_after n regs) = length regs.
Proof. induction regs; intro n; destruct n; cbn [forget_after length]; [reflexivity|reflexivity|rewrite IHregs; reflexivity|rewrite IHregs; reflexivity]. Qed.
Lemma forget_after_shape regs : forall n, map rshape (forget_after n regs) = map rshape regs.
Proof.
  induction regs; intro n; destruct n; cbn [forget_after map]; [reflexivity|reflexivity| |].
  - rewrite forget_region_shape,IHregs; reflexivity.
  - rewrite IHregs; reflexivity.
Qed.
Lemma forget_after_lookup regs : forall n i reg,
  nth_error (forget_after n regs) i = Some reg ->
  exists old, nth_error regs i = Some old /\ (reg = old \/ reg = forget_region old).
Proof.
  induction regs as [|h t IH]; intros n i reg HX; destruct n,i; cbn [forget_after nth_error] in HX |- *;
    try discriminate.
  - inversion HX; subst reg; exists h; auto.
  - exact (IH 0%nat i reg HX).
  - inversion HX; subst reg; exists h; auto.
  - exact (IH n i reg HX).
Qed.
Lemma forget_region_ok rho beta m r reg : region_ok rho beta m r reg ->
  region_ok rho beta m r (forget_region reg).
Proof.
  intros (HB & HV & HS & HC & HF).
  unfold region_ok,forget_region; cbn [rcells rw rfree].
  split; [exact HB|]. split; [exact HV|]. split; [rewrite forget_cells_sorted; exact HS|]. split.
  - apply Forall_map; eapply Forall_impl; [|exact HC]. intros c (HM & HA & HP & HX).
    unfold cell_ok,forget_cell; cbn [cofs cchunk cval].
    split; [exact HM|]. split; [exact HA|]. split; [exact HP|]. intros x HH; discriminate.
  - destruct (rfree reg) as [sz|]; [|exact I].
    destruct HF as (H0 & HW & HP & Hsize).
    split; [exact H0|]. split; [exact HW|]. split; [exact HP|].
    apply Forall_map; exact Hsize.
Qed.
Lemma forget_regions_shape regs : map rshape (map forget_region regs) = map rshape regs.
Proof. rewrite map_map; apply map_ext; apply forget_region_shape. Qed.
Theorem rep_forget_cells rho beta regs m : rep rho beta regs m ->
  rep rho beta (map forget_region regs) m.
Proof.
  intros (HL & HS & HR); split; [rewrite map_length; exact HL|]. split.
  - apply rsep_shape with (regs := regs); [apply forget_regions_shape|exact HS].
  - intros r reg HX; rewrite nth_error_map in HX.
    destruct (nth_error regs r) as [old|] eqn:HO; [|discriminate].
    inversion HX; subst reg; apply forget_region_ok; exact (HR _ _ HO).
Qed.
Theorem rep_forget_after rho beta regs m n : rep rho beta regs m -> rep rho beta (forget_after n regs) m.
Proof.
  intros (HL & HS & HR); split; [rewrite forget_after_length; exact HL|]. split.
  - apply rsep_shape with (regs := regs); [apply forget_after_shape|exact HS].
  - intros r reg HX; destruct (forget_after_lookup regs n r reg HX) as (old & HO & [HE|HE]);
      rewrite HE; [exact (HR _ _ HO)|apply forget_region_ok; exact (HR _ _ HO)].
Qed.
