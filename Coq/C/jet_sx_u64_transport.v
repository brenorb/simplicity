(** Reindex initialized 64-bit regions using exact current-memory value maps. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma region_u64_transport rho rho' beta beta' m r r' xs ys w owned :
  lay beta' r' = lay beta r ->
  length ys = length xs ->
  map (den rho' (lay beta')) ys = map (den rho (lay beta)) xs ->
  forallb (xp_le r') ys = true ->
  region_ok rho beta m r (mkreg (u64_cells 0 xs) w owned) ->
  region_ok rho' beta' m r' (mkreg (u64_cells 0 ys) w owned).
Proof.
  intros HE HL HD HX (HB & HV & HS & HC & HF).
  assert (EB : blk beta' r' = blk beta r) by (unfold blk; rewrite HE; reflexivity).
  assert (ES : bas beta' r' = bas beta r) by (unfold bas; rewrite HE; reflexivity).
  unfold region_ok; cbn [rcells rw rfree]; rewrite EB,ES.
  split; [exact HB|]. split; [exact HV|]. split; [apply u64_cells_sorted; lia|]. split.
  - apply Forall_forall; intros c HY.
    destruct (u64_cells_In ys 0 c HY) as (i & y & Hny & ->); rewrite Z.add_0_l.
    assert (Hi : (i < length xs)%nat).
    { rewrite <- HL; apply nth_error_Some; congruence. }
    destruct (nth_error xs i) as [x|] eqn:Hnx.
    2: { apply nth_error_None in Hnx; lia. }
    pose proof (u64_cells_nth xs 0 i x Hnx) as Hin; rewrite Z.add_0_l in Hin.
    pose proof (proj1 (Forall_forall _ _) HC _ Hin) as (HM & HA & HP & HVX).
    unfold cell_ok; cbn [cofs cchunk cval]; rewrite EB,ES.
    split; [exact HM|]. split; [exact HA|]. split; [exact HP|].
    intros z Hz; inversion Hz; subst z.
    pose proof (f_equal (fun zs => nth_error zs i) HD) as Hdi.
    change (nth_error (map (den rho' (lay beta')) ys) i =
      nth_error (map (den rho (lay beta)) xs) i) in Hdi.
    rewrite !nth_error_map,Hny,Hnx in Hdi; cbn [option_map] in Hdi.
    injection Hdi as Hden.
    destruct (HVX x eq_refl) as [Hload _]; rewrite Hden.
    split; [exact Hload|rewrite forallb_forall in HX; apply HX; eapply nth_error_In; exact Hny].
  - destruct owned as [sz|]; [|exact I].
    destruct HF as (H0 & HW & HP & Hsize).
    split; [exact H0|]. split; [exact HW|]. split; [exact HP|].
    apply Forall_forall; intros c HY.
    destruct (u64_cells_In ys 0 c HY) as (i & y & Hny & ->).
    assert (Hi : (i < length xs)%nat).
    { rewrite <- HL; apply nth_error_Some; congruence. }
    destruct (nth_error xs i) as [x|] eqn:Hnx.
    2: { apply nth_error_None in Hnx; lia. }
    apply (proj1 (Forall_forall _ _) Hsize (mkcell (0 + 8 * Z.of_nat i) Mint64 (Some x))).
    exact (u64_cells_nth xs 0 i x Hnx).
Qed.
