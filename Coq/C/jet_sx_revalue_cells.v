(** Denotation-preserving cell compression, retaining memory, permissions and ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition revalue_cell (f : sx -> sx) c := mkcell (cofs c) (cchunk c) (option_map f (cval c)).
Definition revalue_region f reg := mkreg (map (revalue_cell f) (rcells reg)) (rw reg) (rfree reg).
Lemma revalue_cells_sorted f cs lo :
  cells_sorted lo (map (revalue_cell f) cs) = cells_sorted lo cs.
Proof. revert lo; induction cs; intro lo; cbn [map cells_sorted revalue_cell cofs cchunk]; [reflexivity|rewrite IHcs; reflexivity]. Qed.
Lemma revalue_region_shape f reg : rshape (revalue_region f reg) = rshape reg.
Proof.
  unfold rshape,revalue_region; cbn [rcells rw rfree]; rewrite map_map.
  assert (H : map (fun x => cshape (revalue_cell f x)) (rcells reg) = map cshape (rcells reg))
    by (apply map_ext; intro x; reflexivity).
  rewrite H; reflexivity.
Qed.
Lemma region_ok_revalue rho beta m r f reg :
  region_ok rho beta m r reg ->
  (forall c x, In c (rcells reg) -> cval c = Some x ->
    den rho (lay beta) (f x) = den rho (lay beta) x /\ xp_le r (f x) = true) ->
  region_ok rho beta m r (revalue_region f reg).
Proof.
  intros (HB & HV & HS & HC & HF) HE.
  unfold region_ok,revalue_region; cbn [rcells rw rfree].
  split; [exact HB|]. split; [exact HV|]. split; [rewrite revalue_cells_sorted; exact HS|]. split.
  - apply Forall_map; apply Forall_forall; intros c Hin.
    rewrite Forall_forall in HC; specialize (HC c Hin).
    destruct HC as (HM & HA & HP & HX).
    unfold cell_ok,revalue_cell; cbn [cofs cchunk cval].
    split; [exact HM|]. split; [exact HA|]. split; [exact HP|].
    intros y HY; destruct (cval c) as [x|] eqn:HVX; cbn [option_map] in HY; [|discriminate].
    inversion HY; subst y.
    destruct (HE c x Hin HVX) as [HD Hxp].
    destruct (HX x eq_refl) as [HL _]; rewrite HD; split; [exact HL|exact Hxp].
  - destruct (rfree reg) as [sz|]; [|exact I].
    destruct HF as (H0 & HW & HP & Hsz); split; [exact H0|]. split; [exact HW|]. split; [exact HP|].
    apply Forall_map; exact Hsz.
Qed.
Lemma rep_change_head rho beta old new rest m :
  rshape new = rshape old -> region_ok rho beta m 0 new ->
  rep rho beta (old :: rest) m -> rep rho beta (new :: rest) m.
Proof.
  intros HS Hnew (HL & Hsep & HR); split; [exact HL|]. split.
  - apply rsep_shape with (regs := old :: rest); [cbn [map]; rewrite HS; reflexivity|exact Hsep].
  - intros r reg H; destruct r; cbn [nth_error] in H.
    + inversion H; subst reg; exact Hnew.
    + exact (HR (S r) reg H).
Qed.
Definition revalue_u64 rho beta x := XL (il (den rho (lay beta) x)).
Lemma revalue_u64_den rho beta r x : isk KL x = true ->
  den rho (lay beta) (revalue_u64 rho beta x) = den rho (lay beta) x /\
  xp_le r (revalue_u64 rho beta x) = true.
Proof. intro H; split; [symmetry; apply den_KL; exact H|reflexivity]. Qed.
Require Import C.jet_sx_rep.
Lemma revalue_u64_cells f xs : forall ofs,
  map (revalue_cell f) (u64_cells ofs xs) = u64_cells ofs (map f xs).
Proof. induction xs; intro ofs; cbn [map revalue_cell cofs cchunk cval option_map u64_cells]; [reflexivity|rewrite IHxs; reflexivity]. Qed.
Lemma region_ok_revalue_u64 rho beta m r xs w owned :
  region_ok rho beta m r (mkreg (u64_cells 0 xs) w owned) ->
  forallb (isk KL) xs = true ->
  region_ok rho beta m r (mkreg (u64_cells 0 (map (revalue_u64 rho beta) xs)) w owned).
Proof.
  intros HR HK.
  pose proof (region_ok_revalue rho beta m r (revalue_u64 rho beta)
    (mkreg (u64_cells 0 xs) w owned) HR) as H.
  assert (HE : forall c x, In c (u64_cells 0 xs) -> cval c = Some x ->
    den rho (lay beta) (revalue_u64 rho beta x) = den rho (lay beta) x /\
    xp_le r (revalue_u64 rho beta x) = true).
  { intros c x Hin HX; destruct (u64_cells_In xs 0 c Hin) as (i & y & Hnth & ->).
    cbn [cval] in HX; inversion HX; subst y.
    apply revalue_u64_den; rewrite forallb_forall in HK; apply HK.
    apply nth_error_In with i; exact Hnth. }
  specialize (H HE).
  unfold revalue_region in H; cbn [rcells rw rfree] in H; rewrite revalue_u64_cells in H; exact H.
Qed.
Lemma revalue_u64_machine_map rho beta xs ys :
  map (den rho (lay beta)) xs = map Vlong ys ->
  map (revalue_u64 rho beta) xs = map XL ys.
Proof.
  intro H.
  pose proof (f_equal (map (fun v => XL (il v))) H) as HL.
  change (map (fun v => XL (il v)) (map (den rho (lay beta)) xs) =
    map (fun v => XL (il v)) (map Vlong ys)) in HL.
  rewrite !map_map in HL; exact HL.
Qed.
