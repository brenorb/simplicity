(** Denotation-preserving checkpoint compression of BOTH cells and temporaries.
    No memory is changed and no arithmetic fact is assumed. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Maps Memory Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_revalue_cells.
Import ListNotations.
Set Default Timeout 10.

Definition atomic_sx rho beta x := if isk KL x then revalue_u64 rho beta x else x.
Lemma atomic_sx_den rho beta x : den rho (lay beta) (atomic_sx rho beta x) = den rho (lay beta) x.
Proof.
  unfold atomic_sx. destruct (isk KL x) eqn:HK; [|reflexivity].
  exact (proj1 (revalue_u64_den rho beta 0 x HK)).
Qed.
Lemma atomic_sx_xp rho beta r x : xp_le r x = true -> xp_le r (atomic_sx rho beta x) = true.
Proof. intro H; unfold atomic_sx; destruct (isk KL x); [reflexivity|exact H]. Qed.

Lemma atomic_region rho beta m r reg : region_ok rho beta m r reg ->
  region_ok rho beta m r (revalue_region (atomic_sx rho beta) reg).
Proof.
  intro HR; eapply region_ok_revalue; [exact HR|].
  intros c x HIn HV; split; [apply atomic_sx_den|].
  destruct HR as (_ & _ & _ & HC & _).
  rewrite Forall_forall in HC; specialize (HC c HIn).
  destruct HC as (_ & _ & _ & HX).
  apply atomic_sx_xp; exact (proj2 (HX x HV)).
Qed.

Definition atomic_regs rho beta regs := map (revalue_region (atomic_sx rho beta)) regs.
Lemma atomic_regs_shape rho beta regs : map rshape (atomic_regs rho beta regs) = map rshape regs.
Proof.
  unfold atomic_regs; rewrite map_map; apply map_ext; intro reg; apply revalue_region_shape.
Qed.
Lemma atomic_rep rho beta regs m : rep rho beta regs m -> rep rho beta (atomic_regs rho beta regs) m.
Proof.
  intros (HL & HS & HR); split.
  - unfold atomic_regs; rewrite map_length; exact HL.
  - split.
    + eapply rsep_shape; [apply atomic_regs_shape|exact HS].
    + intros r reg HN; unfold atomic_regs in HN; rewrite nth_error_map in HN.
      destruct (nth_error regs r) as [old|] eqn:HO; [|discriminate].
      cbn [option_map] in HN; injection HN as HE; subst reg.
      apply atomic_region; exact (HR r old HO).
Qed.

Definition atomic_temps rho beta ts := PTree.map (fun _ x => atomic_sx rho beta x) ts.
Lemma atomic_tmatch rho beta ts le : tmatch rho beta ts le -> tmatch rho beta (atomic_temps rho beta ts) le.
Proof.
  intros HT id x HX; unfold atomic_temps in HX; rewrite PTree.gmap in HX.
  destruct (ts!id) as [old|] eqn:HO; [|discriminate].
  cbn [option_map] in HX; injection HX as HE; subst x.
  rewrite atomic_sx_den; exact (HT id old HO).
Qed.

Definition atomic_state rho beta st := mkst (atomic_temps rho beta (stemps st))
  (atomic_regs rho beta (sregs st)) (slog st) (snv st).
Theorem atomic_checkpoint rho beta st le m :
  rep rho beta (sregs st) m -> tmatch rho beta (stemps st) le ->
  rep rho beta (sregs (atomic_state rho beta st)) m /\
  tmatch rho beta (stemps (atomic_state rho beta st)) le /\
  map rshape (sregs (atomic_state rho beta st)) = map rshape (sregs st) /\
  slog (atomic_state rho beta st) = slog st /\ snv (atomic_state rho beta st) = snv st.
Proof.
  intros HR HT; split; [apply atomic_rep; exact HR|]; split; [apply atomic_tmatch; exact HT|];
    split; [apply atomic_regs_shape|]; split; reflexivity.
Qed.
