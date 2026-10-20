(** Build a partial live temporary relation from proved value bindings. *)
From Coq Require Import List.
From compcert Require Import Coqlib AST Maps Values.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval.
Import ListNotations.
Set Default Timeout 10.
Definition temps_of (xs : list (ident * sx)) := fold_right
  (fun p ts => PTree.set (fst p) (snd p) ts) (PTree.empty sx) xs.
Definition binding_actual rho beta le p := le!(fst p) = Some (den rho (lay beta) (snd p)).
Definition binding_values rho beta (xs : list (ident * sx)) := map (fun p => (fst p, den rho (lay beta) (snd p))) xs.

Lemma tmatch_set_live rho beta le id x ts :
  le!id = Some (den rho (lay beta) x) -> tmatch rho beta ts le ->
  tmatch rho beta (PTree.set id x ts) le.
Proof.
  intros HL HT j y HX; rewrite PTree.gsspec in HX.
  destruct (peq j id); [subst j; injection HX as HE; subst y; exact HL|exact (HT j y HX)].
Qed.
Lemma tmatch_bindings rho beta le xs :
  Forall (binding_actual rho beta le) xs -> tmatch rho beta (temps_of xs) le.
Proof.
  intro H; induction H as [|[id x] xs HX HF IH]; cbn [temps_of fold_right fst snd].
  - intros id x HX; rewrite PTree.gempty in HX; discriminate.
  - apply tmatch_set_live; [exact HX|exact IH].
Qed.
Lemma bindings_transfer rho beta le xs ys :
  Forall (binding_actual rho beta le) xs -> binding_values rho beta xs = binding_values rho beta ys ->
  Forall (binding_actual rho beta le) ys.
Proof.
  intros H HE.
  assert (HV : Forall (fun p => le!(fst p) = Some (snd p)) (binding_values rho beta xs)).
  { unfold binding_values; rewrite Forall_map; exact H. }
  rewrite HE in HV; unfold binding_values in HV; rewrite Forall_map in HV; exact HV.
Qed.
