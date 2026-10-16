(** Pointwise specification transport for the explicit contextual contract. *)
From Coq Require Import List.
From compcert Require Import Ctypes Clight Memory Values.
Require Import Simplicity.Ty.
Require Import C.jet_application_context_contract.

Lemma application_jet_bitmachine_spec_pointwise f ge (E : Set) (A B : Ty) env_rep (spec literal : A -> E -> option B) :
  (forall a environment, spec a environment = literal a environment) ->
  application_jet_bitmachine_spec f ge E A B env_rep spec ->
  application_jet_bitmachine_spec f ge E A B env_rep literal.
Proof.
  intros HE HS logical_env env m L s a tail fp HR HF HBM HSep HW HNext HSpace.
  destruct (HS logical_env env m L s a tail fp HR HF HBM HSep HW HNext HSpace)
    as (mf & value & HSpec & HCall & HResult).
  exists mf, value. split; [rewrite <- HE; exact HSpec|exact (conj HCall HResult)].
Qed.
