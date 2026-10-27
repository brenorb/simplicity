(** [ctz_model] is consistent with CompCert's axioms on external functions.

    As for [memcpy_model], a premise about the abstract parameter
    [external_functions_sem] could contradict [external_functions_properties]
    and make every theorem that assumes it vacuous. This module exhibits an
    assignment of semantics to all external functions satisfying
    [extcall_properties] for every name and signature, under which the
    statement of [ctz_model] holds. It is a relative-consistency result; it
    does not discharge [ctz_model]. *)
From Coq Require Import ZArith List Lia String.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs Builtins0.
Require Import C.extraMath C.jet_ctz_model C.jet_memcpy_model_consistent.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition ctz_value (x : int64) : option int :=
  if Int64.eq x Int64.zero then None else Some (Int.repr (Z_ctz (Int64.unsigned x))).

Definition ctz_builtin : builtin_sem (Tret AST.Tint) :=
  mkbuiltin_n1p AST.Tlong (Tret AST.Tint) ctz_value.

(** The builtin contract as a pure external-call semantics. *)
Inductive libc_ctz_sem (ge : Senv.t) : list val -> mem -> trace -> val -> mem -> Prop :=
| libc_ctz_sem_intro : forall vargs vres m,
    bs_sem _ ctz_builtin vargs = Some vres -> libc_ctz_sem ge vargs m E0 vres m.

(** Same proof as CompCert's [known_builtin_ok], for this builtin. *)
Lemma libc_ctz_sem_ok : extcall_properties libc_ctz_sem ctz_sig.
Proof.
  set (bsem := ctz_builtin). constructor; intros.
  - inv H. specialize (bs_well_typed _ bsem vargs).
    unfold val_opt_has_rettype, bsem; rewrite H0. auto.
  - inv H0. econstructor; eauto.
  - inv H; auto.
  - inv H; auto.
  - inv H; auto.
  - inv H. fold bsem in H2. apply val_inject_list_lessdef in H1.
    specialize (bs_inject _ bsem _ _ _ H1).
    unfold val_opt_inject; rewrite H2; intros.
    destruct (bsem vargs') as [vres'|] eqn:?; try contradiction.
    exists vres', m1'; intuition auto using Mem.extends_refl, Mem.unchanged_on_refl.
    constructor; auto.
    apply val_inject_lessdef; auto.
  - inv H0. fold bsem in H3.
    specialize (bs_inject _ bsem _ _ _ H2).
    unfold val_opt_inject; rewrite H3; intros.
    destruct (bsem vargs') as [vres'|] eqn:?; try contradiction.
    exists f, vres', m1'; intuition auto using Mem.extends_refl, Mem.unchanged_on_refl.
    constructor; auto.
    red; intros; congruence.
  - inv H; simpl; lia.
  - inv H; inv H0. exists vres1, m1; constructor; auto.
  - inv H; inv H0.
    split. constructor. intuition congruence.
Qed.

Lemma libc_ctz_sem_models : ctz_model_for libc_ctz_sem.
Proof.
  unfold ctz_model_for; intros ge m x Nonzero. constructor.
  cbn. unfold ctz_value.
  destruct (Int64.eq x Int64.zero) eqn:Zero;[|reflexivity].
  apply Int64.same_if_eq in Zero;subst x;contradiction.
Qed.

(** Model existence: an assignment of semantics to every external function
    that satisfies CompCert's required properties and the ctz model. *)
Theorem ctz_model_consistent :
  exists S : string -> signature -> extcall_sem,
    (forall id sg, extcall_properties (S id sg) sg) /\
    ctz_model_for (S "__builtin_ctzl"%string ctz_sig).
Proof.
  exists (fun id sg =>
    if string_dec id "__builtin_ctzl" then
      if signature_eq sg ctz_sig then libc_ctz_sem else no_behaviour
    else no_behaviour).
  split.
  - intros id sg. destruct (string_dec id "__builtin_ctzl"); [|apply no_behaviour_ok].
    destruct (signature_eq sg ctz_sig) as [->|]; [|apply no_behaviour_ok].
    exact libc_ctz_sem_ok.
  - cbn. destruct (signature_eq ctz_sig ctz_sig) as [_|N]; [|contradiction].
    exact libc_ctz_sem_models.
Qed.
