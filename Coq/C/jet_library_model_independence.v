(** The four library premises cannot be proved from the fixed target.

    [memcpy_model], [memset_model], [memcmp_model] and [ctz_model] are
    statements about [Events.external_functions_sem], an uninterpreted
    CompCert [Parameter].  The only fact CompCert states about it is the axiom
    [external_functions_properties]: every [external_functions_sem id sg]
    satisfies [extcall_properties].  The frozen program gives no definition:
    libc [memcpy], [memset] and [memcmp] are [EF_external], and
    [__builtin_ctzl] is not a CompCert 3.14 builtin
    ([jet_secp_ctz_semantics_gap]).

    Each theorem below is the formal content of "not derivable": for every
    model there is a family of external semantics that satisfies CompCert's
    whole interface (here the empty relation, which never returns) and makes
    the model false.  A proof of a model from the target would only use the
    parameter through that interface, so abstracting it would contradict the
    corresponding theorem.  These are results about provability, not about
    any real libc or compiler. *)
From Coq Require Import String ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Events Globalenvs.
Require Import C.jet_memcpy_model C.jet_memcpy_model_consistent C.jet_memset_model C.jet_memcmp_model
  C.jet_memcmp_model_consistent C.jet_ctz_model.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

(** The empty external semantics [no_behaviour] (the call never returns)
    satisfies the interface ([no_behaviour_ok]). *)
Notation never_returns := no_behaviour.

(** CompCert's whole interface for [external_functions_sem]. *)
Definition external_interface (efs : string -> signature -> extcall_sem) : Prop :=
  forall id sg, extcall_properties (efs id sg) sg.

Lemma never_returns_interface : external_interface (fun _ _ => never_returns).
Proof. intros id sg; apply no_behaviour_ok. Qed.

(** A fresh block with [hi] freeable bytes. *)
Lemma fresh_block hi : 0 <= hi ->
  exists m b, Mem.valid_block m b /\
    Mem.range_perm m b 0 hi Cur Freeable /\ Mem.range_perm m b 0 hi Cur Writable /\
    Mem.range_perm m b 0 hi Cur Readable.
Proof.
  intros _.
  destruct (Mem.alloc Mem.empty 0 hi) as [m b] eqn:A.
  exists m, b.
  assert (F : Mem.range_perm m b 0 hi Cur Freeable)
    by (intros ofs R; eapply Mem.perm_alloc_2; eauto).
  repeat split.
  - eapply Mem.valid_new_block; eauto.
  - exact F.
  - intros ofs R; eapply Mem.perm_implies; [apply F; exact R|constructor].
  - intros ofs R; eapply Mem.perm_implies; [apply F; exact R|constructor].
Qed.

Theorem memcpy_model_fails_for_never_returns : ~ memcpy_model_for never_returns.
Proof.
  intros H.
  destruct (fresh_block 2 ltac:(lia)) as (m & b & V & _ & W & R).
  assert (U1 : Ptrofs.unsigned (Ptrofs.repr 1) = 1) by reflexivity.
  assert (U0 : Ptrofs.unsigned Ptrofs.zero = 0) by reflexivity.
  destruct (Mem.range_perm_loadbytes m b 0 1) as [bytes L].
  { intros ofs O; apply R; lia. }
  destruct (H (Genv.to_senv (Genv.empty_genv unit unit [])) m b (Ptrofs.repr 1) b Ptrofs.zero 1 bytes)
    as (m' & _ & C); rewrite ?U0, ?U1.
  - exact V.
  - exact V.
  - exact L.
  - intros ofs O; apply W; lia.
  - right; left; lia.
  - change Int64.max_unsigned with 18446744073709551615; lia.
  - change Ptrofs.max_unsigned with 18446744073709551615; lia.
  - change Ptrofs.max_unsigned with 18446744073709551615; lia.
  - exact C.
Qed.

Theorem memset_model_fails_for_never_returns : ~ memset_model_for never_returns.
Proof.
  intros H.
  destruct (fresh_block 1 ltac:(lia)) as (m & b & V & _ & W & _).
  destruct (H (Genv.to_senv (Genv.empty_genv unit unit [])) m b Ptrofs.zero Int.zero 1)
    as (m' & _ & C).
  - exact V.
  - change (Ptrofs.unsigned Ptrofs.zero) with 0; exact W.
  - lia.
  - exact C.
Qed.

Theorem memcmp_model_fails_for_never_returns : ~ memcmp_model_for never_returns.
Proof.
  intros H.
  destruct (H (Genv.to_senv (Genv.empty_genv unit unit [])) Mem.empty 1%positive Ptrofs.zero
    1%positive Ptrofs.zero [] []) as (r & C & _).
  - reflexivity.
  - change Int64.max_unsigned with 18446744073709551615; cbn [length]; lia.
  - change Ptrofs.max_unsigned with 18446744073709551615;
    change (Ptrofs.unsigned Ptrofs.zero) with 0; cbn [length]; lia.
  - change Ptrofs.max_unsigned with 18446744073709551615;
    change (Ptrofs.unsigned Ptrofs.zero) with 0; cbn [length]; lia.
  - intros i I; cbn in I; lia.
  - intros i I; cbn in I; lia.
  - exact C.
Qed.

Theorem ctz_model_fails_for_never_returns : ~ ctz_model_for never_returns.
Proof.
  intros H.
  exact (H (Genv.to_senv (Genv.empty_genv unit unit [])) Mem.empty Int64.one ltac:(discriminate)).
Qed.

(** The public results: no model follows from CompCert's interface for
    external calls, quantified over every interpretation of the parameter. *)
Theorem memcpy_model_not_derivable :
  ~ (forall efs, external_interface efs -> memcpy_model_for (efs "memcpy"%string memcpy_sig)).
Proof.
  intros H; apply memcpy_model_fails_for_never_returns.
  exact (H _ never_returns_interface).
Qed.

Theorem memset_model_not_derivable :
  ~ (forall efs, external_interface efs -> memset_model_for (efs "memset"%string memset_sig)).
Proof.
  intros H; apply memset_model_fails_for_never_returns.
  exact (H _ never_returns_interface).
Qed.

Theorem memcmp_model_not_derivable :
  ~ (forall efs, external_interface efs -> memcmp_model_for (efs "memcmp"%string memcmp_sig)).
Proof.
  intros H; apply memcmp_model_fails_for_never_returns.
  exact (H _ never_returns_interface).
Qed.

Theorem ctz_model_not_derivable :
  ~ (forall efs, external_interface efs -> ctz_model_for (efs "__builtin_ctzl"%string ctz_sig)).
Proof.
  intros H; apply ctz_model_fails_for_never_returns.
  exact (H _ never_returns_interface).
Qed.
