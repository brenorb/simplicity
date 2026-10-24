(** Conservative temporary framing for call-free, temporary-only statements. *)
From Coq Require Import List Bool PArith.
From compcert Require Import Clight ClightBigstep Maps.
Import ListNotations.
Set Default Timeout 10.

Fixpoint temp_writes_within (allowed : list positive) (s : statement) : bool :=
  match s with
  | Sskip | Sbreak | Scontinue => true
  | Sset id _ => existsb (Pos.eqb id) allowed
  | Ssequence a b | Sifthenelse _ a b | Sloop a b =>
      temp_writes_within allowed a && temp_writes_within allowed b
  | _ => false
  end.

Theorem exec_temp_frame ge e le m s t lef mf out allowed :
  Clight2.exec_stmt ge e le m s t lef mf out -> temp_writes_within allowed s=true ->
  forall id,~In id allowed -> lef!id=le!id.
Proof.
  intros Run;induction Run;intro Safe;cbn [temp_writes_within] in Safe;try discriminate;
    intros key Outside;try reflexivity.
  - rewrite PTree.gso;[reflexivity|].
    intro Eq;subst key;apply Outside.
    apply existsb_exists in Safe;destruct Safe as (x & Member & Eq).
    apply Pos.eqb_eq in Eq;subst x;exact Member.
  - apply andb_true_iff in Safe;destruct Safe as [Left Right].
    rewrite IHRun2 by assumption;apply IHRun1;assumption.
  - apply andb_true_iff in Safe;destruct Safe as [Left Right].
    apply IHRun;assumption.
  - apply andb_true_iff in Safe;destruct Safe as [Left Right].
    apply IHRun;[destruct b;assumption|exact Outside].
  - apply andb_true_iff in Safe;destruct Safe as [Left Right].
    apply IHRun;assumption.
  - apply andb_true_iff in Safe;destruct Safe as [Left Right].
    rewrite IHRun2 by assumption;apply IHRun1;assumption.
  - pose proof Safe as Loop;apply andb_true_iff in Safe;destruct Safe as [Left Right].
    rewrite IHRun3 by assumption;rewrite IHRun2 by assumption;apply IHRun1;assumption.
Qed.
