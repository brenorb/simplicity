(** Decompose a statement's sequence spine and recombine its actual execution. *)
From Coq Require Import List.
From compcert Require Import Clight ClightBigstep Events.
Import ListNotations.
Set Default Timeout 10.
Fixpoint split_statement_last (s : statement) : list statement * statement :=
  match s with
  | Ssequence first_stmt rest_stmt =>
      let '(prefix, last) := split_statement_last rest_stmt in (first_stmt :: prefix, last)
  | _ => ([], s) end.
Fixpoint statement_sequence (prefix : list statement) (last : statement) : statement :=
  match prefix with [] => last | head :: tail => Ssequence head (statement_sequence tail last) end.
Lemma split_statement_last_exact s :
  statement_sequence (fst (split_statement_last s)) (snd (split_statement_last s)) = s.
Proof.
  induction s; try reflexivity.
  cbn [split_statement_last].
  destruct (split_statement_last s2) as [prefix last] eqn:HE.
  cbn [fst snd statement_sequence].
  cbn [fst snd] in IHs2; rewrite IHs2; reflexivity.
Qed.
Lemma exec_statement_prefix_then_last ge e prefix last le m le1 m1 le2 m2 out :
  Clight2.exec_stmt ge e le m (statement_sequence prefix Sskip) E0 le1 m1 Out_normal ->
  Clight2.exec_stmt ge e le1 m1 last E0 le2 m2 out ->
  Clight2.exec_stmt ge e le m (statement_sequence prefix last) E0 le2 m2 out.
Proof.
  revert le m le1 m1; induction prefix as [|head tail IH];
    intros le m le1 m1 HP HT; cbn [statement_sequence] in *.
  - inversion HP; subst; exact HT.
  - inversion HP; subst.
    + match goal with
      | H : ?t1 ** ?t2 = E0 |- _ =>
          destruct (Eapp_E0_inv t1 t2 H) as [-> ->]
      | H : E0 = ?t1 ** ?t2 |- _ =>
          destruct (Eapp_E0_inv t1 t2 (eq_sym H)) as [-> ->]
      end.
      change E0 with (E0 ** E0).
      eapply exec_Sseq_1; [eassumption|eapply IH; eassumption].
    + contradiction.
Qed.
