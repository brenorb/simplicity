(** Literal Programs.Word.firstFail, including its canonical assertion hash.
    These lemmas support count jets; they do not establish C-jet coverage. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_forWhile_spec C.jet_assertion_spec.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Implicit Arguments.
Set Default Timeout 10.

Definition first_fail_body n {A B : Ty} {alg : Core.Algebra}
    (op : alg (Word n) (A + B)) : alg ((Unit * Word n) * Unit) (Word n + Unit) :=
  take (drop ((op &&& iden) >>> case (injl (I H)) (injr unit))).

Definition first_fail_program n {A B : Ty} {alg : Assertion.Algebra}
    (op : alg (Word n) (A + B)) : alg Unit (Word n) :=
  (unit &&& unit) >>> for_while_program n (first_fail_body n op) >>>
    (iden &&& unit) >>> assertl (O H) assertion_cmr_fail0.

Lemma first_fail_body_parametric n {A B : Ty} {alg1 alg2 : Core.Algebra}
    (R : Core.Parametric.Rel alg1 alg2)
    (op1 : alg1 (Word n) (A + B)) (op2 : alg2 (Word n) (A + B)) :
  R _ _ op1 op2 -> R _ _ (first_fail_body n op1) (first_fail_body n op2).
Proof. intro HO. unfold first_fail_body. auto 12 with parametricity. Qed.

Lemma first_fail_program_parametric n {A B : Ty} {alg1 alg2 : Assertion.Algebra}
    (R : Assertion.Parametric.Rel alg1 alg2)
    (op1 : alg1 (Word n) (A + B)) (op2 : alg2 (Word n) (A + B)) :
  R _ _ op1 op2 -> R _ _ (first_fail_program n op1) (first_fail_program n op2).
Proof.
  destruct R as [R [HC HA]]. intro HO.
  unfold first_fail_program.
  apply (comp_Parametric (Core.Parametric.Pack HC)); [auto with parametricity | ].
  apply (comp_Parametric (Core.Parametric.Pack HC)).
  - apply (for_while_program_parametric n (Core.Parametric.Pack HC)).
    apply (first_fail_body_parametric n (Core.Parametric.Pack HC)). exact HO.
  - apply (comp_Parametric (Core.Parametric.Pack HC)); [auto with parametricity | ].
    apply (assertl_Parametric
      (Assertion.Parametric.Pack (Assertion.Parametric.Build_class HC HA))).
    apply (take_Parametric (Core.Parametric.Pack HC)). apply iden_Parametric.
Qed.

Lemma first_fail_program_reader_finish n {E : Type} {A B : Ty}
    (op : AssertionSem (ReaderT_CIMonadZero E option_Monad_Zero) (Word n) (A + B))
    (environment : E) :
  first_fail_program n op tt environment =
    option_bind (fun result : tySem (Word n + Unit) =>
      match result with inl counter => Some counter | inr _ => None end)
      (for_while_program n (first_fail_body n op) (tt, tt) environment).
Proof.
  unfold first_fail_program.
  remember (for_while_program n (first_fail_body n op) (tt, tt) environment)
    as result eqn:HR.
  destruct result as [[counter | []] | ];
    lazy beta iota zeta delta -[for_while_program first_fail_body assertion_cmr_fail0] in HR |- *;
    rewrite <- HR; reflexivity.
Qed.

Definition first_fail_step n {A B : Ty}
    (op : tySem (Word n) -> option (tySem (A + B)))
    (p : tySem ((Unit * Word n) * Unit)) : option (tySem (Word n + Unit)) :=
  match op (snd (fst p)) with
  | None => None
  | Some (inl _) => Some (inl (snd (fst p)))
  | Some (inr _) => Some (inr tt)
  end.

Definition first_fail_run n {A B : Ty}
    (op : tySem (Word n) -> option (tySem (A + B))) : option (tySem (Word n)) :=
  match for_while_run n (first_fail_step n op) tt tt with
  | Some (inl counter) => Some counter
  | Some (inr _) => None
  | None => None
  end.

Lemma first_fail_body_reader_sem n {E : Type} {A B : Ty}
    (op : CoreSem (ReaderT_CIMonad E option_CIMonad) (Word n) (A + B))
    (p : tySem ((Unit * Word n) * Unit)) (environment : E) :
  first_fail_body n op p environment = first_fail_step n (fun w => op w environment) p.
Proof.
  destruct p as [[[] w] []]. unfold first_fail_body, first_fail_step.
  destruct (op w environment) as [[a | b] | ] eqn:HO;
    lazy beta iota zeta delta in HO |- *; rewrite HO; reflexivity.
Qed.

Lemma first_fail_program_reader_sem n {E : Type} {A B : Ty}
    (op : AssertionSem (ReaderT_CIMonadZero E option_Monad_Zero) (Word n) (A + B))
    (environment : E) :
  first_fail_program n op tt environment = first_fail_run n (fun w => op w environment).
Proof.
  rewrite first_fail_program_reader_finish.
  change (option_bind (fun result : tySem (Word n + Unit) =>
      match result with inl counter => Some counter | inr _ => None end)
    (@for_while_program n Unit (Word n) Unit
      (CoreSem (ReaderT_CIMonad E option_CIMonad)) (first_fail_body n op)
      (tt, tt) environment) = first_fail_run n (fun w => op w environment)).
  rewrite for_while_program_reader_sem.
  unfold first_fail_run.
  assert (HBody :
    for_while_run n (fun p => first_fail_body n op p environment) tt tt =
    for_while_run n (first_fail_step n (fun w => op w environment)) tt tt).
  { apply for_while_run_ext. intro p. apply first_fail_body_reader_sem. }
  rewrite HBody. unfold option_bind, option_join.
  destruct (for_while_run n (first_fail_step n (fun w => op w environment)) tt tt)
    as [[counter | []] | ]; reflexivity.
Qed.
