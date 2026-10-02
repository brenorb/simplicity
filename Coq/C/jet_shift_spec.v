(** Literal Programs.Word.left/right_shift_with variable-control recursion.
    Unlike rotation, SingleV keeps consuming all remaining controls. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_bit_spec.
Import ListNotations.
Module SVC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift_control_step m X n (right : bool) i {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod X (Ty.Prod (Word m) (Vector X n)))
      (Ty.Prod X (Ty.Prod (Word m) (Vector X n))) :=
  SVC.pair (SVC.take SVC.iden)
    (SVC.pair (SVC.drop (SVC.take SVC.iden))
      (if right then
        SVC.comp
          (SVC.pair (SVC.drop (SVC.take (word_bit_spec m i)))
            (SVC.pair (SVC.take SVC.iden) (SVC.drop (SVC.drop SVC.iden))))
          (Bit.cond (SVC.comp (@Word.full_right_shift1 X n term) (SVC.take SVC.iden)) (SVC.drop SVC.iden))
       else SVC.comp
          (SVC.pair (SVC.drop (SVC.take (word_bit_spec m i)))
            (SVC.pair (SVC.drop (SVC.drop SVC.iden)) (SVC.take SVC.iden)))
          (Bit.cond (SVC.comp (@Word.full_left_shift1 X n term) (SVC.drop SVC.iden)) (SVC.take SVC.iden)))).

Fixpoint shift_controls_spec m X n right (indices : list nat) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod X (Ty.Prod (Word m) (Vector X n))) (Vector X n) :=
  match indices with
  | [] => SVC.drop (SVC.drop SVC.iden)
  | i :: rest => match n as n return
      @Alg.Core.domain term (Ty.Prod X (Ty.Prod (Word m) (Vector X n))) (Vector X n) with
    | O => SVC.comp (shift_control_step m X 0 right i) (shift_controls_spec m X 0 right rest)
    | S n => SVC.comp (shift_control_step m X (S n) right i)
        (SVC.comp
          (SVC.pair (SVC.pair (SVC.take SVC.iden) (SVC.take SVC.iden)) (SVC.drop SVC.iden))
          (eq_rect (Vector (Ty.Prod X X) n)
            (fun V => @Alg.Core.domain term (Ty.Prod (Ty.Prod X X) (Ty.Prod (Word m) V)) V)
            (shift_controls_spec m (Ty.Prod X X) n right rest)
            (Vector X (S n)) (eq_sym (@VectorPromote X n))))
    end
  end.

Definition shift_with_word_spec m n right {term : Alg.Core.Algebra} :=
  @shift_controls_spec m Bit n right (List.seq 0 (Nat.pow 2 m)) term.
Definition shift_word_spec m n right {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word m) (Word n)) (Word n) :=
  SVC.comp (SVC.pair (@Bit.false (Ty.Prod (Word m) (Word n)) term) SVC.iden)
    (shift_with_word_spec m n right).

Lemma shift_control_step_parametric m X n right i : Alg.Core.Parametric (@shift_control_step m X n right i).
Proof.
  intros alg1 alg2 R. unfold shift_control_step. apply Alg.pair_Parametric.
  - apply Alg.take_Parametric; apply Alg.iden_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.drop_Parametric; apply Alg.take_Parametric; apply Alg.iden_Parametric.
    + destruct right; apply Alg.comp_Parametric.
      all: try (apply Alg.pair_Parametric;
        [apply Alg.drop_Parametric; apply Alg.take_Parametric; apply word_bit_spec_parametric|
         apply Alg.pair_Parametric;
           solve [apply Alg.take_Parametric; apply Alg.iden_Parametric|
             apply Alg.drop_Parametric; apply Alg.drop_Parametric; apply Alg.iden_Parametric]]).
      all: apply Bit.cond_Parametric.
      * apply Alg.comp_Parametric; [apply Word.full_right_shift1_Parametric|apply Alg.take_Parametric; apply Alg.iden_Parametric].
      * apply Alg.drop_Parametric; apply Alg.iden_Parametric.
      * apply Alg.comp_Parametric; [apply Word.full_left_shift1_Parametric|apply Alg.drop_Parametric; apply Alg.iden_Parametric].
      * apply Alg.take_Parametric; apply Alg.iden_Parametric.
Qed.

Lemma shift_controls_spec_parametric m X n right indices :
  Alg.Core.Parametric (@shift_controls_spec m X n right indices).
Proof.
  revert X n. induction indices as [|i rest IH]; intros X n alg1 alg2 R.
  - apply Alg.drop_Parametric; apply Alg.drop_Parametric; apply Alg.iden_Parametric.
  - destruct n as [|n].
    + apply Alg.comp_Parametric; [apply shift_control_step_parametric|apply IH].
    + cbn [shift_controls_spec]. apply Alg.comp_Parametric; [apply shift_control_step_parametric|].
      apply Alg.comp_Parametric.
      * apply Alg.pair_Parametric.
        -- apply Alg.pair_Parametric; apply Alg.take_Parametric; apply Alg.iden_Parametric.
        -- apply Alg.drop_Parametric; apply Alg.iden_Parametric.
      * destruct (@eq_sym Ty (Vector X (S n)) (Vector (Ty.Prod X X) n) (@VectorPromote X n)); apply IH.
Qed.

Lemma shift_with_word_spec_parametric m n right : Alg.Core.Parametric (@shift_with_word_spec m n right).
Proof. apply shift_controls_spec_parametric. Qed.
Lemma shift_word_spec_parametric m n right : Alg.Core.Parametric (@shift_word_spec m n right).
Proof.
  intros alg1 alg2 R. unfold shift_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Bit.false_Parametric|apply Alg.iden_Parametric].
  - apply shift_with_word_spec_parametric.
Qed.
