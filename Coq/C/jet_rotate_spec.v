(** Literal Programs.Word.left_rotate: least-significant control first,
    conditional rotate1, then vectorPromote; SingleV retains its final step.
    This canonical program is support for C-to-program consumers, not coverage. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_bit_spec C.jet_left_rotate_wide_exec C.jet_wide.
Import ListNotations.
Module VC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint vector_items_spec X n {term : Alg.Core.Algebra} :
    list (@Alg.Core.domain term (Vector X n) X) :=
  match n as n return list (@Alg.Core.domain term (Vector X n) X) with
  | O => [VC.iden]
  | S n => map VC.take (vector_items_spec X n) ++ map VC.drop (vector_items_spec X n)
  end.

Lemma word8_reverse_items_spec {term : Alg.Core.Algebra} :
  rev (@vector_items_spec Bit 3 term) =
    map (fun i => @word_bit_spec 3 i term) (List.seq 0 8).
Proof. reflexivity. Qed.

Definition left_rotate_control_step m X n i {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word m) (Vector X n)) (Ty.Prod (Word m) (Vector X n)) :=
  VC.pair (VC.take VC.iden)
    (VC.comp (VC.pair (VC.take (word_bit_spec m i)) (VC.drop VC.iden))
      (Bit.cond (@Word.left_rotate1 X n term) VC.iden)).

Fixpoint left_rotate_controls_spec m X n (indices : list nat) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word m) (Vector X n)) (Vector X n) :=
  match n as n return @Alg.Core.domain term (Ty.Prod (Word m) (Vector X n)) (Vector X n) with
  | O => match indices with
      | [] => VC.drop VC.iden
      | i :: _ => VC.comp (left_rotate_control_step m X 0 i) (VC.drop VC.iden)
      end
  | S n => match indices with
      | [] => VC.drop VC.iden
      | i :: rest => VC.comp (left_rotate_control_step m X (S n) i)
          (eq_rect (Vector (Ty.Prod X X) n)
            (fun V => @Alg.Core.domain term (Ty.Prod (Word m) V) V)
            (left_rotate_controls_spec m (Ty.Prod X X) n rest)
            (Vector X (S n)) (eq_sym (@VectorPromote X n)))
      end
  end.

Definition left_rotate_word_spec m n {term : Alg.Core.Algebra} :=
  @left_rotate_controls_spec m Bit n (List.seq 0 (Nat.pow 2 m)) term.
Definition left_rotate_byte_spec s {term : Alg.Core.Algebra} :=
  @left_rotate_word_spec 3 (wide_log (byte_rotate_width s)) term.

Lemma left_rotate_control_step_parametric m X n i : Alg.Core.Parametric (@left_rotate_control_step m X n i).
Proof.
  intros alg1 alg2 R. unfold left_rotate_control_step. apply Alg.pair_Parametric.
  - apply Alg.take_Parametric; apply Alg.iden_Parametric.
  - apply Alg.comp_Parametric.
    + apply Alg.pair_Parametric.
      * apply Alg.take_Parametric; apply word_bit_spec_parametric.
      * apply Alg.drop_Parametric; apply Alg.iden_Parametric.
    + apply Bit.cond_Parametric; [apply Word.left_rotate1_Parametric|apply Alg.iden_Parametric].
Qed.

Lemma left_rotate_controls_spec_parametric m X n indices :
  Alg.Core.Parametric (@left_rotate_controls_spec m X n indices).
Proof.
  revert X indices. induction n as [|n IH]; intros X indices alg1 alg2 R; destruct indices as [|i rest].
  - apply Alg.drop_Parametric; apply Alg.iden_Parametric.
  - apply Alg.comp_Parametric; [apply left_rotate_control_step_parametric|].
    apply Alg.drop_Parametric; apply Alg.iden_Parametric.
  - apply Alg.drop_Parametric; apply Alg.iden_Parametric.
  - cbn [left_rotate_controls_spec]. apply Alg.comp_Parametric; [apply left_rotate_control_step_parametric|].
    destruct (@eq_sym Ty (Vector X (S n)) (Vector (Ty.Prod X X) n) (@VectorPromote X n)); apply IH.
Qed.

Lemma left_rotate_word_spec_parametric m n : Alg.Core.Parametric (@left_rotate_word_spec m n).
Proof. apply left_rotate_controls_spec_parametric. Qed.
Lemma left_rotate_byte_spec_parametric s : Alg.Core.Parametric (@left_rotate_byte_spec s).
Proof. apply left_rotate_word_spec_parametric. Qed.
