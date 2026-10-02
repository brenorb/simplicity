(** Literal canonical Programs.Word.right_rotate, retaining variable controls
    and vector promotion. This specification alone adds no C jet coverage. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_bit_spec C.jet_left_rotate_wide_exec C.jet_wide C.jet_rotate_spec.
Import ListNotations.
Module RVC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition right_rotate_control_step m X n i {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word m) (Vector X n)) (Ty.Prod (Word m) (Vector X n)) :=
  RVC.pair (RVC.take RVC.iden)
    (RVC.comp (RVC.pair (RVC.take (word_bit_spec m i)) (RVC.drop RVC.iden))
      (Bit.cond (@Word.right_rotate1 X n term) RVC.iden)).

Fixpoint right_rotate_controls_spec m X n (indices : list nat) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Word m) (Vector X n)) (Vector X n) :=
  match n as n return @Alg.Core.domain term (Ty.Prod (Word m) (Vector X n)) (Vector X n) with
  | O => match indices with
      | [] => RVC.drop RVC.iden
      | i :: _ => RVC.comp (right_rotate_control_step m X 0 i) (RVC.drop RVC.iden)
      end
  | S n => match indices with
      | [] => RVC.drop RVC.iden
      | i :: rest => RVC.comp (right_rotate_control_step m X (S n) i)
          (eq_rect (Vector (Ty.Prod X X) n)
            (fun V => @Alg.Core.domain term (Ty.Prod (Word m) V) V)
            (right_rotate_controls_spec m (Ty.Prod X X) n rest)
            (Vector X (S n)) (eq_sym (@VectorPromote X n)))
      end
  end.

Definition right_rotate_word_spec m n {term : Alg.Core.Algebra} :=
  @right_rotate_controls_spec m Bit n (List.seq 0 (Nat.pow 2 m)) term.
Definition right_rotate_byte_spec s {term : Alg.Core.Algebra} :=
  @right_rotate_word_spec 3 (wide_log (byte_rotate_width s)) term.

Lemma right_rotate_control_step_parametric m X n i : Alg.Core.Parametric (@right_rotate_control_step m X n i).
Proof.
  intros alg1 alg2 R. unfold right_rotate_control_step. apply Alg.pair_Parametric.
  - apply Alg.take_Parametric; apply Alg.iden_Parametric.
  - apply Alg.comp_Parametric.
    + apply Alg.pair_Parametric.
      * apply Alg.take_Parametric; apply word_bit_spec_parametric.
      * apply Alg.drop_Parametric; apply Alg.iden_Parametric.
    + apply Bit.cond_Parametric; [apply Word.right_rotate1_Parametric|apply Alg.iden_Parametric].
Qed.

Lemma right_rotate_controls_spec_parametric m X n indices :
  Alg.Core.Parametric (@right_rotate_controls_spec m X n indices).
Proof.
  revert X indices. induction n as [|n IH]; intros X indices alg1 alg2 R; destruct indices as [|i rest].
  - apply Alg.drop_Parametric; apply Alg.iden_Parametric.
  - apply Alg.comp_Parametric; [apply right_rotate_control_step_parametric|].
    apply Alg.drop_Parametric; apply Alg.iden_Parametric.
  - apply Alg.drop_Parametric; apply Alg.iden_Parametric.
  - cbn [right_rotate_controls_spec]. apply Alg.comp_Parametric; [apply right_rotate_control_step_parametric|].
    destruct (@eq_sym Ty (Vector X (S n)) (Vector (Ty.Prod X X) n) (@VectorPromote X n)); apply IH.
Qed.

Lemma right_rotate_word_spec_parametric m n : Alg.Core.Parametric (@right_rotate_word_spec m n).
Proof. apply right_rotate_controls_spec_parametric. Qed.
Lemma right_rotate_byte_spec_parametric s : Alg.Core.Parametric (@right_rotate_byte_spec s).
Proof. apply right_rotate_word_spec_parametric. Qed.

