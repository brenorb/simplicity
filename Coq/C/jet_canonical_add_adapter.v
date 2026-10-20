(** Literal Programs.Arith.add and the optimized Word.adder adapter.
    The bit base is only semantically equal; positive vector depths have
    identical Core programs. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition canonical_add_word n {term : Alg.Core.Algebra} :
    term (Ty.Prod (Word n) (Word n)) (Ty.Prod Bit (Word n)) :=
  Bit.false &&& iden >>> @Word.fullAdder n term.

Lemma canonical_add_word_wide_core_matches n term :
  @canonical_add_word (S n) term = @Word.adder (S n) term.
Proof. reflexivity. Qed.

Lemma canonical_add_word_parametric n :
  Alg.Core.Parametric (@canonical_add_word n).
Proof.
  intros term1 term2 R. unfold canonical_add_word.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Bit.false_Parametric|apply Alg.iden_Parametric].
  - apply Word.fullAdder_Parametric.
Qed.

Lemma canonical_add_word_matches_adder n (x : Ty.tySem (Ty.Prod (Word n) (Word n))) :
  @canonical_add_word n Alg.CoreFunSem x = @Word.adder n Alg.CoreFunSem x.
Proof.
  destruct n as [|n].
  - destruct x as [a b]. destruct a as [[] | []], b as [[] | []]; reflexivity.
  - reflexivity.
Qed.
Print Assumptions canonical_add_word_matches_adder.
