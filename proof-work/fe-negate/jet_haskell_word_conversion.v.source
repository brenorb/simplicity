(** Port of Ty.Word.toWord's low-first State traversal and its fromZ bridge. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit C.jet_predicate_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint haskell_word_state n (z : Z) : Ty.tySem (Word n) * Z :=
  match n as n return Ty.tySem (Word n) * Z with
  | O => ((if Z.odd z then Bit.one else Bit.zero), z / 2)
  | S n =>
      let '(lo, rest) := haskell_word_state n z in
      let '(hi, final) := haskell_word_state n rest in
      ((hi, lo), final)
  end.

Lemma haskell_word_state_matches n z :
  haskell_word_state n z = (@fromZ (WordToZ n) z, z / word_modulus n).
Proof.
  revert z. induction n as [|n IH]; intro z.
  - reflexivity.
  - cbn [haskell_word_state]. rewrite IH, IH.
    change (((@fromZ (WordToZ n) (z / word_modulus n), @fromZ (WordToZ n) z),
      (z / word_modulus n) / word_modulus n) =
      ((@fromZ (WordToZ n) (z / word_modulus n), @fromZ (WordToZ n) z),
        z / word_modulus (S n))).
    rewrite Z.div_div by (pose proof (word_modulus_positive n); lia).
    rewrite word_modulus_S. reflexivity.
Qed.

Definition haskell_to_word n z := fst (haskell_word_state n z).
Lemma haskell_to_word_matches n z : haskell_to_word n z = @fromZ (WordToZ n) z.
Proof. unfold haskell_to_word. rewrite haskell_word_state_matches. reflexivity. Qed.
Print Assumptions haskell_to_word_matches.
