(** Numeric interpretation of the literal carry-expanded canonical program.
    This bridge is used to compare actual C limb outputs, not to substitute
    a different numeric function for the specification. *)
From Coq Require Import ZArith.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_predicate_spec C.jet_canonical_add_adapter.
Require Import C.jet_secp_canonical_normalize C.jet_secp_canonical_negate.
Require Import C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_fe_one256_value :
  @toZ (WordToZ 8) (@literal_fe_one256 Alg.CoreFunSem tt) = 1.
Proof. vm_compute. reflexivity. Qed.

Lemma literal_fe_add_expand_value c (x : Ty.tySem (Word 8)) :
  @toZ (WordToZ 9) (@literal_fe_add_expand Alg.CoreFunSem (c,x)) =
  @toZ (PairToZ BitToZ (WordToZ 8)) (c,x).
Proof.
  destruct c as [[] | []].
  - change (@toZ (WordToZ 8) (@Word.zero 8 Alg.CoreFunSem tt) * word_modulus 8 +
      @toZ (WordToZ 8) x = 0 * word_modulus 8 + @toZ (WordToZ 8) x).
    rewrite Word.zero_correct. reflexivity.
  - change (@toZ (WordToZ 8) (@literal_fe_one256 Alg.CoreFunSem tt) * word_modulus 8 +
      @toZ (WordToZ 8) x = 1 * word_modulus 8 + @toZ (WordToZ 8) x).
    rewrite literal_fe_one256_value. reflexivity.
Qed.

Lemma literal_fe_add_expand_pair_value (p : Ty.tySem (Ty.Prod Bit (Word 8))) :
  @toZ (WordToZ 9) (@literal_fe_add_expand Alg.CoreFunSem p) =
  @toZ (PairToZ BitToZ (WordToZ 8)) p.
Proof. destruct p as [c x]. apply literal_fe_add_expand_value. Qed.

Lemma literal_fe_add_numeric (a b : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (a,b)) =
  (@toZ (WordToZ 8) a + @toZ (WordToZ 8) b) mod canonical_field_order.
Proof.
  change (@toZ (WordToZ 8)
    (@literal_fe_normalize512 Alg.CoreFunSem
      (@literal_fe_add_expand Alg.CoreFunSem
        (@canonical_add_word 8 Alg.CoreFunSem (a,b)))) =
    (@toZ (WordToZ 8) a + @toZ (WordToZ 8) b) mod canonical_field_order).
  rewrite literal_fe_normalize512_matches, canonical_fe_normalize512_numeric.
  rewrite literal_fe_add_expand_pair_value, canonical_add_word_matches_adder.
  rewrite Word.adder_correct. reflexivity.
Qed.
Print Assumptions literal_fe_one256_value.
Print Assumptions literal_fe_add_expand_value.
Print Assumptions literal_fe_add_expand_pair_value.
Print Assumptions literal_fe_add_numeric.
