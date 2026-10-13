(** Literal scalar_normalize port from pinned Programs/LibSecp256k1.hs.
    Canonical representation support only; no C jet equivalence is claimed. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_subtract_spec.
Local Open Scope Z_scope.
Local Open Scope ty_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

(** groupOrder is the literal 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141 in the pinned Haskell. *)
Definition canonical_group_order : Z :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337.
Definition canonical_group_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) canonical_group_order.
Definition canonical_scalar_normalize {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
  ((iden &&& (unit >>> Alg.scribe canonical_group_word) >>> @subtract_word_spec term 8) &&& iden)
  >>> (O O H &&& (O I H &&& I H))
  >>> cond (I H) (O H).

Lemma canonical_group_order_range :
  0 < canonical_group_order < word_modulus 8 /\
  word_modulus 8 < 2 * canonical_group_order.
Proof. vm_compute; repeat split; discriminate. Qed.
Lemma canonical_group_word_value :
  @toZ (WordToZ 8) canonical_group_word = canonical_group_order.
Proof.
  unfold canonical_group_word; rewrite to_fromZ.
  apply Z.mod_small.
  change (0 <= canonical_group_order < word_modulus 8).
  pose proof canonical_group_order_range; lia.
Qed.
Local Opaque subtract_word_spec canonical_group_word.

Lemma canonical_scalar_normalize_step (x : Ty.tySem (Word 8)) :
  @canonical_scalar_normalize Alg.CoreFunSem x =
  let z := @subtract_word_spec Alg.CoreFunSem 8 (x, canonical_group_word) in
  match fst z with inl _ => snd z | inr _ => x end.
Proof.
  change ((let z := @subtract_word_spec Alg.CoreFunSem 8
      (x, @Alg.scribe Ty.Unit (Word 8) canonical_group_word Alg.CoreFunSem tt) in
    match fst z with inl _ => snd z | inr _ => x end) =
    (let z := @subtract_word_spec Alg.CoreFunSem 8 (x, canonical_group_word) in
     match fst z with inl _ => snd z | inr _ => x end)).
  rewrite Alg.scribe_correct; reflexivity.
Qed.

Theorem canonical_scalar_normalize_numeric (x : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem x) =
    @toZ (WordToZ 8) x mod canonical_group_order.
Proof.
  rewrite canonical_scalar_normalize_step.
  set (v := @toZ (WordToZ 8) x).
  set (payload := @fromZ (WordToZ 8) (v - canonical_group_order)).
  assert (HSub : @subtract_word_spec Alg.CoreFunSem 8 (x, canonical_group_word) =
    ((if v <? canonical_group_order then inr tt else inl tt), payload)).
  { symmetry.
    rewrite <- canonical_group_word_value at 1.
    apply subtract_representation_matches.
    unfold payload; rewrite to_fromZ, canonical_group_word_value; reflexivity. }
  rewrite HSub; cbn [fst snd].
  pose proof (word_value_bounds 8 x) as HX; fold v in HX.
  destruct canonical_group_order_range as [[HP HM] HTwice].
  destruct (v <? canonical_group_order) eqn:Hlt.
  - apply Z.ltb_lt in Hlt. symmetry; apply Z.mod_small; lia.
  - apply Z.ltb_ge in Hlt.
    unfold payload; rewrite to_fromZ.
    fold (word_modulus 8).
    rewrite Z.mod_small by lia.
    replace v with ((v - canonical_group_order) + 1 * canonical_group_order)%Z at 2 by ring.
    rewrite Z.mod_add by lia; rewrite Z.mod_small by lia; reflexivity.
Qed.

