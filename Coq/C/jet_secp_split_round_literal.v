(** Literal roundDivTwo384 and the rounded-coefficient portions of
    scalar_split_lambda, Haskell/Core/Simplicity/Programs/LibSecp256k1.hs
    593--600. The payload is 128 bits; strict coefficient bounds justify
    discarding its carry only for these two original multipliers. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_word_repr C.jet_toZ C.jet_increment_spec C.jet_increment_wide_word
 C.jet_full_increment8_word C.jet_multiply_spec C.jet_secp_wnaf_literal_next C.jet_secp_split_multipliers.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_round384 {term:Alg.Core.Algebra} : term (Word 9) (Word 7) :=
 O ((I (@Word.leftmost Bit 7 term) &&& O H) >>> @full_increment_word_spec term 7) >>> I H.
Definition literal_split_coefficient (first:bool) {term:Alg.Core.Algebra} : term (Word 8) (Word 7) :=
 (iden &&& (unit >>> Alg.scribe (@fromZ (WordToZ 8) (split_multiplier_value first)))) >>>
 @multiply_word_spec 8 term >>> @literal_round384 term.

Lemma literal_round384_parametric : Alg.Core.Parametric (@literal_round384).
Proof.
 intros a b R;unfold literal_round384;apply Alg.comp_Parametric.
 - apply Alg.take_Parametric;apply Alg.comp_Parametric.
   + apply Alg.pair_Parametric;[apply Alg.drop_Parametric;apply Word.leftmost_Parametric|
     apply Alg.take_Parametric;apply Alg.iden_Parametric].
   + apply full_increment_word_spec_parametric.
 - apply Alg.drop_Parametric;apply Alg.iden_Parametric.
Qed.
Lemma literal_split_coefficient_parametric first : Alg.Core.Parametric (@literal_split_coefficient first).
Proof.
 intros a b R;unfold literal_split_coefficient;apply Alg.comp_Parametric.
 - apply Alg.pair_Parametric;[apply Alg.iden_Parametric|].
   apply Alg.comp_Parametric;[apply Alg.unit_Parametric|apply Alg.scribe_Parametric].
 - apply Alg.comp_Parametric;[apply multiply_word_spec_parametric|apply literal_round384_parametric].
Qed.

Local Opaque full_increment_word_spec.
Lemma increment128_payload bit word :
 @toZ (WordToZ 7) (snd (@full_increment_word_spec Alg.CoreFunSem 7 (bit,word)))=
 (@toZ (WordToZ 7) word+ @toZ BitToZ bit) mod 2^128.
Proof.
 pose proof (full_increment_word_spec_numeric 7 bit word) as Value.
 assert (Expand:forall p:Ty.tySem (Ty.Prod Bit (Word 7)),
  @toZ (PairToZ BitToZ (WordToZ 7)) p=
  @toZ BitToZ (fst p)*2^128+ @toZ (WordToZ 7) (snd p)) by (intros [c v];reflexivity).
 rewrite Expand in Value.
 rewrite <-Value.
 set (result:=@full_increment_word_spec Alg.CoreFunSem 7 (bit,word)).
 change (@toZ (WordToZ 7) (snd result)=
  (@toZ BitToZ (fst result)*2^128+ @toZ (WordToZ 7) (snd result)) mod 2^128).
 apply Z.mod_unique with (q:=@toZ BitToZ (fst result));
 [left;exact (word_toZ_range 7 (snd result))|ring].
Qed.

Lemma round384_integer hi mid lo : 0<=mid<2^128 -> 0<=lo<2^256 ->
 ((hi*2^128+mid)*2^256+lo+2^383)/2^384=hi+mid/2^127.
Proof.
 intros Mid Low.
 pose proof (Z.div_mod mid (2^127) ltac:(lia)) as Divide.
 pose proof (Z.mod_pos_bound mid (2^127) ltac:(lia)) as Remainder.
 assert (Quotient:0<=mid/2^127<2).
 { split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
 assert (Cases:mid/2^127=0 \/ mid/2^127=1) by lia.
 symmetry;apply Z.div_unique with (r:=lo+2^256*(mid mod 2^127)+2^383*(1-mid/2^127)).
 - destruct Cases as [Zero|One];rewrite ?Zero,?One;lia.
 - nia.
Qed.

Theorem literal_round384_numeric (p:Ty.tySem (Word 9)) :
 @toZ (WordToZ 7) (@literal_round384 Alg.CoreFunSem p)=
 ((@toZ (WordToZ 9) p+2^383)/2^384) mod 2^128.
Proof.
 destruct p as [[hi mid] lo].
 change (@toZ (WordToZ 7) (snd (@full_increment_word_spec Alg.CoreFunSem 7
  (@Word.leftmost Bit 7 Alg.CoreFunSem mid,hi)))=
  (((@toZ (WordToZ 7) hi*2^128+ @toZ (WordToZ 7) mid)*2^256+
   @toZ (WordToZ 8) lo+2^383)/2^384) mod 2^128).
 rewrite increment128_payload,literal_wnaf_top128,round384_integer;
 [reflexivity|apply word_toZ_range|apply word_toZ_range].
Qed.

Local Opaque literal_round384 multiply_word_spec Alg.scribe fromZ.
Theorem literal_split_coefficient_numeric first (k:Ty.tySem (Word 8)) :
 @toZ (WordToZ 7) (@literal_split_coefficient first Alg.CoreFunSem k)=
 split_coefficient first (@toZ (WordToZ 8) k).
Proof.
 change (@toZ (WordToZ 7) (@literal_round384 Alg.CoreFunSem
  (@multiply_word_spec 8 Alg.CoreFunSem (k,@Alg.scribe Ty.Unit (Word 8)
   (@fromZ (WordToZ 8) (split_multiplier_value first)) Alg.CoreFunSem tt)))=
  split_coefficient first (@toZ (WordToZ 8) k)).
 rewrite Alg.scribe_correct,literal_round384_numeric,multiply_word_spec_numeric,to_fromZ.
 change (two_power_nat (ToZ.Theory.bitSize (WordToZ 8))) with (2^256).
 rewrite (Z.mod_small (split_multiplier_value first) (2^256)) by
  (pose proof (split_multiplier_bounds first);lia).
 change (split_coefficient first (@toZ (WordToZ 8) k) mod 2^128=
  split_coefficient first (@toZ (WordToZ 8) k)).
 apply Z.mod_small;apply split_coefficient_bounds;apply word_toZ_range.
Qed.
