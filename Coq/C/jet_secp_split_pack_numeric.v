(** Literal split_lambda sign selection agrees with every small signed residue.
    The original msb/subtraction/low-half program is retained. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_toZ C.jet_predicate_spec C.jet_subtract_spec
 C.jet_secp_canonical_scalar C.jet_secp_split_literal C.jet_secp_split_half_numeric
 C.jet_word_bit_spec C.jet_int64_bit_mask.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque subtract_word_spec Alg.scribe.

Lemma literal_split_pack_half_step word :
 @literal_split_pack_half Alg.CoreFunSem word=
 match @Word.leftmost Bit 8 Alg.CoreFunSem word with
 | inl _ => (Bit.zero,snd word)
 | inr _ => (Bit.one,snd (snd (@subtract_word_spec Alg.CoreFunSem 8 (word,canonical_group_word))))
 end.
Proof.
 unfold literal_split_pack_half.
 change ((match @Word.leftmost Bit 8 Alg.CoreFunSem word with
 | inl _ => (Bit.zero,snd word)
 | inr _ => (Bit.one,snd (snd (@subtract_word_spec Alg.CoreFunSem 8
    (word,@Alg.scribe Ty.Unit (Word 8) canonical_group_word Alg.CoreFunSem tt))))
 end)=match @Word.leftmost Bit 8 Alg.CoreFunSem word with
 | inl _ => (Bit.zero,snd word)
 | inr _ => (Bit.one,snd (snd (@subtract_word_spec Alg.CoreFunSem 8 (word,canonical_group_word))))
 end).
 rewrite Alg.scribe_correct;reflexivity.
Qed.
Lemma literal_split_top_cases word :
 (@Word.leftmost Bit 8 Alg.CoreFunSem word=Bit.zero /\ @toZ (WordToZ 8) word<2^255) \/
 (@Word.leftmost Bit 8 Alg.CoreFunSem word=Bit.one /\ 2^255<= @toZ (WordToZ 8) word).
Proof.
 pose proof (word_bit_spec_numeric 8 255 word ltac:(cbn;lia)) as Top.
 change (Bit.toBool (@Word.leftmost Bit 8 Alg.CoreFunSem word)=Z.testbit (@toZ (WordToZ 8) word) 255) in Top.
 pose proof (word_value_bounds 8 word) as Bounds.
 change (0<= @toZ (WordToZ 8) word<2^256) in Bounds.
 rewrite (top_bit_threshold _ 255 ltac:(lia) Bounds) in Top.
 destruct (@toZ (WordToZ 8) word <? 2^255) eqn:Small;
  destruct (@Word.leftmost Bit 8 Alg.CoreFunSem word) as [u|u];destruct u;
  cbn in Top;try discriminate.
 - left;split;[reflexivity|apply Z.ltb_lt;exact Small].
 - right;split;[reflexivity|apply Z.ltb_ge;exact Small].
Qed.
Lemma split_small_residue z : -2^128<z<2^128 ->
 z mod canonical_group_order=(if z <? 0 then canonical_group_order+z else z).
Proof.
 intro Small.
 assert (N:2^128<canonical_group_order) by (unfold canonical_group_order;lia).
 destruct (z <? 0) eqn:Neg.
 - apply Z.ltb_lt in Neg;symmetry;apply Z.mod_unique with (q:= -1);[left;lia|ring].
 - apply Z.ltb_ge in Neg;apply Z.mod_small;lia.
Qed.

Lemma split_low_positive hi lo : 0<=hi<2^128 -> 0<=lo<2^128 ->
 hi*2^128+lo<2^128 -> lo=hi*2^128+lo.
Proof. intros Hi Lo Small;lia. Qed.
Lemma split_positive_half (word:Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) word<2^128 -> split_half_signed (Bit.zero,snd word)= @toZ (WordToZ 8) word.
Proof.
 intro Small;change (@toZ (WordToZ 7) (snd word)-2^128*0= @toZ (WordToZ 8) word).
 rewrite Z.mul_0_r,Z.sub_0_r.
 rewrite split_word_value in Small|-*.
 apply split_low_positive;[apply word_value_bounds|apply word_value_bounds|exact Small].
Qed.
Lemma split_borrow_negative (p:Ty.tySem (Ty.Prod Bit (Word 8))) delta :
 delta<0 -> borrow_word_balance 8 p=delta -> fst p=Bit.one.
Proof.
 destruct p as [sg payload];intros Negative Balance.
 pose proof (word_value_bounds 8 payload) as Bounds.
 destruct sg as [u|u];destruct u;[|reflexivity].
 change (@toZ (WordToZ 8) payload-word_modulus 8*0=delta) in Balance;lia.
Qed.
Local Opaque literal_split_pack_half.
Theorem literal_split_pack_half_numeric word z :
 -2^128<z<2^128 -> @toZ (WordToZ 8) word=z mod canonical_group_order ->
 split_half_signed (@literal_split_pack_half Alg.CoreFunSem word)=z.
Proof.
 intros Small Value.
 pose proof (literal_split_top_cases word) as Top.
 pose proof (split_small_residue z Small) as Residue.
 assert (N:2^255+2^128<canonical_group_order<2^256) by (unfold canonical_group_order;lia).
 rewrite Residue in Value;destruct (z <? 0) eqn:Neg.
 - apply Z.ltb_lt in Neg.
   assert (TopOne:@Word.leftmost Bit 8 Alg.CoreFunSem word=Bit.one).
   { destruct Top as [[Hsign Hbound] | [Hsign Hbound]];[exfalso;lia|exact Hsign]. }
   rewrite literal_split_pack_half_step,TopOne.
   assert (Difference:@toZ (WordToZ 8) word- @toZ (WordToZ 8) canonical_group_word=z).
   { rewrite canonical_group_word_value;lia. }
   assert (Borrow:fst (@subtract_word_spec Alg.CoreFunSem 8 (word,canonical_group_word))=Bit.one).
   { eapply split_borrow_negative;[exact Neg|].
     rewrite subtract_word_spec_numeric;exact Difference. }
   pose proof (split_subtract_half_numeric word canonical_group_word ltac:(rewrite Difference;exact Small)) as Half.
   pose (result:=@subtract_word_spec Alg.CoreFunSem 8 (word,canonical_group_word)).
   pose proof (f_equal (fun s=>split_half_signed (s,snd (snd result))) Borrow) as Transport.
   exact (eq_trans (eq_sym Transport) (eq_trans Half Difference)).
 - apply Z.ltb_ge in Neg.
   assert (TopZero:@Word.leftmost Bit 8 Alg.CoreFunSem word=Bit.zero).
   { destruct Top as [[Hsign Hbound] | [Hsign Hbound]];[exact Hsign|exfalso;lia]. }
   rewrite literal_split_pack_half_step,TopZero.
   rewrite split_positive_half by lia;exact Value.
Qed.

