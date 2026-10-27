(** Canonical C scalar encodings of every literal signed Word128 state.
    The negative endpoint -2^128 is included. These adapters describe the
    unchanged input representation; they do not alter the literal program. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_predicate_spec C.jet_secp_wnaf_literal_signed
 C.jet_secp_canonical_scalar.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wnaf5_input_sign (sb:Ty.tySem Bit) : Z :=
 match sb with inl _=>1 | inr _=> -1 end.
Definition wnaf5_input_magnitude (sb:Ty.tySem Bit) (word:Ty.tySem (Word 7)) : Z :=
 match sb with inl _=> @toZ (WordToZ 7) word
 | inr _=>2^128- @toZ (WordToZ 7) word end.
Definition wnaf5_input_scalar (sb:Ty.tySem Bit) (word:Ty.tySem (Word 7)) : Z :=
 match sb with inl _=> @toZ (WordToZ 7) word
 | inr _=>canonical_group_order-(2^128- @toZ (WordToZ 7) word) end.

Lemma wnaf5_input_sign_cases sb : wnaf5_input_sign sb=1 \/ wnaf5_input_sign sb= -1.
Proof. destruct sb;[left|right];reflexivity. Qed.
Lemma wnaf5_input_magnitude_range sb word : 0<=wnaf5_input_magnitude sb word<2^129.
Proof.
 pose proof (word_value_bounds 7 word) as W.
 change (0<= @toZ (WordToZ 7) word<2^128) in W.
 destruct sb;cbn [wnaf5_input_magnitude];lia.
Qed.
Lemma wnaf5_input_signed_value sb word :
 literal_wnaf_signed_value sb word=wnaf5_input_sign sb*wnaf5_input_magnitude sb word.
Proof.
 unfold literal_wnaf_signed_value;destruct sb as [u|u];destruct u;
 [change (@toZ BitToZ (inl tt)) with 0|change (@toZ BitToZ (inr tt)) with 1];
 cbn [wnaf5_input_sign wnaf5_input_magnitude];ring.
Qed.
Lemma wnaf5_input_positive word :
 0<=wnaf5_input_scalar (inl tt) word<2^255 /\
 wnaf5_input_scalar (inl tt) word=wnaf5_input_magnitude (inl tt) word.
Proof.
 pose proof (word_value_bounds 7 word) as W.
 change (0<= @toZ (WordToZ 7) word<2^128) in W.
 cbn [wnaf5_input_scalar wnaf5_input_magnitude];split;[lia|reflexivity].
Qed.
Lemma wnaf5_input_negative word :
 2^255<=wnaf5_input_scalar (inr tt) word<canonical_group_order /\
 (-wnaf5_input_scalar (inr tt) word) mod canonical_group_order=
 wnaf5_input_magnitude (inr tt) word.
Proof.
 pose proof (word_value_bounds 7 word) as W.
 change (0<= @toZ (WordToZ 7) word<2^128) in W.
 assert (Order:2^255+2^128<canonical_group_order).
 { unfold canonical_group_order;lia. }
 cbn [wnaf5_input_scalar wnaf5_input_magnitude];split;[lia|].
 replace (-(canonical_group_order-(2^128- @toZ (WordToZ 7) word))) with
  ((2^128- @toZ (WordToZ 7) word)+(-1)*canonical_group_order) by ring.
 rewrite Z.mod_add by lia;apply Z.mod_small;lia.
Qed.
