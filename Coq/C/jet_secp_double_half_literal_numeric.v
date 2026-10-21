(** Numeric observation of the literal one-bit shift used by fe_halve. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Alg Simplicity.Ty.
Require Import C.jet_predicate_spec C.jet_vector_shift_word C.jet_secp_double_literal C.jet_secp_fe_math
  C.jet_secp_literal_add_numeric C.jet_secp_literal_add_program
  C.jet_secp_negate_literal_contract C.jet_secp_canonical_normalize
  C.jet_secp_multiply_literal_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque Word.full_right_shift1 literal_fe_add literal_fe_multiply.

Lemma bit_vector_bits n : vector_bits BitToZ n=ToZ.Theory.bitSize (WordToZ n).
Proof.
  induction n as [|n IH];[reflexivity|].
  change ((vector_bits BitToZ n+vector_bits BitToZ n)%nat=
    (ToZ.Theory.bitSize (WordToZ n)+ToZ.Theory.bitSize (WordToZ n))%nat).
  rewrite IH;reflexivity.
Qed.

Lemma double_multiplier_word_value i :
  @toZ (WordToZ 8) (double_multiplier_word i)=i mod feP.
Proof.
  unfold double_multiplier_word;rewrite to_fromZ;apply Z.mod_small.
  change (0<=i mod feP<word_modulus 8).
  pose proof canonical_field_order_range as [[HP HW] _].
  rewrite canonical_field_order_matches_limb_model in HP,HW.
  pose proof (Z.mod_pos_bound i feP HP);lia.
Qed.
Local Opaque double_multiplier_word.
Lemma literal_fe_multiply_int_step i (a : Ty.tySem (Word 8)) :
  @literal_fe_multiply_int i Alg.CoreFunSem a=
    @literal_fe_multiply Alg.CoreFunSem (double_multiplier_word i,a).
Proof.
  change (@literal_fe_multiply Alg.CoreFunSem
    (@Alg.scribe (Word 8) (Word 8) (double_multiplier_word i) Alg.CoreFunSem a,a)=
    @literal_fe_multiply Alg.CoreFunSem (double_multiplier_word i,a)).
  rewrite Alg.scribe_correct;reflexivity.
Qed.
Theorem literal_fe_multiply_int_numeric i (a : Ty.tySem (Word 8)) :
  @toZ (WordToZ 8) (@literal_fe_multiply_int i Alg.CoreFunSem a)=
    (i*@toZ (WordToZ 8) a) mod feP.
Proof.
  rewrite literal_fe_multiply_int_step,literal_multiply_numeric,double_multiplier_word_value.
  apply Z.mul_mod_idemp_l;pose proof canonical_field_order_range as [[HP _] _].
  rewrite canonical_field_order_matches_limb_model in HP;lia.
Qed.
Lemma bit_vector_value n (a : Ty.tySem (Word n)) :
  vector_value BitToZ n a=@toZ (WordToZ n) a.
Proof.
  induction n as [|n IH];[reflexivity|];destruct a as [hi lo].
  change (vector_value BitToZ n hi*two_power_nat (vector_bits BitToZ n)+vector_value BitToZ n lo=
    @toZ (WordToZ n) hi*two_power_nat (ToZ.Theory.bitSize (WordToZ n))+@toZ (WordToZ n) lo).
  rewrite !IH,bit_vector_bits;reflexivity.
Qed.

Lemma double_half_shift_value (a : Ty.tySem (Word 8)) :
  let r := @Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a) in
  @toZ (WordToZ 8) a = 2 * @toZ (WordToZ 8) (fst r) + @toZ BitToZ (snd r).
Proof.
  pose proof (full_right_shift1_value BitToZ 8 (inl tt) a) as HShift.
  cbn zeta in HShift;rewrite !bit_vector_value in HShift.
  change (@toZ (WordToZ 8) a =
    @toZ (WordToZ 8) (fst (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a))) * 2 +
    @toZ BitToZ (snd (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)))) in HShift.
  cbn zeta;rewrite (Z.mul_comm _ 2) in HShift;exact HShift.
Qed.
Lemma literal_fe_halve_step (a : Ty.tySem (Word 8)) :
  let r := @Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a) in
  @literal_fe_halve Alg.CoreFunSem a =
    if Bit.toBool (snd r) then @literal_fe_add Alg.CoreFunSem (double_half_word,fst r) else fst r.
Proof.
  change ((match snd (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)) with
    | inl _ => fst (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a))
    | inr _ => @literal_fe_add Alg.CoreFunSem
        (@Alg.scribe Ty.Unit (Word 8) double_half_word Alg.CoreFunSem tt,
         fst (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)))
    end)=if Bit.toBool (snd (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)))
      then @literal_fe_add Alg.CoreFunSem (double_half_word,fst (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)))
      else fst (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a))).
  rewrite Alg.scribe_correct.
  destruct (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)) as [q r].
  destruct r as [u|u];destruct u;reflexivity.
Qed.

Lemma double_half_constant :
  0<=((feP+1)/2)<feP /\ 2*((feP+1)/2)=feP+1.
Proof. vm_compute;repeat split;try reflexivity;discriminate. Qed.
Lemma double_half_word_value : @toZ (WordToZ 8) double_half_word=(feP+1)/2.
Proof.
  unfold double_half_word;rewrite to_fromZ;apply Z.mod_small.
  change (0<=(feP+1)/2<word_modulus 8).
  pose proof double_half_constant as [HC _].
  pose proof canonical_field_order_range as [[HP HW] _].
  rewrite canonical_field_order_matches_limb_model in HP,HW;lia.
Qed.

Theorem literal_fe_halve_range (a : Ty.tySem (Word 8)) :
  0<=@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a)<feP.
Proof.
  pose proof (double_half_shift_value a) as HShift;cbn zeta in HShift.
  rewrite literal_fe_halve_step.
  destruct (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)) as [q r] eqn:HR.
  cbn [fst snd] in HShift|-*.
  destruct r as [u|u];destruct u.
  - change (@toZ (WordToZ 8) a=2*@toZ (WordToZ 8) q+0) in HShift.
    pose proof (word_value_bounds 8 a) as BA;pose proof (word_value_bounds 8 q) as BQ.
    pose proof canonical_field_order_range as [[HP HW] HT].
    rewrite canonical_field_order_matches_limb_model in HP,HW,HT.
    change (0<=@toZ (WordToZ 8) q<feP);lia.
  - change (0<=@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (double_half_word,q))<feP).
    rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model.
    apply Z.mod_pos_bound;pose proof canonical_field_order_range as [[HP _] _].
    rewrite canonical_field_order_matches_limb_model in HP;exact HP.
Qed.

Theorem literal_fe_halve_double (a : Ty.tySem (Word 8)) :
  (2*@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem a)) mod feP=
  @toZ (WordToZ 8) a mod feP.
Proof.
  pose proof (double_half_shift_value a) as HShift;cbn zeta in HShift.
  rewrite literal_fe_halve_step.
  destruct (@Word.full_right_shift1 Bit 8 Alg.CoreFunSem (inl tt,a)) as [q r] eqn:HR.
  cbn [fst snd] in HShift|-*.
  destruct r as [u|u];destruct u.
  - change (@toZ (WordToZ 8) a=2*@toZ (WordToZ 8) q+0) in HShift.
    change ((2*@toZ (WordToZ 8) q) mod feP=@toZ (WordToZ 8) a mod feP).
    replace (2*@toZ (WordToZ 8) q) with (@toZ (WordToZ 8) a) by lia;reflexivity.
  - change (@toZ (WordToZ 8) a=2*@toZ (WordToZ 8) q+1) in HShift.
    change ((2*@toZ (WordToZ 8) (@literal_fe_add Alg.CoreFunSem (double_half_word,q))) mod feP=
      @toZ (WordToZ 8) a mod feP).
    rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,double_half_word_value.
    pose proof double_half_constant as [_ HC].
    assert (HP : feP<>0) by (pose proof canonical_field_order_range as [[HP _] _];
      rewrite canonical_field_order_matches_limb_model in HP;lia).
    rewrite Z.mul_mod_idemp_r by exact HP.
    replace (2*((feP+1)/2+@toZ (WordToZ 8) q)) with (@toZ (WordToZ 8) a+1*feP) by lia.
    rewrite Z.mod_add by exact HP;reflexivity.
Qed.
