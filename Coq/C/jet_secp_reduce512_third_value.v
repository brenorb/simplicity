(** Exact third-fold machine value and all actual u128 no-overflow guards. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import C.jet_secp_canonical_scalar.
Require Import C.jet_secp_reduce512_wide C.jet_secp_reduce512_symbolic
  C.jet_secp_reduce512_first_value C.jet_secp_reduce512_fold_bounds
  C.jet_secp_reduce512_third_atomic C.jet_secp_scalar_mul512_accumulate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma third_carry_bound s k : wide_value s < k * Int64.modulus -> Int64.unsigned (whi s) < k.
Proof.
  intro H; unfold wide_value in H.
  pose proof (Int64.unsigned_range (wlo s)); pose proof (Int64.unsigned_range (wtop s)).
  pose proof Int64.modulus_pos; nia.
Qed.
Lemma third_lower_split s : wtop s = Int64.zero ->
  wide_value s = Int64.unsigned (wlo s) + Int64.modulus * Int64.unsigned (whi s).
Proof. intro H; unfold wide_value; rewrite H,Int64.unsigned_zero; ring. Qed.
Section TYPED.
Variable digits : nat -> int64.
Variable p4 : int.
Lemma third_p4_unsigned : Int64.unsigned (third_ma_p4 p4) = Int.unsigned p4.
Proof.
  unfold third_ma_p4; apply Int64.unsigned_repr.
  pose proof (Int.unsigned_range p4); change Int64.max_unsigned with 18446744073709551615; 
    change Int.modulus with 4294967296 in *; lia.
Qed.
Lemma third_column_values : Int.unsigned p4 <= 2 ->
  wide_value (third_ma0 digits p4) = Int64.unsigned (digits 0%nat) + Int64.unsigned wide_C0 * Int.unsigned p4 /\
  wide_value (third_ma1 digits p4) = Int64.unsigned (whi (third_ma0 digits p4)) +
    Int64.unsigned (digits 1%nat) + Int64.unsigned wide_C1 * Int.unsigned p4 /\
  wide_value (third_ma2 digits p4) = Int64.unsigned (whi (third_ma1 digits p4)) +
    Int64.unsigned (digits 2%nat) + Int.unsigned p4 /\
  wide_value (third_ma3 digits p4) = Int64.unsigned (whi (third_ma2 digits p4)) +
    Int64.unsigned (digits 3%nat).
Proof.
  intro HP.
  pose proof (Int.unsigned_range p4) as RP.
  pose proof (Int64.unsigned_range (digits 0%nat)) as R0.
  pose proof (Int64.unsigned_range (digits 1%nat)) as R1.
  pose proof (Int64.unsigned_range (digits 2%nat)) as R2.
  pose proof (Int64.unsigned_range (digits 3%nat)) as R3.
  assert (HC0 : Int64.unsigned wide_C0 = 4624529908474429119) by reflexivity.
  assert (HC1 : Int64.unsigned wide_C1 = 4994812053365940164) by reflexivity.
  assert (HB : Int64.modulus = 18446744073709551616) by reflexivity.
  assert (H0 : wide_value (third_ma0 digits p4) = Int64.unsigned (digits 0%nat) +
      Int64.unsigned wide_C0 * Int.unsigned p4).
  { unfold third_ma0; rewrite wide_muladd_fast_value,wide_from_word_value,third_p4_unsigned; [reflexivity|reflexivity|].
    rewrite wide_from_word_value,third_p4_unsigned,HC0,HB; nia. }
  assert (B0 : Int64.unsigned (whi (third_ma0 digits p4)) < 3).
  { apply third_carry_bound; rewrite H0,HC0,HB; nia. }
  assert (HA1 : wide_value (wide_sumadd_fast (digits 1%nat)
      (wide_from_word (whi (third_ma0 digits p4)))) =
      Int64.unsigned (whi (third_ma0 digits p4)) + Int64.unsigned (digits 1%nat)).
  { rewrite wide_sumadd_fast_value,wide_from_word_value; [reflexivity|reflexivity|].
    rewrite wide_from_word_value,HB; nia. }
  assert (H1 : wide_value (third_ma1 digits p4) =
      Int64.unsigned (whi (third_ma0 digits p4)) +
      Int64.unsigned (digits 1%nat) + Int64.unsigned wide_C1 * Int.unsigned p4).
  { unfold third_ma1; rewrite wide_muladd_fast_value,HA1,third_p4_unsigned; [reflexivity|reflexivity|].
    rewrite HA1,third_p4_unsigned,HC1,HB; nia. }
  assert (B1 : Int64.unsigned (whi (third_ma1 digits p4)) < 3).
  { apply third_carry_bound; rewrite H1,HC1,HB; nia. }
  assert (HA2 : wide_value (wide_sumadd_fast (digits 2%nat)
      (wide_from_word (whi (third_ma1 digits p4)))) =
      Int64.unsigned (whi (third_ma1 digits p4)) + Int64.unsigned (digits 2%nat)).
  { rewrite wide_sumadd_fast_value,wide_from_word_value; [reflexivity|reflexivity|].
    rewrite wide_from_word_value,HB; nia. }
  assert (H2 : wide_value (third_ma2 digits p4) =
      Int64.unsigned (whi (third_ma1 digits p4)) +
      Int64.unsigned (digits 2%nat) + Int.unsigned p4).
  { unfold third_ma2; rewrite wide_sumadd_fast_value,HA2,third_p4_unsigned; [reflexivity|reflexivity|].
    rewrite HA2,third_p4_unsigned,HB; nia. }
  assert (B2 : Int64.unsigned (whi (third_ma2 digits p4)) < 2).
  { apply third_carry_bound; rewrite H2,HB; nia. }
  assert (H3 : wide_value (third_ma3 digits p4) =
      Int64.unsigned (whi (third_ma2 digits p4)) + Int64.unsigned (digits 3%nat)).
  { unfold third_ma3; rewrite wide_sumadd_fast_value,wide_from_word_value; [reflexivity|reflexivity|].
    rewrite wide_from_word_value,HB; nia. }
  exact (conj H0 (conj H1 (conj H2 H3))).
Qed.
Definition third_input_low := column_words_value [digits 0%nat; digits 1%nat; digits 2%nat; digits 3%nat].
Definition third_fold_value := third_input_low + Int.unsigned p4 * first_delta.
Lemma third_reconstruction : Int.unsigned p4 <= 2 ->
  column_words_value (third_machine_outputs digits p4) +
    reduce512_radix * Int64.unsigned (whi (third_ma3 digits p4)) = third_fold_value.
Proof.
  intro HP; destruct (third_column_values HP) as (H0 & H1 & H2 & H3).
  rewrite !third_lower_split in H0,H1,H2,H3 by reflexivity.
  unfold third_machine_outputs,third_fold_value,third_input_low,first_delta,reduce512_radix.
  cbn [column_words_value].
  change Int64.modulus with 18446744073709551616 in *.
  assert (HC0 : Int64.unsigned wide_C0 = 4624529908474429119) by reflexivity.
  assert (HC1 : Int64.unsigned wide_C1 = 4994812053365940164) by reflexivity.
  rewrite HC0 in H0; rewrite HC1 in H1; nia.
Qed.
Lemma third_fold_bound : Int.unsigned p4 <= 2 -> 0 <= third_fold_value < 2 * canonical_group_order.
Proof.
  intro HP; pose proof (Int.unsigned_range p4).
  pose proof (column_words_bound [digits 0%nat; digits 1%nat; digits 2%nat; digits 3%nat]) as HL.
  change (0 <= third_input_low < reduce512_radix) in HL.
  destruct reduce512_delta_bounds as [HD [_ [_ HN]]].
  unfold third_fold_value; nia.
Qed.
Lemma third_c_bound : Int.unsigned p4 <= 2 -> 0 <= Int64.unsigned (whi (third_ma3 digits p4)) <= 1.
Proof.
  intro HP; pose proof (third_reconstruction HP) as HE.
  pose proof (third_fold_bound HP) as HB.
  pose proof (column_words_bound (third_machine_outputs digits p4)) as HL.
  pose proof (Int64.unsigned_range (whi (third_ma3 digits p4))) as HC.
  destruct reduce512_delta_bounds as [HD _].
  pose proof reduce512_delta_order as HN.
  assert (HR : 0 < reduce512_radix) by
    (unfold reduce512_radix; change (0 < 115792089237316195423570985008687907853269984665640564039457584007913129639936); lia).
  split; [lia|nia].
Qed.
End TYPED.
