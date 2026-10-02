(** Byte and wide C subtraction values against the canonical program. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_read8 C.jet_add8 C.jet_add8_word.
Require Import C.jet_wide C.jet_wide_spec C.jet_toZ C.jet_predicate_spec C.jet_subtract_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition subtract8_borrow r t := Int.lt (add8_u r) (add8_u t).
Definition subtract8_payload r t := Int.zero_ext 8 (Int.sub (Int.mul Int.one (add8_u r)) (add8_u t)).
Definition wide_subtract_borrow r t := Int64.ltu r t.
Definition wide_subtract_payload r t := Int64.sub r t.

Lemma carrier_mod_word n carrier delta : 0 < carrier -> (word_modulus n | carrier) ->
  (delta mod carrier) mod word_modulus n = delta mod word_modulus n.
Proof.
  intros HC HD. symmetry. apply Znumtheory.Zmod_div_mod; [apply word_modulus_positive|exact HC|exact HD].
Qed.
Lemma subtract8_borrow_numeric r t :
  subtract8_borrow r t = (Int.unsigned (add8_u r) <? Int.unsigned (add8_u t)).
Proof.
  pose proof (add8_u_range r) as HR. pose proof (add8_u_range t) as HT.
  unfold subtract8_borrow, Int.lt.
  rewrite !Int.signed_eq_unsigned by (change Int.max_signed with 2147483647; lia).
  destruct (zlt (Int.unsigned (add8_u r)) (Int.unsigned (add8_u t)));
    symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma subtract8_payload_numeric r t :
  @toZ (WordToZ 3) (decode_word8 (Int64.repr (Int.unsigned (subtract8_payload r t)))) =
    (Int.unsigned (add8_u r) - Int.unsigned (add8_u t)) mod word_modulus 3.
Proof.
  rewrite decode_word8_of_int. unfold subtract8_payload. rewrite Int.mul_commut, Int.mul_one.
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  rewrite Z.mod_mod by lia. unfold Int.sub. rewrite Int.unsigned_repr_eq.
  change ((Int.unsigned (add8_u r) - Int.unsigned (add8_u t)) mod Int.modulus mod word_modulus 3 =
    (Int.unsigned (add8_u r) - Int.unsigned (add8_u t)) mod word_modulus 3).
  apply carrier_mod_word; [change (0 < 4294967296); lia|]. exists 16777216. reflexivity.
Qed.
Lemma subtract8_values_denote_spec left right :
  ((if subtract8_borrow (read8_result left) (read8_result right) then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned (subtract8_payload (read8_result left) (read8_result right))))) =
    @subtract_word_spec Alg.CoreFunSem 3 (decode_word8 left, decode_word8 right).
Proof.
  rewrite subtract8_borrow_numeric, !read8_result_unsigned.
  apply subtract_representation_matches. rewrite subtract8_payload_numeric, !read8_result_unsigned. reflexivity.
Qed.
Lemma wide_subtract_borrow_numeric r t : wide_subtract_borrow r t = (Int64.unsigned r <? Int64.unsigned t).
Proof.
  unfold wide_subtract_borrow, Int64.ltu.
  destruct (zlt (Int64.unsigned r) (Int64.unsigned t));
    symmetry; [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.
Lemma wide_subtract_payload_numeric s r t :
  @toZ (WordToZ (wide_log s)) (decode_wide s (Int64.zero_ext (wide_bits s) (wide_subtract_payload r t))) =
    (Int64.unsigned r - Int64.unsigned t) mod word_modulus (wide_log s).
Proof.
  assert (Hdecode : @toZ (WordToZ (wide_log s))
    (decode_wide s (Int64.zero_ext (wide_bits s) (wide_subtract_payload r t))) =
    Int64.unsigned (wide_subtract_payload r t) mod word_modulus (wide_log s)).
  { unfold decode_wide. rewrite to_fromZ. destruct s.
    - rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
      change ((Int64.unsigned (wide_subtract_payload r t) mod 65536) mod 65536 =
        Int64.unsigned (wide_subtract_payload r t) mod 65536). apply Z.mod_mod. lia.
    - rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
      change ((Int64.unsigned (wide_subtract_payload r t) mod 4294967296) mod 4294967296 =
        Int64.unsigned (wide_subtract_payload r t) mod 4294967296). apply Z.mod_mod. lia.
    - rewrite Int64.zero_ext_above by (change (64 >= 64); lia). reflexivity. }
  rewrite Hdecode. unfold wide_subtract_payload, Int64.sub. rewrite Int64.unsigned_repr_eq.
  apply carrier_mod_word; [change (0 < 18446744073709551616); lia|].
  destruct s; [exists 281474976710656|exists 4294967296|exists 1]; reflexivity.
Qed.
Lemma wide_subtract_values_denote_input s (x y : Ty.tySem (Word (wide_log s))) r t :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  Int64.unsigned t = @toZ (WordToZ (wide_log s)) y ->
  ((if wide_subtract_borrow r t then inr tt else inl tt),
    decode_wide s (Int64.zero_ext (wide_bits s) (wide_subtract_payload r t))) =
    @subtract_word_spec Alg.CoreFunSem (wide_log s) (x, y).
Proof.
  intros HR HT. rewrite wide_subtract_borrow_numeric, HR, HT.
  apply subtract_representation_matches. rewrite wide_subtract_payload_numeric, HR, HT. reflexivity.
Qed.
