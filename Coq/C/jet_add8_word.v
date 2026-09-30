(** Symbolic C-byte arithmetic and its canonical primitive Simplicity adder.
    No enumeration of the 65,536 input pairs is used. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Util.Monad.
Require Import C.jet_spec C.jet_read8 C.jet_add8 C.jet_add8_update.
Require Import C.jet_word_bits C.jet_word_decode C.jet_word_position.
Require Import C.jet_write8_position C.jet_frame_arith C.jet_frame_spec.
Require Export C.jet_toZ.
Local Open Scope Z_scope.

(** Programs.Arith.add word8 is false &&& iden >>> full_add word8. *)
Definition add8_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod Word8 Word8) (Ty.Prod Bit Word8) :=
  @Word.adder 3 term.

Definition decode_carry_word8 (w : int64) : Ty.tySem (Ty.Prod Bit Word8) :=
  ((if Int64.testbit w 8 then inr tt else inl tt), decode_word8 w).

Lemma add8_u_range r : 0 <= Int.unsigned (add8_u r) < 256.
Proof.
  unfold add8_u. rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  apply Z.mod_pos_bound. reflexivity.
Qed.

Lemma read8_result_unsigned w :
  Int.unsigned (add8_u (read8_result w)) = @toZ (WordToZ 3) (decode_word8 w).
Proof.
  unfold read8_result, add8_u.
  rewrite Int.or_commut, Int.or_zero.
  rewrite !Int.zero_ext_idem by lia.
  assert (HM : Int64.and w (Int64.repr 255) = Int64.zero_ext 8 w).
  { symmetry. apply Int64.zero_ext_and; lia. }
  rewrite HM.
  rewrite Int64.zero_ext_mod by (change (0 <= 8 < 64); lia).
  assert (HR : 0 <= Int64.unsigned w mod 256 < 256)
    by (apply Z.mod_pos_bound; lia).
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  change (Int.unsigned (Int.repr (Int64.unsigned w mod 256)) mod 256 =
    @toZ (WordToZ 3) (decode_word8 w)).
  rewrite Int.unsigned_repr by (change (0 <= Int64.unsigned w mod 256 <= 4294967295); lia).
  rewrite Z.mod_small by exact HR.
  unfold decode_word8. rewrite to_fromZ. reflexivity.
Qed.

Lemma add8_byte_unsigned r s :
  Int.unsigned (add8_byte r s) =
    (Int.unsigned (add8_u r) + Int.unsigned (add8_u s)) mod 256.
Proof.
  pose proof (add8_u_range r) as HR. pose proof (add8_u_range s) as HS.
  unfold add8_byte, add8_sum_raw.
  rewrite Int.mul_commut, Int.mul_one.
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  unfold Int.add.
  rewrite Int.unsigned_repr by
    (change (0 <= Int.unsigned (add8_u r) + Int.unsigned (add8_u s) <= 4294967295); lia).
  reflexivity.
Qed.

Lemma add8_overflow r s :
  Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r) =
    (255 <? Int.unsigned (add8_u r) + Int.unsigned (add8_u s)).
Proof.
  pose proof (add8_u_range r) as HR. pose proof (add8_u_range s) as HS.
  unfold Int.sub, Int.ltu.
  change (Int.unsigned (Int.repr 255)) with 255.
  rewrite Int.unsigned_repr by
    (change (0 <= 255 - Int.unsigned (add8_u s) <= 4294967295); lia).
  destruct (zlt (255 - Int.unsigned (add8_u s)) (Int.unsigned (add8_u r)));
    symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.

Lemma decode_word8_of_int r :
  @toZ (WordToZ 3) (decode_word8 (Int64.repr (Int.unsigned r))) =
  Int.unsigned r mod 256.
Proof.
  unfold decode_word8.
  rewrite Int64.unsigned_repr by
    (pose proof (Int.unsigned_range_2 r) as HR;
     change (0 <= Int.unsigned r <= 4294967295) in HR;
     change (0 <= Int.unsigned r <= 18446744073709551615); lia).
  rewrite to_fromZ. reflexivity.
Qed.

Lemma add8_values_denote_spec left right :
  ((if Int.ltu (Int.sub (Int.repr 255) (add8_u (read8_result right)))
       (add8_u (read8_result left)) then inr tt else inl tt),
    decode_word8 (Int64.repr (Int.unsigned (add8_byte (read8_result left) (read8_result right))))) =
  @add8_spec Alg.CoreFunSem (decode_word8 left, decode_word8 right).
Proof.
  apply (toZ_injective (PairToZ BitToZ (WordToZ 3))).
  unfold add8_spec. rewrite Word.adder_correct.
  rewrite (@toZ_Pair BitToZ (WordToZ 3)).
  rewrite add8_overflow, !read8_result_unsigned.
  rewrite decode_word8_of_int, add8_byte_unsigned, !read8_result_unsigned.
  set (a := @toZ (WordToZ 3) (decode_word8 left)).
  set (b := @toZ (WordToZ 3) (decode_word8 right)).
  assert (HA : 0 <= a < 256).
  { unfold a, decode_word8. rewrite to_fromZ. apply Z.mod_pos_bound. reflexivity. }
  assert (HB : 0 <= b < 256).
  { unfold b, decode_word8. rewrite to_fromZ. apply Z.mod_pos_bound. reflexivity. }
  change (@toZ BitToZ (if 255 <? a + b then inr tt else inl tt) * 256 +
    ((a + b) mod 256) mod 256 = a + b).
  rewrite Z.mod_mod by lia.
  destruct (255 <? a + b) eqn:HC.
  - apply Z.ltb_lt in HC.
    change (1 * 256 + (a + b) mod 256 = a + b).
    replace ((a + b) mod 256) with (a + b - 256); [lia |].
    apply Z.mod_unique with (q := 1); lia.
  - apply Z.ltb_ge in HC.
    change (0 * 256 + (a + b) mod 256 = a + b).
    rewrite Z.mod_small by lia. lia.
Qed.
Lemma add8_carry_at_bit cursor old r s :
  1 <= cursor <= 64 ->
  Int64.testbit (add8_carry_at cursor old r s) (cursor - 1) =
    Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r).
Proof.
  intros HC. unfold add8_carry_at.
  destruct (Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r)).
  - rewrite Int64.bits_or by (change (0 <= cursor - 1 < 64); lia).
    rewrite Int64.bits_shl by (change (0 <= cursor - 1 < 64); lia).
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    replace (cursor - 1 - (cursor - 1)) with 0 by lia.
    change (orb (Int64.testbit old (cursor - 1)) Datatypes.true = Datatypes.true).
    apply orb_true_r.
  - rewrite clear_low_bits by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Lemma add8_word_at_prefix cursor old r s :
  9 <= cursor <= 64 ->
  word_outside_eq 0 cursor (add8_word_at cursor old r s) old.
Proof.
  intros HC i HI [HL|HG]; [lia|].
  unfold add8_word_at. rewrite put_byte_bits by lia.
  rewrite zlt_false by lia. unfold add8_carry_at.
  destruct (Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r)).
  - rewrite Int64.bits_or by exact HI.
    rewrite Int64.bits_shl by exact HI.
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    rewrite Int64.bits_one.
    destruct (zeq (i - (cursor - 1)) 0); [lia | apply orb_false_r].
  - rewrite clear_low_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

Lemma add8_word_at_decode cursor old r s :
  9 <= cursor <= 64 ->
  decode_carry_word8
    (Int64.shru (add8_word_at cursor old r s) (Int64.repr (cursor - 9))) =
  ((if Int.ltu (Int.sub (Int.repr 255) (add8_u s)) (add8_u r)
    then inr tt else inl tt),
   decode_word8 (Int64.repr (Int.unsigned (add8_byte r s)))).
Proof.
  intros HC. unfold decode_carry_word8. f_equal.
  - rewrite Int64.bits_shru by (change (0 <= 8 < 64); lia).
    rewrite cursor_unsigned by lia.
    rewrite zlt_true by (change (8 + (cursor - 9) < 64); lia).
    replace (8 + (cursor - 9)) with (cursor - 1) by lia.
    unfold add8_word_at. rewrite put_byte_bits by lia.
    rewrite zlt_false by lia. rewrite add8_carry_at_bit by lia. reflexivity.
  - unfold add8_word_at.
    replace (cursor - 9) with (cursor - 1 - 8) by lia.
    rewrite <- decode_word8_projection, put_byte_projection by lia.
    apply decode_word8_projection.
Qed.

Lemma add8_word_at_spec cursor old left right :
  9 <= cursor <= 64 ->
  decode_carry_word8
    (Int64.shru (add8_word_at cursor old (read8_result left) (read8_result right))
      (Int64.repr (cursor - 9))) =
  @add8_spec Alg.CoreFunSem (decode_word8 left, decode_word8 right).
Proof.
  intros HC. rewrite add8_word_at_decode by exact HC.
  apply add8_values_denote_spec.
Qed.

Lemma add8_spec_parametric : Alg.Core.Parametric (@add8_spec).
Proof. intros alg1 alg2 R. apply Word.adder_Parametric. Qed.

Lemma add8_spec_initial (M : CIMonad.type) (xy : Ty.tySem (Ty.Prod Word8 Word8)) :
  @add8_spec (Alg.CoreSem M) xy = eta (@add8_spec Alg.CoreFunSem xy).
Proof. apply Alg.CoreSem_initial. exact add8_spec_parametric. Qed.
