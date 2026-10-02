(** Literal canonical right padding/extension, for the next actual C consumers.
    Reuses the checked fill/constant/byte-sequence infrastructure. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jet_spec C.jet_encoding C.jet_word_bit_spec C.jet_int32_bit_mask.
Require Import C.jet_extend_word_spec C.jet_extend_word8_exec C.jet_extend_word8_loop.
Require Import C.jet_right_extend_word8_loop C.jet_extend_bit8_exec C.jet_write8_sequence.
Import ListNotations.
Module RC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint right_pad_word_spec n d (high : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) (Vector (Word n) d) :=
  match d with
  | O => RC.iden
  | S d => RC.pair (right_pad_word_spec n d high)
      (@Word.fill (Word n) (Word n) d term (RC.comp RC.unit (pad_word_constant n high)))
  end.
Definition right_extend_word_spec n d {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) (Vector (Word n) d) :=
  RC.comp (RC.pair (@Word.rightmost Bit n term) RC.iden)
    (Bit.cond (right_pad_word_spec n d Datatypes.true) (right_pad_word_spec n d Datatypes.false)).
Lemma right_pad_word_spec_parametric n d high : Alg.Core.Parametric (@right_pad_word_spec n d high).
Proof.
  intros alg1 alg2 R. induction d; cbn [right_pad_word_spec].
  - apply Alg.iden_Parametric.
  - apply Alg.pair_Parametric; [exact IHd|]. apply Word.fill_Parametric.
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply pad_word_constant_parametric].
Qed.
Lemma right_extend_word_spec_parametric n d : Alg.Core.Parametric (@right_extend_word_spec n d).
Proof.
  intros alg1 alg2 R. unfold right_extend_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Word.rightmost_Parametric|apply Alg.iden_Parametric].
  - apply Bit.cond_Parametric; apply right_pad_word_spec_parametric.
Qed.
Lemma encode_right_pad_word_spec n d high (x : Ty.tySem (Word n)) :
  encode (@right_pad_word_spec n d high Alg.CoreFunSem x) =
    encode x ++ concat (repeat (encode (@pad_word_constant n high Alg.CoreFunSem tt)) (Nat.pow 2 d - 1)).
Proof.
  induction d.
  - change (encode x = encode x ++ []); rewrite app_nil_r; reflexivity.
  - change (encode (@right_pad_word_spec n d high Alg.CoreFunSem x) ++
      encode (@Word.fill (Word n) (Word n) d Alg.CoreFunSem
        (RC.comp RC.unit (pad_word_constant n high)) x) =
      encode x ++ concat (repeat (encode (@pad_word_constant n high Alg.CoreFunSem tt))
        (Nat.pow 2 (S d) - 1))).
    rewrite IHd, encode_vector_fill. cbn -[Nat.pow pad_word_constant repeat concat encode].
    rewrite <- app_assoc, <- concat_app, <- repeat_app.
    replace (Nat.pow 2 (S d) - 1)%nat with ((Nat.pow 2 d - 1) + Nat.pow 2 d)%nat.
    + reflexivity.
    + pose proof (Nat.pow_nonzero 2 d ltac:(lia)); cbn [Nat.pow]; lia.
Qed.
Lemma right_extend_word8_lsb_denotes (x : Ty.tySem (Word 3)) r :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  right_extend_word8_lsb r = Bit.toBool (@Word.rightmost Bit 3 Alg.CoreFunSem x).
Proof.
  intros Hr. unfold right_extend_word8_lsb.
  change (negb (Int.eq (Int.and r (Int.repr (2 ^ 0))) Int.zero) =
    Bit.toBool (@Word.rightmost Bit 3 Alg.CoreFunSem x)).
  rewrite int32_single_bit_mask_nonzero by lia. unfold Int.testbit; rewrite Hr.
  change (Z.testbit (@toZ (WordToZ 3) x) 0 = Bit.toBool (@word_bit_spec 3 0 Alg.CoreFunSem x)).
  symmetry. exact (word_bit_spec_numeric 3 0 x ltac:(cbn; lia)).
Qed.
Definition right_extend_word8_output_args s r := [extend_word8_payload r] ++
  repeat (extend_bit8_arg (right_extend_word8_lsb (extend_word8_payload r)))
    (Z.to_nat (extend_word8_count s)).
Lemma right_extend_word8_args_length s r :
  8 * Z.of_nat (length (right_extend_word8_output_args s r)) = extend_word8_bits s.
Proof. unfold right_extend_word8_output_args; rewrite app_length, repeat_length; destruct s; reflexivity. Qed.
Lemma right_extend_word8_sequence_denotes s (x : Ty.tySem (Word 3)) r :
  Int.unsigned (extend_word8_payload r) = @toZ (WordToZ 3) x ->
  decode_word8 (Int64.repr (Int.unsigned (extend_word8_payload r))) = x ->
  byte_sequence_cells (right_extend_word8_output_args s r) =
    encode (@right_extend_word_spec 3 (extend_word8_depth s) Alg.CoreFunSem x).
Proof.
  intros Hr Hdecode. unfold byte_sequence_cells, right_extend_word8_output_args.
  rewrite map_app, concat_app, map_repeat. cbn [map concat]. rewrite app_nil_r.
  rewrite extend_word8_constant_decode, Hdecode.
  pose proof (right_extend_word8_lsb_denotes x (extend_word8_payload r) Hr) as HB.
  change (encode x ++ concat (repeat
    (encode (@pad_word_constant 3 (right_extend_word8_lsb (extend_word8_payload r)) Alg.CoreFunSem tt))
    (Z.to_nat (extend_word8_count s))) =
    encode (match @Word.rightmost Bit 3 Alg.CoreFunSem x with
      | inl _ => @right_pad_word_spec 3 (extend_word8_depth s) Datatypes.false Alg.CoreFunSem x
      | inr _ => @right_pad_word_spec 3 (extend_word8_depth s) Datatypes.true Alg.CoreFunSem x end)).
  destruct (@Word.rightmost Bit 3 Alg.CoreFunSem x) as [[]|[]] eqn:Hbit;
    cbn [Bit.toBool] in HB; rewrite HB;
    rewrite encode_right_pad_word_spec; destruct s; reflexivity.
Qed.
