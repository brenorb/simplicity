(** Literal canonical Programs.Word.left_pad_pad/left_extend, generalized
    over the input width and doubling depth. These support actual C proofs. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Import C.jet_encoding C.jet_word_repr C.jet_word_bit_spec C.jet_int64_bit_mask.
Require Import C.jet_spec C.jet_read8 C.jet_add8_word C.jet_constant.
Require Import C.jet_extend_word8_loop C.jet_extend_word8_exec C.jet_extend_bit8_exec C.jet_write8_sequence.
Import ListNotations.
Module EC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition pad_word_constant n (high : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Ty.Unit (Word n) :=
  if high then @Word.fill Ty.Unit Bit n term Bit.true else @Word.zero n term.
Fixpoint left_pad_word_spec n d (high : bool) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) (Vector (Word n) d) :=
  match d with
  | O => EC.iden
  | S d => EC.pair (@Word.fill (Word n) (Word n) d term (EC.comp EC.unit (pad_word_constant n high)))
      (left_pad_word_spec n d high)
  end.
Definition left_extend_word_spec n d {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Word n) (Vector (Word n) d) :=
  EC.comp (EC.pair (@Word.leftmost Bit n term) EC.iden)
    (Bit.cond (left_pad_word_spec n d Datatypes.true) (left_pad_word_spec n d Datatypes.false)).

Lemma pad_word_constant_parametric n high : Alg.Core.Parametric (@pad_word_constant n high).
Proof.
  intros alg1 alg2 R. unfold pad_word_constant; destruct high;
    [apply Word.fill_Parametric; apply Bit.true_Parametric|apply zero_Parametric].
Qed.
Lemma left_pad_word_spec_parametric n d high : Alg.Core.Parametric (@left_pad_word_spec n d high).
Proof.
  intros alg1 alg2 R. induction d; cbn [left_pad_word_spec].
  - apply Alg.iden_Parametric.
  - apply Alg.pair_Parametric; [|exact IHd]. apply Word.fill_Parametric.
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply pad_word_constant_parametric].
Qed.
Lemma left_extend_word_spec_parametric n d : Alg.Core.Parametric (@left_extend_word_spec n d).
Proof.
  intros alg1 alg2 R. unfold left_extend_word_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; [apply Word.leftmost_Parametric|apply Alg.iden_Parametric].
  - apply Bit.cond_Parametric; apply left_pad_word_spec_parametric.
Qed.

Lemma encode_vector_fill A X d (t : @Alg.Core.domain Alg.CoreFunSem A X) x :
  @encode (Vector X d) (@Word.fill A X d Alg.CoreFunSem t x) =
    concat (repeat (@encode X (t x)) (Nat.pow 2 d)).
Proof.
  induction d.
  - change (encode (t x) = encode (t x) ++ []). rewrite app_nil_r; reflexivity.
  - change (encode (@Word.fill A X d Alg.CoreFunSem t x) ++
      encode (@Word.fill A X d Alg.CoreFunSem t x) =
      concat (repeat (encode (t x)) (Nat.pow 2 (S d)))).
    rewrite !IHd. replace (Nat.pow 2 (S d)) with (Nat.pow 2 d + Nat.pow 2 d)%nat by (cbn; lia).
    rewrite repeat_app, concat_app; reflexivity.
Qed.
Lemma encode_left_pad_word_spec n d high (x : Ty.tySem (Word n)) :
  encode (@left_pad_word_spec n d high Alg.CoreFunSem x) =
    concat (repeat (encode (@pad_word_constant n high Alg.CoreFunSem tt)) (Nat.pow 2 d - 1)) ++ encode x.
Proof.
  induction d.
  - reflexivity.
  - change (encode (@Word.fill (Word n) (Word n) d Alg.CoreFunSem
        (EC.comp EC.unit (pad_word_constant n high)) x) ++
      encode (@left_pad_word_spec n d high Alg.CoreFunSem x) =
      concat (repeat (encode (@pad_word_constant n high Alg.CoreFunSem tt))
        (Nat.pow 2 (S d) - 1)) ++ encode x).
    rewrite encode_vector_fill, IHd. cbn -[Nat.pow pad_word_constant repeat concat encode].
    rewrite app_assoc, <- concat_app, <- repeat_app.
    replace (Nat.pow 2 (S d) - 1)%nat with (Nat.pow 2 d + (Nat.pow 2 d - 1))%nat.
    + reflexivity.
    + pose proof (Nat.pow_nonzero 2 d ltac:(lia)); cbn [Nat.pow]; lia.
Qed.

Lemma extend_word8_msb_denotes (x : Ty.tySem Word8) r :
  Int.unsigned r = @toZ (WordToZ 3) x ->
  extend_word8_msb r = Bit.toBool (@Word.leftmost Bit 3 Alg.CoreFunSem x).
Proof.
  intros Hr. pose proof (word_toZ_range 3 x) as HX.
  change (0 <= @toZ (WordToZ 3) x < 256) in HX.
  assert (HB : Bit.toBool (@Word.leftmost Bit 3 Alg.CoreFunSem x) = Z.testbit (@toZ (WordToZ 3) x) 7).
  { change (Bit.toBool (@word_bit_spec 3 7 Alg.CoreFunSem x) = Z.testbit (@toZ (WordToZ 3) x) 7).
    exact (word_bit_spec_numeric 3 7 x ltac:(cbn; lia)). }
  rewrite HB, (top_bit_threshold _ 7 ltac:(lia) HX).
  unfold extend_word8_msb. rewrite Int.shr_div_two_p, Int.signed_eq_unsigned by
    (rewrite Hr; change Int.max_signed with 2147483647; lia).
  rewrite Hr. change (negb (Int.eq (Int.repr (@toZ (WordToZ 3) x / 128)) Int.zero) =
    negb (@toZ (WordToZ 3) x <? 128)).
  destruct (@toZ (WordToZ 3) x <? 128) eqn:HL.
  - apply Z.ltb_lt in HL. rewrite Z.div_small by lia; reflexivity.
  - apply Z.ltb_ge in HL.
    assert (HQ : @toZ (WordToZ 3) x / 128 = 1).
    { symmetry. apply Z.div_unique with (r := @toZ (WordToZ 3) x - 128); lia. }
    rewrite HQ; reflexivity.
Qed.
Lemma extend_word8_constant_decode bit :
  decode_word8 (Int64.repr (Int.unsigned (extend_bit8_arg bit))) =
    @pad_word_constant 3 bit Alg.CoreFunSem tt.
Proof. destruct bit; vm_compute; reflexivity. Qed.

Definition extend_word8_depth s := match s with E8to16 => 1%nat | E8to32 => 2%nat | E8to64 => 3%nat end.
Lemma extend_word8_args_length s r :
  8 * Z.of_nat (length (extend_word8_output_args s r)) = extend_word8_bits s.
Proof. unfold extend_word8_output_args; rewrite app_length, repeat_length; destruct s; reflexivity. Qed.

Lemma extend_word8_sequence_denotes s (x : Ty.tySem Word8) r :
  Int.unsigned (extend_word8_payload r) = @toZ (WordToZ 3) x ->
  decode_word8 (Int64.repr (Int.unsigned (extend_word8_payload r))) = x ->
  byte_sequence_cells (extend_word8_output_args s r) =
    encode (@left_extend_word_spec 3 (extend_word8_depth s) Alg.CoreFunSem x).
Proof.
  intros Hr Hdecode. unfold byte_sequence_cells, extend_word8_output_args.
  rewrite map_app, concat_app, map_repeat. cbn [map concat]. rewrite app_nil_r.
  rewrite extend_word8_constant_decode, Hdecode.
  pose proof (extend_word8_msb_denotes x (extend_word8_payload r) Hr) as HB.
  change (concat (repeat
    (encode (@pad_word_constant 3 (extend_word8_msb (extend_word8_payload r)) Alg.CoreFunSem tt))
    (Z.to_nat (extend_word8_count s))) ++ encode x =
    encode (match @Word.leftmost Bit 3 Alg.CoreFunSem x with
      | inl _ => @left_pad_word_spec 3 (extend_word8_depth s) Datatypes.false Alg.CoreFunSem x
      | inr _ => @left_pad_word_spec 3 (extend_word8_depth s) Datatypes.true Alg.CoreFunSem x end)).
  destruct (@Word.leftmost Bit 3 Alg.CoreFunSem x) as [[]|[]] eqn:Hbit;
    cbn [Bit.toBool] in HB; rewrite HB;
    rewrite encode_left_pad_word_spec; destruct s; reflexivity.
Qed.
