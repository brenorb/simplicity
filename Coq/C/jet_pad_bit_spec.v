(** Canonical Programs.Word padding/extension terms for the next bit-input
    jet consumers. These bridges alone do not count as C jet equivalence. *)
From Coq Require Import ZArith Bool.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_wide C.jet_wide_spec C.jet_readBit_layout C.jet_word_decode.
Module AC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

(** Programs.Word.hs:145-152: recurse on the high half, fill the low half. *)
Fixpoint right_pad_low_1_n n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Bit (Word n) :=
  match n with
  | O => AC.iden
  | S n => AC.pair (right_pad_low_1_n n)
      (fill (n := n) (AC.comp AC.unit Bit.false))
  end.

(** Programs.Word.hs:129-139: fill the high half, recurse on the low half. *)
Fixpoint left_pad_high_1_n n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Bit (Word n) :=
  match n with
  | O => AC.iden
  | S n => AC.pair (fill (n := n) (AC.comp AC.unit Bit.true)) (left_pad_high_1_n n)
  end.

(** leftmost word1 is iden; retain the literal conditional padding composition. *)
Definition left_extend_bit_spec n {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Bit (Word n) :=
  AC.comp (AC.pair AC.iden AC.iden)
    (Bit.cond (left_pad_high_1_n n) (@left_pad_low_1_n term n)).

Lemma right_pad_low_1_n_parametric n : Alg.Core.Parametric (@right_pad_low_1_n n).
Proof.
  intros alg1 alg2 R. induction n; cbn [right_pad_low_1_n].
  - apply Alg.iden_Parametric.
  - apply Alg.pair_Parametric; [exact IHn|]. apply fill_Parametric.
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Bit.false_Parametric].
Qed.
Lemma left_pad_high_1_n_parametric n : Alg.Core.Parametric (@left_pad_high_1_n n).
Proof.
  intros alg1 alg2 R. induction n; cbn [left_pad_high_1_n].
  - apply Alg.iden_Parametric.
  - apply Alg.pair_Parametric; [|exact IHn]. apply fill_Parametric.
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Bit.true_Parametric].
Qed.
Lemma left_extend_bit_spec_parametric n : Alg.Core.Parametric (@left_extend_bit_spec n).
Proof.
  intros alg1 alg2 R. unfold left_extend_bit_spec. apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric; apply Alg.iden_Parametric.
  - apply Bit.cond_Parametric; [apply left_pad_high_1_n_parametric|apply left_pad_low_1_n_parametric].
Qed.

Definition right_pad_bit_long s b := Int64.shl (bit_long b) (Int64.repr (wide_bits s - 1)).
Definition extend_bit_long s (b : bool) :=
  if b then Int64.repr (2 ^ wide_bits s - 1) else Int64.zero.

Lemma right_pad_bit_wide_decode s (x : Ty.tySem Bit) :
  decode_wide s (Int64.zero_ext (wide_bits s) (right_pad_bit_long s (Bit.toBool x))) =
    @right_pad_low_1_n (wide_log s) Alg.CoreFunSem x.
Proof. destruct s, x as [[]|[]]; vm_compute; reflexivity. Qed.
Lemma right_pad_bit8_decode (x : Ty.tySem Bit) :
  decode_word8 (Int64.repr (Int.unsigned (Int.shl (bit_int (Bit.toBool x)) (Int.repr 7)))) =
    @right_pad_low_1_n 3 Alg.CoreFunSem x.
Proof. destruct x as [[]|[]]; vm_compute; reflexivity. Qed.
Lemma extend_bit_wide_decode s (x : Ty.tySem Bit) :
  decode_wide s (Int64.zero_ext (wide_bits s) (extend_bit_long s (Bit.toBool x))) =
    @left_extend_bit_spec (wide_log s) Alg.CoreFunSem x.
Proof. destruct s, x as [[]|[]]; vm_compute; reflexivity. Qed.
Lemma extend_bit8_decode (x : Ty.tySem Bit) :
  decode_word8 (Int64.repr (Int.unsigned (if Bit.toBool x then Int.repr 255 else Int.zero))) =
    @left_extend_bit_spec 3 Alg.CoreFunSem x.
Proof. destruct x as [[]|[]]; vm_compute; reflexivity. Qed.
