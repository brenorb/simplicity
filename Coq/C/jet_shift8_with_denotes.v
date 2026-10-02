(** Decode the exact checked fill-shift carrier to the canonical program. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_spec C.jet_word_repr C.jet_rotate_count_exec.
Require Import C.jet_shift8_with_layout_machine C.jet_shift8_with_spec C.jet_shift8_with_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift8_with_machine_denotes right fill amount x :
  shift8_with_machine_value right fill amount x =
    @shift8_with_spec right Alg.CoreFunSem (fill,(amount,x)).
Proof.
  assert (HR : Int.unsigned (Int.repr (@toZ (WordToZ 3) x)) = @toZ (WordToZ 3) x).
  { apply Int.unsigned_repr. pose proof (word_toZ_range 3 x) as H.
    change (0 <= @toZ (WordToZ 3) x < 256) in H.
    change Int.max_unsigned with 4294967295; lia. }
  assert (HA : Int.unsigned (Int.repr (@toZ (WordToZ 2) amount)) = @toZ (WordToZ 2) amount).
  { apply Int.unsigned_repr. pose proof (word_toZ_range 2 amount) as H.
    change (0 <= @toZ (WordToZ 2) amount < 16) in H.
    change Int.max_unsigned with 4294967295; lia. }
  assert (HF : Bit.fromBool (Bit.toBool fill) = fill) by (destruct fill as [[]|[]]; reflexivity).
  unfold shift8_with_machine_value.
  rewrite (shift8_with_payload_repr right (Bit.toBool fill) amount x _ _ HR HA), HF.
  set (y := @shift8_with_spec right Alg.CoreFunSem (fill,(amount,x))).
  change (decode_word8 (Int64.repr
    (Int.unsigned (Int.zero_ext 8 (Int.repr (@toZ (WordToZ 3) y))))) = y).
  pose proof (word_toZ_range 3 y) as HY.
  change (0 <= @toZ (WordToZ 3) y < 256) in HY.
  assert (HU : Int.unsigned (Int.repr (@toZ (WordToZ 3) y)) = @toZ (WordToZ 3) y).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
  rewrite byte_carrier_cast_id by (rewrite HU; exact HY).
  rewrite HU. unfold decode_word8.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  apply from_toZ.
Qed.
