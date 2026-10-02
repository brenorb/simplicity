(** Actual LP64 shift_32 result denotes the literal canonical program. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_rotate_count_exec.
Require Import C.jet_shift_wide_helper_exec C.jet_shift_wide_bits.
Require Import C.jet_shift_byte_layout_machine C.jet_left_rotate_wide_exec C.jet_shift32_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma shift32_machine_denotes right amount x :
  shift_byte_machine_value R32 right amount x = @shift32_plain_spec right Alg.CoreFunSem (amount,x).
Proof.
  pose proof (word_toZ_range 3 amount) as HA. change (0 <= @toZ (WordToZ 3) amount < 256) in HA.
  pose proof (word_toZ_range 5 x) as HX. change (0 <= @toZ (WordToZ 5) x < 4294967296) in HX.
  assert (HU : Int.unsigned (Int.repr (@toZ (WordToZ 3) amount)) = @toZ (WordToZ 3) amount).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
  assert (HR : Int64.unsigned (Int64.repr (@toZ (WordToZ 5) x)) = @toZ (WordToZ 5) x).
  { apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615; lia. }
  assert (HAC : Int.zero_ext 8 (Int.repr (@toZ (WordToZ 3) amount)) = Int.repr (@toZ (WordToZ 3) amount)).
  { apply byte_carrier_cast_id. rewrite HU; lia. }
  unfold shift_byte_machine_value, decode_wide. apply word_fromZ_bits. intros j Hj.
  change (0 <= j < 32) in Hj.
  change (Int64.testbit (Int64.zero_ext 32
    (shift_wide_payload W32 right false (Int64.repr (@toZ (WordToZ 5) x))
      (Int.repr (@toZ (WordToZ 3) amount)))) j =
    Z.testbit (@toZ (WordToZ 5) (@shift32_plain_spec right Alg.CoreFunSem (amount,x))) j).
  rewrite Int64.bits_zero_ext, (zlt_true _ j 32) by lia.
  unfold shift_wide_payload, shift_wide_maybe_fill. rewrite HAC.
  rewrite (@shift_wide_count_result_bits W32 right x) by assumption.
  rewrite HU. symmetry. apply shift32_plain_spec_bits; exact Hj.
Qed.
