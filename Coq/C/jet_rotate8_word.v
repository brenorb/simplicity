(** Actual byte rotation result denotes the literal canonical program.
    The payload is symbolic; only bounded count arithmetic is normalized. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_spec C.jet_word_repr C.jet_rotate_count_exec.
Require Import C.jet_rotate8_helper C.jet_rotate8_count C.jet_rotate8_bits.
Require Import C.jet_rotate8_exec C.jet_rotate8_layout_machine C.jet_rotate8_spec.
Require Import C.jet_rotate_control_word C.jet_right_rotate_wide_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma rotate8_machine_denotes right amount x :
  rotate8_machine_value right amount x = @rotate8_spec right Alg.CoreFunSem (amount,x).
Proof.
  pose proof (word_toZ_range 2 amount) as HA. change (0 <= @toZ (WordToZ 2) amount < 16) in HA.
  pose proof (word_toZ_range 3 x) as HX. change (0 <= @toZ (WordToZ 3) x < 256) in HX.
  assert (HU : Int.unsigned (Int.repr (@toZ (WordToZ 2) amount)) = @toZ (WordToZ 2) amount).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
  assert (HR : Int.unsigned (Int.repr (@toZ (WordToZ 3) x)) = @toZ (WordToZ 3) x).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
  unfold rotate8_machine_value, decode_word8.
  rewrite Int64.unsigned_repr by
    (pose proof (Int.unsigned_range_2
      (rotate8_payload right (Int.repr (@toZ (WordToZ 3) x))
        (Int.repr (@toZ (WordToZ 2) amount))));
     change Int.max_unsigned with 4294967295 in *;
     change Int64.max_unsigned with 18446744073709551615; lia).
  apply (proj2 (word_fromZ_bits 3 (@rotate8_spec right Alg.CoreFunSem (amount,x)) _)).
  intros j Hj. change (0 <= j < 8) in Hj.
  change (Int.testbit (rotate8_payload right (Int.repr (@toZ (WordToZ 3) x))
    (Int.repr (@toZ (WordToZ 2) amount))) j =
    Z.testbit (@toZ (WordToZ 3) (@rotate8_spec right Alg.CoreFunSem (amount,x))) j).
  unfold rotate8_payload. rewrite Int.bits_zero_ext, (zlt_true _ j 8) by lia.
  rewrite rotate8_spec_bits by exact Hj. unfold rotate8_raw, rotate8_scalar_value.
  rewrite byte_carrier_cast_id by (rewrite HR; exact HX).
  destruct right.
  - rewrite (@rotate8_result_bits x) by
      (try exact HR; try exact Hj; unfold rotate8_reverse_amount; apply rotate8_amount_bounds).
    rewrite rotate8_reverse_amount_unsigned by apply rotate8_amount_bounds.
    rewrite rotate8_amount_unsigned, HU.
    change (Z.testbit (@toZ (WordToZ 3) x) ((j - ((8 - @toZ (WordToZ 2) amount mod 8) mod 8)) mod 8) =
      Z.testbit (@toZ (WordToZ 3) x) ((j - -(@toZ (WordToZ 2) amount mod 8)) mod 8)).
    rewrite rotate_reverse_index by (apply Z.mod_pos_bound; lia).
    f_equal. f_equal. lia.
  - rewrite (@rotate8_result_bits x) by
      (try exact HR; try exact Hj; apply rotate8_amount_bounds).
    rewrite rotate8_amount_unsigned, HU. reflexivity.
Qed.
