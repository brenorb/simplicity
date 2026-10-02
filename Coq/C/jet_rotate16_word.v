(** Actual rotate_16 helper result denotes the canonical variable program. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr.
Require Import C.jet_rotate_wide_helper C.jet_rotate_count_exec C.jet_rotate_wide_word C.jet_right_rotate_wide_word.
Require Import C.jet_rotate16_exec C.jet_rotate16_layout_machine C.jet_rotate16_spec C.jet_rotate_control_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma rotate16_machine_denotes right amount x :
  rotate16_machine_value right amount x = @rotate16_spec right Alg.CoreFunSem (amount,x).
Proof.
  pose proof (word_toZ_range 2 amount) as HA. change (0 <= @toZ (WordToZ 2) amount < 16) in HA.
  pose proof (word_toZ_range 4 x) as HX. change (0 <= @toZ (WordToZ 4) x < 65536) in HX.
  assert (HU : Int.unsigned (Int.repr (@toZ (WordToZ 2) amount)) = @toZ (WordToZ 2) amount).
  { apply Int.unsigned_repr. change Int.max_unsigned with 4294967295; lia. }
  assert (HR : Int64.unsigned (Int64.repr (@toZ (WordToZ 4) x)) = @toZ (WordToZ 4) x).
  { apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615; lia. }
  unfold rotate16_machine_value, decode_wide. apply word_fromZ_bits. intros j Hj.
  change (0 <= j < 16) in Hj.
  change (Int64.testbit (Int64.zero_ext 16
    (rotate16_payload right (Int64.repr (@toZ (WordToZ 4) x))
      (Int.repr (@toZ (WordToZ 2) amount)))) j =
    Z.testbit (@toZ (WordToZ 4) (@rotate16_spec right Alg.CoreFunSem (amount,x))) j).
  rewrite Int64.bits_zero_ext, zlt_true by lia.
  rewrite rotate16_spec_bits by exact Hj. unfold rotate16_payload, rotate16_scalar_value.
  destruct right.
  - rewrite (@wide_rotate_result_bits W16 x) by
      (try exact HR; try exact Hj; unfold wide_rotate_reverse_amount; apply wide_rotate_amount_bounds).
    rewrite wide_rotate_reverse_amount_unsigned by apply wide_rotate_amount_bounds.
    rewrite wide_rotate_amount_unsigned, HU.
    change (Z.testbit (@toZ (WordToZ 4) x) ((j - ((16 - @toZ (WordToZ 2) amount mod 16) mod 16)) mod 16) =
      Z.testbit (@toZ (WordToZ 4) x) ((j - -(@toZ (WordToZ 2) amount mod 16)) mod 16)).
    rewrite rotate_reverse_index by (apply Z.mod_pos_bound; lia).
    f_equal. f_equal. lia.
  - rewrite (@wide_rotate_result_bits W16 x) by
      (try exact HR; try exact Hj; apply wide_rotate_amount_bounds).
    rewrite wide_rotate_amount_unsigned, HU. reflexivity.
Qed.
