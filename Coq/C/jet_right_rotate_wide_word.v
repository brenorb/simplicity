(** Bridge from the actual reversed-count helper result to literal canonical
    right rotation. Reuses the left-family scalar bit theorem. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_word_repr.
Require Import C.jet_rotate_wide_helper C.jet_rotate_count_exec.
Require Import C.jet_left_rotate_wide_exec C.jet_rotate_wide_word.
Require Import C.jet_right_rotate_wide_exec C.jet_right_rotate_wide_layout_machine.
Require Import C.jet_right_rotate_spec C.jet_right_rotate_word_controls.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma rotate_reverse_index width amount j :
  0 <= amount < width ->
  (j - ((width - amount) mod width)) mod width = (j + amount) mod width.
Proof.
  intros HA. destruct (Z.eq_dec amount 0) as [HZ|HZ].
  - subst amount. rewrite Z.sub_0_r, Z.mod_same, Z.sub_0_r, Z.add_0_r by lia. reflexivity.
  - rewrite (Z.mod_small (width - amount) width) by lia.
    replace (j - (width - amount)) with ((j + amount) + (-1) * width) by lia.
    rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma right_rotate_byte_machine_denotes s amount x :
  right_rotate_byte_machine_value s amount x =
    @right_rotate_byte_spec s Alg.CoreFunSem (amount,x).
Proof.
  pose proof (wide_bits_bounds (byte_rotate_width s)) as HW.
  pose proof (word_toZ_range 3 amount) as HA.
  assert (HU : Int.unsigned (Int.repr (@toZ (WordToZ 3) amount)) = @toZ (WordToZ 3) amount).
  { apply Int.unsigned_repr. change (0 <= @toZ (WordToZ 3) amount < 256) in HA.
    change Int.max_unsigned with 4294967295; lia. }
  assert (HR : Int64.unsigned (Int64.repr (@toZ (WordToZ (wide_log (byte_rotate_width s))) x)) =
      @toZ (WordToZ (wide_log (byte_rotate_width s))) x).
  { apply Int64.unsigned_repr. pose proof (word_toZ_range (wide_log (byte_rotate_width s)) x) as HX.
    rewrite <- wide_bits_pow in HX. destruct s; change Int64.max_unsigned with 18446744073709551615;
      change (0 <= @toZ (WordToZ (wide_log (byte_rotate_width R32))) x < 2 ^ 32) in HX ||
      change (0 <= @toZ (WordToZ (wide_log (byte_rotate_width R64))) x < 2 ^ 64) in HX; lia. }
  unfold right_rotate_byte_machine_value, decode_wide. apply word_fromZ_bits.
  intros j Hj. rewrite <- wide_bits_pow in Hj.
  change (Int64.testbit (Int64.zero_ext (wide_bits (byte_rotate_width s))
    (right_rotate_byte_payload s
      (Int64.repr (@toZ (WordToZ (wide_log (byte_rotate_width s))) x))
      (Int.repr (@toZ (WordToZ 3) amount)))) j =
    Z.testbit (@toZ (WordToZ (wide_log (byte_rotate_width s)))
      (@right_rotate_byte_spec s Alg.CoreFunSem (amount,x))) j).
  rewrite Int64.bits_zero_ext, zlt_true by lia.
  unfold right_rotate_byte_payload.
  rewrite (@wide_rotate_result_bits (byte_rotate_width s) x) by
    (try exact HR; try exact Hj; unfold wide_rotate_reverse_amount; apply wide_rotate_amount_bounds).
  rewrite wide_rotate_reverse_amount_unsigned by apply wide_rotate_amount_bounds.
  rewrite wide_rotate_amount_unsigned, HU.
  rewrite rotate_reverse_index by (apply Z.mod_pos_bound; lia).
  symmetry. apply right_rotate_byte_spec_bits; exact Hj.
Qed.
