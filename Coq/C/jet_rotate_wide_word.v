(** Bit bridge for the actual rotate scalar helper and canonical byte-control
    program. No execution contract or payload enumeration is assumed here. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Word.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_word_repr.
Require Import C.jet_rotate_wide_helper C.jet_rotate_count_exec.
Require Import C.jet_left_rotate_wide_exec C.jet_left_rotate_wide_layout_machine.
Require Import C.jet_rotate_spec C.jet_rotate_word_controls.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma wide_rotate_result_bits s (x : Ty.tySem (Word (wide_log s))) r a j :
  Int64.unsigned r = @toZ (WordToZ (wide_log s)) x ->
  0 <= Int.unsigned a < wide_bits s -> 0 <= j < wide_bits s ->
  Int64.testbit (wide_rotate_result s r a) j =
    Z.testbit (@toZ (WordToZ (wide_log s)) x)
      ((j - Int.unsigned a) mod wide_bits s).
Proof.
  intros Hr HA Hj. pose proof (wide_bits_bounds s) as HW.
  unfold wide_rotate_result. pose proof (Int.eq_spec a Int.zero) as HZ.
  destruct (Int.eq a Int.zero) eqn:HZb.
  - subst a. rewrite Int.unsigned_zero, Z.sub_0_r, Z.mod_small by exact Hj.
    unfold Int64.testbit. rewrite Hr. reflexivity.
  - assert (HP : 0 < Int.unsigned a).
    { assert (Int.unsigned a <> 0).
      { intro HE. apply HZ. rewrite <- (Int.repr_unsigned a), HE. reflexivity. }
      lia. }
    assert (HL : Int64.unsigned (Int64.repr (Int.unsigned a)) = Int.unsigned a).
    { apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615; lia. }
    assert (HR : Int64.unsigned (Int64.repr (wide_bits s - Int.unsigned a)) =
        wide_bits s - Int.unsigned a).
    { apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615; lia. }
    unfold wide_rotate_nonzero.
    rewrite Int64.bits_or, Int64.bits_shl, Int64.bits_shru by
      (change Int64.zwordsize with 64; lia).
    rewrite HL, HR. change Int64.zwordsize with 64.
    destruct (zlt j (Int.unsigned a)) as [Hlt|Hge].
    + rewrite zlt_true by lia. cbn [orb].
      assert (HM : (j - Int.unsigned a) mod wide_bits s = j + wide_bits s - Int.unsigned a).
      { symmetry. apply Z.mod_unique_pos with (q := -1); lia. }
      rewrite HM. unfold Int64.testbit. rewrite Hr. f_equal; lia.
    + assert (HB : Int64.testbit r (j + (wide_bits s - Int.unsigned a)) = false).
      { unfold Int64.testbit. rewrite Hr. apply word_toZ_high_bits.
        rewrite <- wide_bits_pow. lia. }
      destruct (zlt (j + (wide_bits s - Int.unsigned a)) 64);
        [rewrite HB|]; rewrite orb_false_r.
      all: rewrite Z.mod_small by lia; unfold Int64.testbit; rewrite Hr; reflexivity.
Qed.

Lemma left_rotate_byte_machine_denotes s amount x :
  left_rotate_byte_machine_value s amount x =
    @left_rotate_byte_spec s Alg.CoreFunSem (amount,x).
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
  unfold left_rotate_byte_machine_value, decode_wide. apply word_fromZ_bits.
  intros j Hj. rewrite <- wide_bits_pow in Hj.
  change (Int64.testbit (Int64.zero_ext (wide_bits (byte_rotate_width s))
    (left_rotate_byte_payload s
      (Int64.repr (@toZ (WordToZ (wide_log (byte_rotate_width s))) x))
      (Int.repr (@toZ (WordToZ 3) amount)))) j =
    Z.testbit (@toZ (WordToZ (wide_log (byte_rotate_width s)))
      (@left_rotate_byte_spec s Alg.CoreFunSem (amount,x))) j).
  rewrite Int64.bits_zero_ext, zlt_true by lia.
  unfold left_rotate_byte_payload.
  rewrite (@wide_rotate_result_bits (byte_rotate_width s) x) by
    (try exact HR; try exact Hj; apply wide_rotate_amount_bounds).
  rewrite wide_rotate_amount_unsigned, HU. symmetry. apply left_rotate_byte_spec_bits; exact Hj.
Qed.
