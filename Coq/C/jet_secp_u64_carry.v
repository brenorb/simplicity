(** Exact wrapped uint64 addition and carry; no no-overflow restriction. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma u64_add_with_carry x y :
  Int64.unsigned (Int64.add x y) =
    (Int64.unsigned x + Int64.unsigned y) mod Int64.modulus /\
  Z.b2z (Int64.ltu (Int64.add x y) x) =
    (Int64.unsigned x + Int64.unsigned y) / Int64.modulus.
Proof.
  rewrite Int64.add_unsigned, Int64.unsigned_repr_eq.
  split; [reflexivity|].
  pose proof (Int64.unsigned_range x) as HX.
  pose proof (Int64.unsigned_range y) as HY.
  unfold Int64.ltu; rewrite Int64.unsigned_repr_eq.
  destruct (Z_lt_ge_dec (Int64.unsigned x + Int64.unsigned y) Int64.modulus) as [HL|HH].
  - rewrite Z.mod_small, Z.div_small by lia.
    destruct (zlt (Int64.unsigned x + Int64.unsigned y) (Int64.unsigned x)); cbn; lia.
  - assert (HM : (Int64.unsigned x + Int64.unsigned y) mod Int64.modulus =
        Int64.unsigned x + Int64.unsigned y - Int64.modulus).
    { replace (Int64.unsigned x + Int64.unsigned y) with
        ((Int64.unsigned x + Int64.unsigned y - Int64.modulus) + 1 * Int64.modulus) at 1 by ring.
      rewrite Z.mod_add by lia; apply Z.mod_small; lia. }
    assert (HD : (Int64.unsigned x + Int64.unsigned y) / Int64.modulus = 1).
    { symmetry; apply Z.div_unique with (r := Int64.unsigned x + Int64.unsigned y - Int64.modulus);
        [left; lia|lia]. }
    rewrite HM, HD.
    destruct (zlt (Int64.unsigned x + Int64.unsigned y - Int64.modulus) (Int64.unsigned x)); cbn; lia.
Qed.
Lemma u64_add_carry_bit x y :
  Int64.unsigned (Int64.repr (Int.signed
    (if Int64.ltu (Int64.add x y) x then Int.one else Int.zero))) =
  (Int64.unsigned x + Int64.unsigned y) / Int64.modulus.
Proof.
  rewrite <- (proj2 (u64_add_with_carry x y)).
  destruct (Int64.ltu (Int64.add x y) x); reflexivity.
Qed.
Lemma u64_add_carry_bit_right x y :
  Int64.unsigned (Int64.repr (Int.signed
    (if Int64.ltu (Int64.add x y) y then Int.one else Int.zero))) =
  (Int64.unsigned x + Int64.unsigned y) / Int64.modulus.
Proof.
  rewrite (Int64.add_commut x y), (Z.add_comm (Int64.unsigned x) (Int64.unsigned y)).
  apply u64_add_carry_bit.
Qed.
