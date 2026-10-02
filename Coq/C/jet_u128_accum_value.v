(** Machine values of the actual uint128 += uint64 helper. The low-word
    comparison observes the wrapped sum; the full sum must fit 128 bits. *)
From Coq Require Import ZArith Lia Bool.
From compcert Require Import Coqlib Integers.
Require Import C.jet_readBit_layout C.jet_umul128_value.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition u128_accum_lo lo a := Int64.add lo a.
Definition u128_accum_carry lo a := Int64.ltu (u128_accum_lo lo a) a.
Definition u128_accum_hi hi lo a := Int64.add hi (bit_long (u128_accum_carry lo a)).

Lemma u128_accum_low_balance lo a :
  Int64.unsigned (u128_accum_lo lo a) +
    Int64.unsigned (bit_long (u128_accum_carry lo a)) * Int64.modulus =
  Int64.unsigned lo + Int64.unsigned a.
Proof.
  pose proof (Int64.unsigned_range lo) as HL.
  pose proof (Int64.unsigned_range a) as HA.
  pose proof (Int64.unsigned_range (Int64.add lo a)) as HS.
  destruct (Int64.unsigned_add_either lo a) as [Hsum|Hsum].
  - assert (HC : u128_accum_carry lo a = Datatypes.false).
    { unfold u128_accum_carry, u128_accum_lo, Int64.ltu.
      rewrite Hsum, zlt_false by lia. reflexivity. }
    unfold u128_accum_lo. rewrite HC, Hsum.
    change (Int64.unsigned lo + Int64.unsigned a + 0 * Int64.modulus =
      Int64.unsigned lo + Int64.unsigned a). lia.
  - assert (HC : u128_accum_carry lo a = Datatypes.true).
    { unfold u128_accum_carry, u128_accum_lo, Int64.ltu.
      rewrite Hsum, zlt_true by lia. reflexivity. }
    unfold u128_accum_lo. rewrite HC, Hsum.
    change (Int64.unsigned lo + Int64.unsigned a - Int64.modulus + 1 * Int64.modulus =
      Int64.unsigned lo + Int64.unsigned a). lia.
Qed.

Theorem u128_accum_machine_observation hi lo a :
  Int64.unsigned hi * Int64.modulus + Int64.unsigned lo + Int64.unsigned a <
    Int64.modulus * Int64.modulus ->
  Int64.unsigned (u128_accum_hi hi lo a) * Int64.modulus +
    Int64.unsigned (u128_accum_lo lo a) =
    Int64.unsigned hi * Int64.modulus + Int64.unsigned lo + Int64.unsigned a.
Proof.
  intros Hfit. pose proof (u128_accum_low_balance lo a) as HB.
  pose proof (Int64.unsigned_range hi) as HH.
  pose proof (Int64.unsigned_range (u128_accum_lo lo a)) as HL.
  pose proof (Int64.unsigned_range (bit_long (u128_accum_carry lo a))) as HC.
  assert (HM : 0 < Int64.modulus) by (vm_compute; reflexivity).
  assert (Hhigh : 0 <= Int64.unsigned hi + Int64.unsigned (bit_long (u128_accum_carry lo a)) < Int64.modulus).
  { split; [lia|]. nia. }
  unfold u128_accum_hi. rewrite umul128_add_unsigned by exact (proj2 Hhigh). nia.
Qed.
