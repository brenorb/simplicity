(** CompCert carrier observations for the actual secp256k1_umul128 steps.
    Products/mid/high sums are exact; the low return is intentionally modular.
    These results support C helper execution, not public jet coverage. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import C.jet_divmod96_value C.jet_umul128_arith.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition umul128_low w := Int64.repr (Int.unsigned (Int64.loword w)).
Definition umul128_ll a b := Int64.mul (umul128_low a) (umul128_low b).
Definition umul128_lh a b := Int64.mul (umul128_low a) (divmod96_high b).
Definition umul128_hl a b := Int64.mul (divmod96_high a) (umul128_low b).
Definition umul128_hh a b := Int64.mul (divmod96_high a) (divmod96_high b).
Definition umul128_mid ll lh hl :=
  Int64.add (Int64.add (divmod96_high ll) (umul128_low lh)) (umul128_low hl).
Definition umul128_hi hh lh hl mid :=
  Int64.add (Int64.add (Int64.add hh (divmod96_high lh)) (divmod96_high hl)) (divmod96_high mid).
Definition umul128_lo ll mid := Int64.add (Int64.shl mid (Int64.repr 32)) (umul128_low ll).

Lemma umul128_low_unsigned w : Int64.unsigned (umul128_low w) = Int64.unsigned w mod divmod96_radix.
Proof.
  unfold umul128_low. rewrite Int64.unsigned_repr.
  - unfold Int64.loword. rewrite Int.unsigned_repr_eq. reflexivity.
  - pose proof (Int.unsigned_range (Int64.loword w)). change Int.modulus with 4294967296 in *.
    change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma umul128_mul_unsigned x y : Int64.unsigned x * Int64.unsigned y < Int64.modulus ->
  Int64.unsigned (Int64.mul x y) = Int64.unsigned x * Int64.unsigned y.
Proof.
  intros H. unfold Int64.mul. apply Int64.unsigned_repr.
  pose proof (Int64.unsigned_range x). pose proof (Int64.unsigned_range y).
  unfold Int64.max_unsigned. nia.
Qed.
Lemma umul128_add_unsigned x y : Int64.unsigned x + Int64.unsigned y < Int64.modulus ->
  Int64.unsigned (Int64.add x y) = Int64.unsigned x + Int64.unsigned y.
Proof.
  intros H. unfold Int64.add. apply Int64.unsigned_repr.
  pose proof (Int64.unsigned_range x). pose proof (Int64.unsigned_range y).
  unfold Int64.max_unsigned. lia.
Qed.
Lemma umul128_sum3_unsigned x y z : Int64.unsigned x + Int64.unsigned y + Int64.unsigned z < Int64.modulus ->
  Int64.unsigned (Int64.add (Int64.add x y) z) = Int64.unsigned x + Int64.unsigned y + Int64.unsigned z.
Proof.
  intros H. pose proof (Int64.unsigned_range z).
  pose proof (umul128_add_unsigned x y ltac:(lia)) as Hxy.
  rewrite umul128_add_unsigned; [rewrite Hxy; reflexivity|rewrite Hxy; exact H].
Qed.
Lemma umul128_sum4_unsigned x y z w :
  Int64.unsigned x + Int64.unsigned y + Int64.unsigned z + Int64.unsigned w < Int64.modulus ->
  Int64.unsigned (Int64.add (Int64.add (Int64.add x y) z) w) =
    Int64.unsigned x + Int64.unsigned y + Int64.unsigned z + Int64.unsigned w.
Proof.
  intros H. pose proof (Int64.unsigned_range w).
  pose proof (umul128_sum3_unsigned x y z ltac:(lia)) as Hxyz.
  rewrite umul128_add_unsigned; [rewrite Hxyz; reflexivity|rewrite Hxyz; exact H].
Qed.

Lemma umul128_lo_modular ll mid : umul128_lo ll mid =
  Int64.repr (Int64.unsigned mid * divmod96_radix + Int64.unsigned (umul128_low ll)).
Proof.
  unfold umul128_lo. rewrite Int64.shl_mul_two_p.
  change (Int64.repr (two_p (Int64.unsigned (Int64.repr 32)))) with (Int64.repr divmod96_radix).
  unfold Int64.add, Int64.mul. apply Int64.eqm_samerepr. apply Int64.eqm_add.
  - apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_mult.
    + apply Int64.eqm_refl.
    + apply Int64.eqm_unsigned_repr_l. apply Int64.eqm_refl.
  - apply Int64.eqm_refl.
Qed.

Theorem umul128_machine_observation a b :
  let ll := umul128_ll a b in let lh := umul128_lh a b in
  let hl := umul128_hl a b in let hh := umul128_hh a b in
  let mid := umul128_mid ll lh hl in
  Int64.unsigned (umul128_hi hh lh hl mid) = (Int64.unsigned a * Int64.unsigned b) / Int64.modulus /\
  Int64.unsigned (umul128_lo ll mid) = (Int64.unsigned a * Int64.unsigned b) mod Int64.modulus.
Proof.
  intros ll lh hl hh mid.
  set (LL := (Int64.unsigned a mod divmod96_radix) * (Int64.unsigned b mod divmod96_radix)).
  set (LH := (Int64.unsigned a mod divmod96_radix) * (Int64.unsigned b / divmod96_radix)).
  set (HL := (Int64.unsigned a / divmod96_radix) * (Int64.unsigned b mod divmod96_radix)).
  set (HH := (Int64.unsigned a / divmod96_radix) * (Int64.unsigned b / divmod96_radix)).
  set (MID := LL / divmod96_radix + LH mod divmod96_radix + HL mod divmod96_radix).
  set (HI := HH + LH / divmod96_radix + HL / divmod96_radix + MID / divmod96_radix).
  set (LO := (MID mod divmod96_radix) * divmod96_radix + LL mod divmod96_radix).
  pose proof (umul128_limb_algorithm divmod96_radix (Int64.unsigned a) (Int64.unsigned b)
    ltac:(unfold divmod96_radix; lia) (Int64.unsigned_range a) (Int64.unsigned_range b)) as Halg.
  change (0 <= LL < Int64.modulus /\ 0 <= LH < Int64.modulus /\ 0 <= HL < Int64.modulus /\
    0 <= HH < Int64.modulus /\ 0 <= MID < 3 * divmod96_radix /\ 0 <= HI < Int64.modulus /\
    0 <= LO < Int64.modulus /\ Int64.unsigned a * Int64.unsigned b = HI * Int64.modulus + LO /\
    HI = (Int64.unsigned a * Int64.unsigned b) / Int64.modulus /\
    LO = (Int64.unsigned a * Int64.unsigned b) mod Int64.modulus) in Halg.
  destruct Halg as (RLL & RLH & RHL & RHH & RMID & RHI & RLO & Hbalance & Hhi & Hlo).
  assert (HLL : Int64.unsigned ll = LL).
  { unfold ll, umul128_ll. rewrite umul128_mul_unsigned;
      rewrite !umul128_low_unsigned; [reflexivity|exact (proj2 RLL)]. }
  assert (HLH : Int64.unsigned lh = LH).
  { unfold lh, umul128_lh. rewrite umul128_mul_unsigned;
      rewrite umul128_low_unsigned, divmod96_high_unsigned; [reflexivity|exact (proj2 RLH)]. }
  assert (HHL : Int64.unsigned hl = HL).
  { unfold hl, umul128_hl. rewrite umul128_mul_unsigned;
      rewrite umul128_low_unsigned, divmod96_high_unsigned; [reflexivity|exact (proj2 RHL)]. }
  assert (HHH : Int64.unsigned hh = HH).
  { unfold hh, umul128_hh. rewrite umul128_mul_unsigned;
      rewrite !divmod96_high_unsigned; [reflexivity|exact (proj2 RHH)]. }
  assert (HMID : Int64.unsigned mid = MID).
  { unfold mid, umul128_mid. rewrite umul128_sum3_unsigned;
      rewrite divmod96_high_unsigned, !umul128_low_unsigned, HLL, HLH, HHL.
    - reflexivity.
    - change (MID < Int64.modulus). change (3 * divmod96_radix) with 12884901888 in RMID.
      change Int64.modulus with 18446744073709551616. lia. }
  split.
  - unfold umul128_hi. rewrite umul128_sum4_unsigned;
      rewrite !divmod96_high_unsigned, HHH, HLH, HHL, HMID.
    + exact Hhi.
    + exact (proj2 RHI).
  - rewrite umul128_lo_modular, Int64.unsigned_repr_eq, HMID, umul128_low_unsigned, HLL, <- Hlo.
    symmetry. apply Z.mod_unique with (MID / divmod96_radix); [left; exact RLO|].
    pose proof (Z.div_mod MID divmod96_radix ltac:(unfold divmod96_radix; lia)) as HM.
    change Int64.modulus with (divmod96_radix * divmod96_radix). unfold LO. nia.
Qed.
