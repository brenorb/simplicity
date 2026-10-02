(** Canonical full_multiply word64 bridge for the actual multiplication and
    two uint128 accumulation values. The canonical output range supplies both
    no-overflow bounds; this bridge alone is not public jet coverage. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word.
Require Import C.jet_toZ C.jet_word_repr C.jet_umul128_value C.jet_umul128_layout C.jet_u128_accum_value.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_multiply64_lo a b u v := u128_accum_lo (u128_accum_lo (umul128_result_lo a b) u) v.
Definition full_multiply64_hi a b u v :=
  u128_accum_hi (u128_accum_hi (umul128_result_hi a b) (umul128_result_lo a b) u)
    (u128_accum_lo (umul128_result_lo a b) u) v.

Lemma full_multiply64_machine_observation a b u v :
  Int64.unsigned a * Int64.unsigned b + Int64.unsigned u + Int64.unsigned v <
    Int64.modulus * Int64.modulus ->
  Int64.unsigned (full_multiply64_hi a b u v) * Int64.modulus +
    Int64.unsigned (full_multiply64_lo a b u v) =
    Int64.unsigned a * Int64.unsigned b + Int64.unsigned u + Int64.unsigned v.
Proof.
  intros Hfit. pose proof (Int64.unsigned_range v) as HV.
  assert (Hprod : Int64.unsigned (umul128_result_hi a b) * Int64.modulus +
    Int64.unsigned (umul128_result_lo a b) = Int64.unsigned a * Int64.unsigned b).
  { destruct (umul128_machine_observation a b) as [HH HL].
    change (Int64.unsigned (umul128_result_hi a b) = (Int64.unsigned a * Int64.unsigned b) / Int64.modulus) in HH.
    change (Int64.unsigned (umul128_result_lo a b) = (Int64.unsigned a * Int64.unsigned b) mod Int64.modulus) in HL.
    rewrite HH, HL. pose proof (Z.div_mod (Int64.unsigned a * Int64.unsigned b) Int64.modulus ltac:(discriminate)). nia. }
  pose proof (u128_accum_machine_observation (umul128_result_hi a b) (umul128_result_lo a b) u
    ltac:(rewrite Hprod; lia)) as Hfirst.
  unfold full_multiply64_hi, full_multiply64_lo.
  rewrite u128_accum_machine_observation by (rewrite Hfirst, Hprod; exact Hfit).
  rewrite Hfirst, Hprod. reflexivity.
Qed.

Lemma full_multiply64_representation (x y z w : Ty.tySem (Word 6)) a b u v :
  Int64.unsigned a = @toZ (WordToZ 6) x -> Int64.unsigned b = @toZ (WordToZ 6) y ->
  Int64.unsigned u = @toZ (WordToZ 6) z -> Int64.unsigned v = @toZ (WordToZ 6) w ->
  (@fromZ (WordToZ 6) (Int64.unsigned (full_multiply64_hi a b u v)),
   @fromZ (WordToZ 6) (Int64.unsigned (full_multiply64_lo a b u v))) =
    @fullMultiplier 6 Alg.CoreFunSem ((x,y),(z,w)).
Proof.
  intros HA HB HU HV.
  pose proof (word_toZ_range 7 (@fullMultiplier 6 Alg.CoreFunSem ((x,y),(z,w)))) as Hrange.
  rewrite fullMultiplier_correct in Hrange.
  change (0 <= @toZ (WordToZ 6) x * @toZ (WordToZ 6) y + @toZ (WordToZ 6) z +
    @toZ (WordToZ 6) w < Int64.modulus * Int64.modulus) in Hrange.
  apply (toZ_injective (WordToZ 7)). rewrite fullMultiplier_correct.
  change (@toZ (WordToZ 6) (@fromZ (WordToZ 6) (Int64.unsigned (full_multiply64_hi a b u v))) * Int64.modulus +
    @toZ (WordToZ 6) (@fromZ (WordToZ 6) (Int64.unsigned (full_multiply64_lo a b u v))) =
    @toZ (WordToZ 6) x * @toZ (WordToZ 6) y + @toZ (WordToZ 6) z + @toZ (WordToZ 6) w).
  rewrite !to_fromZ.
  change ((Int64.unsigned (full_multiply64_hi a b u v) mod Int64.modulus) * Int64.modulus +
    (Int64.unsigned (full_multiply64_lo a b u v) mod Int64.modulus) =
    @toZ (WordToZ 6) x * @toZ (WordToZ 6) y + @toZ (WordToZ 6) z + @toZ (WordToZ 6) w).
  rewrite !Z.mod_small by apply Int64.unsigned_range.
  rewrite <- HA, <- HB, <- HU, <- HV in *. apply full_multiply64_machine_observation; lia.
Qed.
