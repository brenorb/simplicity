(** Connect the checked actual uint128 helper values to literal
    Programs.Arith.multiply word64. This is a bridge, not jet coverage. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Word.
Require Import C.jet_multiply_spec C.jet_toZ C.jet_umul128_value C.jet_umul128_layout.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma multiply64_product_representation (x y : Ty.tySem (Word 6)) a b :
  Int64.unsigned a = @toZ (WordToZ 6) x -> Int64.unsigned b = @toZ (WordToZ 6) y ->
  (@fromZ (WordToZ 6) (Int64.unsigned (umul128_result_hi a b)),
   @fromZ (WordToZ 6) (Int64.unsigned (umul128_result_lo a b))) =
    @multiply_word_spec 6 Alg.CoreFunSem (x,y).
Proof.
  intros HA HB. apply (toZ_injective (WordToZ 7)). rewrite multiply_word_spec_numeric.
  change (@toZ (WordToZ 6) (@fromZ (WordToZ 6) (Int64.unsigned (umul128_result_hi a b))) * Int64.modulus +
    @toZ (WordToZ 6) (@fromZ (WordToZ 6) (Int64.unsigned (umul128_result_lo a b))) =
    @toZ (WordToZ 6) x * @toZ (WordToZ 6) y).
  rewrite !to_fromZ.
  change ((Int64.unsigned (umul128_result_hi a b) mod Int64.modulus) * Int64.modulus +
    (Int64.unsigned (umul128_result_lo a b) mod Int64.modulus) = @toZ (WordToZ 6) x * @toZ (WordToZ 6) y).
  rewrite !Z.mod_small by apply Int64.unsigned_range.
  destruct (umul128_machine_observation a b) as [HH HL].
  change (Int64.unsigned (umul128_result_hi a b) = (Int64.unsigned a * Int64.unsigned b) / Int64.modulus) in HH.
  change (Int64.unsigned (umul128_result_lo a b) = (Int64.unsigned a * Int64.unsigned b) mod Int64.modulus) in HL.
  rewrite HH, HL, <- HA, <- HB.
  pose proof (Z.div_mod (Int64.unsigned a * Int64.unsigned b) Int64.modulus ltac:(discriminate)). nia.
Qed.
