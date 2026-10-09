(** Literal fe_is_odd = fe_normalize >>> lsb256, with its limb bridge.
    The public jet lifecycle is proved in jet_secp_odd_lifecycle. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_word_bit_spec C.jet_secp_fe_math.
Require Import C.jet_secp_canonical_normalize.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize.

Definition canonical_fe_is_odd {term : Alg.Core.Algebra} : term (Word 8) Bit :=
  @canonical_fe_normalize term >>> @Word.rightmost Bit 8 term.
Lemma canonical_fe_is_odd_numeric (value : Ty.tySem (Word 8)) :
  Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem value) =
    Z.testbit (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)) 0.
Proof.
  change (Bit.toBool (@word_bit_spec 8 0 Alg.CoreFunSem
    (@canonical_fe_normalize Alg.CoreFunSem value)) =
    Z.testbit (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)) 0).
  apply word_bit_spec_numeric; cbn; lia.
Qed.

Lemma field_low_limb_odd_value value :
  Int64.unsigned (Int64.and (Int64.repr (value mod 2 ^ 52)) Int64.one) =
    Z.b2z (Z.testbit value 0).
Proof.
  pose proof (Z.mod_pos_bound value (2 ^ 52) ltac:(lia)) as HLimbs.
  unfold Int64.and.
  rewrite (Int64.unsigned_repr (value mod 2 ^ 52)) by
    (change Int64.max_unsigned with 18446744073709551615; lia).
  change (Int64.unsigned (Int64.repr (Z.land (value mod 2 ^ 52) 1)) = Z.b2z (Z.testbit value 0)).
  replace 1 with (2 ^ 1 - 1) at 1 by reflexivity.
  rewrite land_ones_mod by lia.
  rewrite Int64.unsigned_repr by
    (pose proof (Z.mod_pos_bound (value mod 2 ^ 52) (2 ^ 1) ltac:(lia));
     change Int64.max_unsigned with 18446744073709551615; lia).
  change ((value mod 2 ^ 52) mod 2 = Z.b2z (Z.testbit value 0)).
  rewrite <- Z.bit0_mod, Z.mod_pow2_bits_low by lia; reflexivity.
Qed.
