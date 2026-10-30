(** The even affine ordinate is unique at a fixed X. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group
 C.jet_secp_affine_word_valid C.jet_secp_field_word_group C.jet_secp_curve_literal
 C.jet_secp_curve_nonzero C.jet_secp_canonical_normalize C.jet_secp_canonical_odd
 C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_is_odd literal_fe_negate secp_field_word.
Lemma secp_field_negate_odd (y:Ty.tySem (Word 8)):
 0<@toZ (WordToZ 8) y<feP ->
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem (@literal_fe_negate Alg.CoreFunSem y))=
 negb (Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)).
Proof.
 intro Range;rewrite !canonical_fe_is_odd_numeric,!canonical_fe_normalize_numeric,
 canonical_field_order_matches_limb_model,literal_curve_negate_numeric.
 rewrite Z.mod_mod,Z.mod_small,Z.mod_small by lia.
 rewrite !Z.bit0_odd,Z.odd_sub.
 assert (Odd:Z.odd feP=Datatypes.true) by (vm_compute;reflexivity).
 rewrite Odd;destruct (Z.odd (@toZ (WordToZ 8) y));reflexivity.
Qed.
Lemma secp_normalize_bounded_word (y:Ty.tySem (Word 8)):
 0<=@toZ (WordToZ 8) y<feP ->@canonical_fe_normalize Alg.CoreFunSem y=y.
Proof.
 intro Range;apply (toZ_injective (WordToZ 8)).
 rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model;apply Z.mod_small;exact Range.
Qed.
Theorem secp_even_y_unique (x y v:Ty.tySem (Word 8)):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,y))=Datatypes.true ->
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (x,v))=Datatypes.true ->
 0<=@toZ (WordToZ 8) y<feP ->0<=@toZ (WordToZ 8) v<feP ->
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem y)=Datatypes.false ->
 Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem v)=Datatypes.false ->y=v.
Proof.
 intros CurveY CurveV RangeY RangeV EvenY EvenV.
 pose proof (secp_affine_curve_of_literal x y CurveY) as FieldY.
 pose proof (secp_affine_curve_of_literal x v CurveV) as FieldV.
 assert (Square:SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_field_word y) 2=
  SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_field_word v) 2) by congruence.
 destruct (SMain.Ksqr_eq secp_group_theory _ _ Square) as [Same|Opposite].
 - pose proof (secp_field_word_equal_normalized y v Same) as Equal.
   rewrite !secp_normalize_bounded_word in Equal by assumption;exact Equal.
 - assert (Nonzero:@toZ (WordToZ 8) v<>0).
   { rewrite literal_ge_curve_numeric in CurveV;apply Z.eqb_eq in CurveV.
     pose proof (secp_curve_y_nonzero (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) v) (eq_sym CurveV)) as NZ.
     intro Zero;apply NZ;rewrite Zero;reflexivity. }
   assert (NegRange:0<=@toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem v)<feP).
   { rewrite literal_curve_negate_numeric;apply Z.mod_pos_bound;pose proof secp_group_field_positive;lia. }
   assert (Same:secp_field_word y=secp_field_word (@literal_fe_negate Alg.CoreFunSem v)).
   { rewrite secp_field_word_negate;exact Opposite. }
   pose proof (secp_field_word_equal_normalized y _ Same) as Equal.
   rewrite !secp_normalize_bounded_word in Equal by assumption.
   pose proof (secp_field_negate_odd v ltac:(clear -RangeV Nonzero;lia)) as Parity.
   pose proof (eq_trans (eq_sym (f_equal
    (fun word:Ty.tySem (Word 8)=>Bit.toBool (@canonical_fe_is_odd Alg.CoreFunSem word)) Equal)) EvenY) as NegEven.
   pose proof (eq_trans (eq_sym NegEven) (eq_trans Parity (f_equal negb EvenV))) as Impossible.
   discriminate Impossible.
Qed.
