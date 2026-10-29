(** Interpret the existing literal word operations in the already verified
    prime field. These are bridges for the original terms, not new targets. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_toZ
 C.jet_predicate_spec C.jet_secp_literal_add_numeric C.jet_secp_literal_add_program C.jet_secp_double_literal
 C.jet_secp_double_half_literal_numeric C.jet_secp_canonical_normalize C.jet_secp_canonical_zero
 C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_curve_literal
 C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_field_word_group_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Definition secp_field_integer (z:Z):secp_group_field:=GZnZ.mkznz feP (z mod feP) (GZnZ.modz feP z).
Definition secp_field_word (w:Ty.tySem (Word 8)):=secp_field_integer (@toZ (WordToZ 8) w).
Lemma secp_field_integer_mod z:secp_field_integer (z mod feP)=secp_field_integer z.
Proof. apply GZnZ.zirr;apply Z.mod_mod;pose proof secp_group_field_positive;lia. Qed.
Lemma secp_field_integer_add x y:secp_field_integer (x+y)=GZnZ.add feP (secp_field_integer x) (secp_field_integer y).
Proof. apply GZnZ.zirr;apply Z.add_mod;pose proof secp_group_field_positive;lia. Qed.
Lemma secp_field_integer_mul x y:secp_field_integer (x*y)=GZnZ.mul feP (secp_field_integer x) (secp_field_integer y).
Proof. apply GZnZ.zirr;apply Z.mul_mod;pose proof secp_group_field_positive;lia. Qed.
Lemma secp_field_integer_opp x:secp_field_integer (-x)=GZnZ.opp feP (secp_field_integer x).
Proof.
 apply GZnZ.zirr.
 change ((-x) mod feP=(- (x mod feP)) mod feP).
 replace (-x) with ((-1)*x) by ring.
 replace (- (x mod feP)) with ((-1)*(x mod feP)) by ring.
 symmetry;apply Z.mul_mod_idemp_r;pose proof secp_group_field_positive;lia.
Qed.
Lemma secp_field_integer_p:secp_field_integer feP=GZnZ.zero feP.
Proof. apply GZnZ.zirr;vm_compute;reflexivity. Qed.
Local Opaque secp_field_integer.
Lemma secp_field_word_normalize w:secp_field_word (@canonical_fe_normalize Alg.CoreFunSem w)=secp_field_word w.
Proof.
 unfold secp_field_word;rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
 apply secp_field_integer_mod.
Qed.
Lemma secp_field_word_add x y:secp_field_word (@literal_fe_add Alg.CoreFunSem (x,y))=
 GZnZ.add feP (secp_field_word x) (secp_field_word y).
Proof.
 unfold secp_field_word;rewrite literal_fe_add_numeric,canonical_field_order_matches_limb_model,secp_field_integer_mod.
 apply secp_field_integer_add.
Qed.
Lemma secp_field_word_mul x y:secp_field_word (@literal_fe_multiply Alg.CoreFunSem (x,y))=
 GZnZ.mul feP (secp_field_word x) (secp_field_word y).
Proof.
 unfold secp_field_word;rewrite literal_multiply_numeric,secp_field_integer_mod;apply secp_field_integer_mul.
Qed.
Lemma secp_field_word_square x:secp_field_word (@literal_fe_square Alg.CoreFunSem x)=
 GZnZ.mul feP (secp_field_word x) (secp_field_word x).
Proof.
 unfold secp_field_word;rewrite literal_square_numeric,secp_field_integer_mod;apply secp_field_integer_mul.
Qed.
Lemma secp_field_word_negate x:secp_field_word (@literal_fe_negate Alg.CoreFunSem x)=
 GZnZ.opp feP (secp_field_word x).
Proof.
 unfold secp_field_word;rewrite literal_curve_negate_numeric,secp_field_integer_mod.
 replace (feP-@toZ (WordToZ 8) x) with (feP+ -@toZ (WordToZ 8) x) by ring.
 rewrite secp_field_integer_add,secp_field_integer_p,secp_field_integer_opp.
 unfold secp_group_field;ring.
Qed.
Lemma secp_field_word_multiply_int i x:secp_field_word (@literal_fe_multiply_int i Alg.CoreFunSem x)=
 GZnZ.mul feP (secp_field_integer i) (secp_field_word x).
Proof.
 unfold secp_field_word;rewrite literal_fe_multiply_int_numeric,secp_field_integer_mod;apply secp_field_integer_mul.
Qed.
Local Transparent secp_field_integer.
Lemma secp_field_integer_two:secp_field_integer 2=GZnZ.add feP (GZnZ.one feP) (GZnZ.one feP).
Proof. apply GZnZ.zirr;vm_compute;reflexivity. Qed.
Lemma secp_field_integer_three:secp_field_integer 3=GZnZ.add feP (GZnZ.add feP (GZnZ.one feP) (GZnZ.one feP)) (GZnZ.one feP).
Proof. apply GZnZ.zirr;vm_compute;reflexivity. Qed.
Lemma secp_field_word_halve x:secp_field_word (@literal_fe_halve Alg.CoreFunSem x)=
 GZnZ.div feP (secp_field_word x) (GZnZ.add feP (GZnZ.one feP) (GZnZ.one feP)).
Proof.
 set (h:=secp_field_word (@literal_fe_halve Alg.CoreFunSem x)).
 assert (Double:GZnZ.mul feP (GZnZ.add feP (GZnZ.one feP) (GZnZ.one feP)) h=secp_field_word x).
 { unfold h,secp_field_word,secp_field_integer;apply GZnZ.zirr.
   change ((2*(@toZ (WordToZ 8) (@literal_fe_halve Alg.CoreFunSem x) mod feP)) mod feP=
    @toZ (WordToZ 8) x mod feP).
   rewrite Z.mul_mod_idemp_r by (pose proof secp_group_field_positive;lia).
   exact (literal_fe_halve_double x). }
 transitivity (GZnZ.div feP (GZnZ.mul feP (GZnZ.add feP (GZnZ.one feP) (GZnZ.one feP)) h)
  (GZnZ.add feP (GZnZ.one feP) (GZnZ.one feP))).
 - symmetry;unfold secp_group_field;field;exact (SMain.two_not_zero secp_group_theory).
 - rewrite Double;reflexivity.
Qed.
Lemma secp_field_word_one:secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt)=GZnZ.one feP.
Proof. unfold secp_field_word;rewrite literal_fe_one256_value;apply GZnZ.zirr;reflexivity. Qed.
Lemma secp_field_word_zero_test x:secp_group_zero_test (secp_field_word x)=
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem x).
Proof.
 unfold secp_group_zero_test,secp_field_word,secp_field_integer;cbn [GZnZ.val].
 rewrite canonical_fe_is_zero_numeric.
 rewrite <-canonical_field_order_matches_limb_model.
 apply word_mod_field_zero;apply word_value_bounds.
Qed.
Lemma secp_field_word_zero:secp_field_word (@Word.zero 8 Alg.CoreFunSem tt)=GZnZ.zero feP.
Proof. unfold secp_field_word;rewrite Word.zero_correct;apply GZnZ.zirr;reflexivity. Qed.
