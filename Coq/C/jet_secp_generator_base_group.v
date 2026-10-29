(** The actual generator bases used by the original literal program. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_curve_group_certificate C.jet_secp_curve_group_lambda
 C.jet_secp_generate_literal C.jet_secp_field_word_group C.jet_secp_jacobian_group
 C.jet_secp_jacobian_affine_group C.jet_secp_jacobian_word_group C.jet_secp_table_pass2_group
 C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_generator_base_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Definition secp_generator_base_x second:=secp_field_word (fst (literal_generator_base_word second)).
Definition secp_generator_base_y second:=secp_field_word (snd (literal_generator_base_word second)).
Lemma secp_generator_base_curve second:
 SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_generator_base_y second) 2=
 GZnZ.add feP (GZnZ.add feP
  (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_generator_base_x second) 3)
  (GZnZ.mul feP (GZnZ.zero feP) (secp_generator_base_x second))) secp_group_seven.
Proof. destruct second;apply GZnZ.zirr;vm_compute;reflexivity. Qed.
Definition secp_generator_base_group second:secp_group_point:=
 SMain.curve_elt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP) (GZnZ.zero feP) secp_group_seven
  (secp_generator_base_x second) (secp_generator_base_y second) (secp_generator_base_curve second).
Lemma secp_generator_base_low:secp_generator_base_group false=secp_group_generator.
Proof.
 apply (SMain.curve_elt_irr secp_group_theory);apply GZnZ.zirr;vm_compute;reflexivity.
Qed.
Definition secp_generator_high_projective:=secp_group_projective_power secp_group_generator_projective
 (Z.to_pos (2^128)).
Lemma secp_generator_high_coordinates:
 let p:=secp_generator_high_projective in
 GZnZ.val feP (SMain.z p)<>0 /\
 GZnZ.val feP (SMain.x p)=GZnZ.val feP (GZnZ.mul feP (secp_generator_base_x true) (SMain.z p)) /\
 GZnZ.val feP (SMain.y p)=GZnZ.val feP (GZnZ.mul feP (secp_generator_base_y true) (SMain.z p)).
Proof. vm_compute;repeat split;discriminate. Qed.
Lemma secp_generator_base_high:
 secp_generator_base_group true=EGroup.gpow secp_group_generator secp_curve_group (2^128).
Proof.
 pose proof secp_generator_high_coordinates as [Nonzero [X Y]].
 assert (Projected:SMain.pe2e secp_group_theory secp_generator_high_projective=secp_generator_base_group true).
 { apply secp_group_projective_affine;assumption. }
 unfold secp_generator_high_projective in Projected.
 rewrite secp_group_projective_power_correct,secp_group_generator_projective_value,
  secp_group_power_pos_correct in Projected.
 symmetry;exact Projected.
 Local Opaque EGroup.gpow secp_group_generator SMain.pe2e secp_group_projective_power secp_group_power_pos.
Qed.
Lemma secp_affine_unit_group (x y:Ty.tySem (Word 8))
 (Curve:SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_field_word y) 2=
 GZnZ.add feP (GZnZ.add feP (SMain.pow (GZnZ.one feP) (GZnZ.mul feP) (secp_field_word x) 3)
  (GZnZ.mul feP (GZnZ.zero feP) (secp_field_word x))) secp_group_seven):
 secp_affine_word_rep (GZnZ.one feP) (x,y)
 (SMain.curve_elt (GZnZ.one feP) (GZnZ.add feP) (GZnZ.mul feP)
  (GZnZ.zero feP) secp_group_seven (secp_field_word x) (secp_field_word y) Curve).
Proof.
 unfold secp_affine_word_rep,secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep.
 cbn [fst snd];rewrite secp_field_word_one.
 replace (GZnZ.mul feP (GZnZ.one feP) (GZnZ.one feP)) with (GZnZ.one feP) by ring.
 assert (Jacobian:secp_jacobian_curve (secp_field_word x) (secp_field_word y) (GZnZ.one feP)).
 { unfold secp_jacobian_curve;cbn [SMain.pow] in Curve;unfold secp_group_field in *;ring [Curve]. }
 exists Jacobian.
 rewrite (secp_jacobian_affine_value _ _ _ Jacobian (SMain.one_not_zero secp_group_theory)).
 apply (SMain.curve_elt_irr secp_group_theory);field;discriminate.
Qed.
Theorem secp_literal_generator_base_group second:
 secp_affine_word_rep (GZnZ.one feP) (literal_generator_base_word second)
  (EGroup.gpow secp_group_generator secp_curve_group (if second then 2^128 else 1)).
Proof.
 assert (Represented:secp_affine_word_rep (GZnZ.one feP) (literal_generator_base_word second)
  (secp_generator_base_group second)).
 { apply secp_affine_unit_group. }
 destruct second.
 - rewrite <-secp_generator_base_high;exact Represented.
 - rewrite secp_group_power_one,<-secp_generator_base_low;exact Represented.
Qed.
