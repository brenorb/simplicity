(** Reuse the existing affine-table finiteness witnesses and interpret the
    actual pass1 walk and ratios, before constructing its balanced tree. *)
From Coq Require Import ZArith Lia List Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_field_word_group C.jet_secp_jacobian_word_group C.jet_secp_jacobian_mixed_word_group
 C.jet_secp_jacobian_mixed_ratio C.jet_secp_scalar_table_literal C.jet_secp_add_literal
 C.jet_secp_literal_add_program C.jet_secp_literal_gej_predicate C.jet_secp_canonical_zero
 C.jet_secp_double_literal C.jet_secp_rescale_literal C.jet_secp_curve_literal
 C.jet_secp_table_affine_seed C.jet_secp_table_affine_nonzero C.jet_secp_table_normalized_step
 C.jet_secp_table_step_nonzero C.jet_toZ.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_table_walk_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque literal_gej_ge_add_ex literal_gej_ge_add literal_gej_is_infinity
 canonical_fe_is_zero literal_gej_double literal_gej_zinv literal_fe_one256 SMain.add.
Fixpoint secp_group_table_advance (n:nat) (p q:secp_group_point):secp_group_point:=
 match n with
 | Datatypes.O=>p
 | Datatypes.S k=>SMain.add secp_group_theory (secp_group_table_advance k p q) q end.
Lemma secp_literal_mixed_value_snd (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge):
 snd (@literal_gej_ge_add_ex Alg.CoreFunSem (a,b))=@literal_gej_ge_add Alg.CoreFunSem (a,b).
Proof. reflexivity. Qed.
Lemma secp_literal_mixed_group_pair (c:secp_group_field)
 (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge) (p q:secp_group_point):
 c<>GZnZ.zero feP ->secp_jacobian_word_rep c a p ->
 secp_jacobian_word_rep c (b,@literal_fe_one256 Alg.CoreFunSem tt) q ->
 secp_jacobian_word_rep c (snd (@literal_gej_ge_add_ex Alg.CoreFunSem (a,b))) (SMain.add secp_group_theory p q).
Proof.
 rewrite secp_literal_mixed_value_snd;destruct a as [[x y] z],b as [bx byword];apply secp_literal_mixed_group.
Qed.
Theorem secp_literal_table_advance_group (n:nat) (c:secp_group_field)
 (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge) (p q:secp_group_point):
 c<>GZnZ.zero feP ->secp_jacobian_word_rep c a p ->
 secp_jacobian_word_rep c (b,@literal_fe_one256 Alg.CoreFunSem tt) q ->
 secp_jacobian_word_rep c (literal_table_advance n a b) (secp_group_table_advance n p q).
Proof.
 intros Nonzero Start Increment;induction n as [|n IH];cbn [literal_table_advance secp_group_table_advance].
 - exact Start.
 - apply secp_literal_mixed_group_pair;assumption.
Qed.
Local Opaque literal_table_advance secp_group_table_advance.
Lemma secp_literal_finite_from_z (a:Ty.tySem literal_table_gej):
 Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem (snd a))=Datatypes.false ->
 @literal_gej_is_infinity Alg.CoreFunSem a=inl tt.
Proof.
 destruct a as [[x y] z].
 change (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem z)=Datatypes.false ->
  @canonical_fe_is_zero Alg.CoreFunSem z=inl tt).
 destruct (@canonical_fe_is_zero Alg.CoreFunSem z) as [b|b];destruct b;intro Flag;[reflexivity|discriminate].
Qed.
Theorem secp_literal_affine_table_walk_finite (ax ay:Ty.tySem (Word 8)) (j:nat):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->(j<=7)%nat ->
 let d:=@literal_gej_double Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt) in
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d) in
 @literal_gej_is_infinity Alg.CoreFunSem
  (literal_table_advance j (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d))=inl tt.
Proof.
 intros Valid Range;cbn zeta;apply secp_literal_finite_from_z.
 pose proof (literal_table_affine_curve ax ay Valid) as Curve.
 destruct (literal_table_seed_residue ax ay Valid) as [Start Increment].
 destruct (literal_table_walk_residue j (@toZ (WordToZ 8) ax) (@toZ (WordToZ 8) ay) _ _
  Range Curve Start Increment) as [Scale Representation].
 assert (Member:In (2*j+1)%nat table_odd_indices).
 { clear -Range;unfold table_odd_indices;cbn [In];lia. }
 exact (table_point_residue_finite (2*j+1)%nat (@toZ (WordToZ 8) ax) (@toZ (WordToZ 8) ay)
  _ _ Member Curve Scale Representation).
Qed.
Lemma secp_literal_mixed_ratio_field_pair (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge):
 @literal_gej_is_infinity Alg.CoreFunSem a=inl tt ->
 let result:=@literal_gej_ge_add_ex Alg.CoreFunSem (a,b) in
 secp_field_word (snd (snd result))=
 GZnZ.mul feP (secp_field_word (fst result)) (secp_field_word (snd a)).
Proof. destruct a as [[x y] z],b as [bx byword];apply literal_mixed_finite_ratio_field. Qed.
Local Opaque secp_field_word.
Theorem secp_literal_table_ratio_context (n:nat) (c:secp_group_field)
 (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge):
 @literal_gej_is_infinity Alg.CoreFunSem (literal_table_advance n a b)=inl tt ->
 GZnZ.mul feP c (secp_field_word (snd (literal_table_advance (S n) a b)))=
 GZnZ.mul feP (GZnZ.mul feP c (secp_field_word (snd (literal_table_advance n a b))))
  (secp_field_word (literal_table_ratio n a b)).
Proof.
 intro Finite.
 Local Transparent literal_table_advance.
 change (GZnZ.mul feP c (secp_field_word (snd (snd (@literal_gej_ge_add_ex Alg.CoreFunSem
  (literal_table_advance n a b,b)))))=
 GZnZ.mul feP (GZnZ.mul feP c (secp_field_word (snd (literal_table_advance n a b))))
  (secp_field_word (literal_table_ratio n a b))).
 rewrite secp_literal_mixed_ratio_field_pair by exact Finite.
 unfold literal_table_ratio,secp_group_field in *;ring.
Qed.
