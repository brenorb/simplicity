(** Compose the actual scalar splits and shared-Z correction of Strauss. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_curve_group_endomorphism C.jet_secp_lookup5_group
 C.jet_secp_signed_group_action C.jet_secp_field_word_group C.jet_secp_jacobian_word_group
 C.jet_secp_strauss_scalar_group C.jet_secp_strauss_window_values C.jet_secp_wnaf5_reconstruction
 C.jet_secp_scalar_split128_literal C.jet_secp_split_literal C.jet_secp_split_half_numeric
 C.jet_secp_canonical_scalar C.jet_secp_generate_small_group C.jet_secp_scalar_table_group
 C.jet_secp_table_pass2_group C.jet_secp_scalar_table_literal C.jet_secp_strauss_complete_program
 C.jet_secp_strauss_program C.jet_secp_literal_add_program C.jet_secp_negate_literal_contract
 C.jet_secp_curve_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_strauss_body_group_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque literal_strauss_body literal_scalar_table5 literal_scalar_split_lambda
 literal_scalar_split128 canonical_scalar_normalize literal_strauss_digits129 literal_fe_multiply secp_field_word.
Local Infix "⊕" := (SMain.add secp_group_theory) (at level 50,left associativity).
Lemma secp_literal_split128_rebuild (raw:Ty.tySem (Word 8)):
 @literal_scalar_split128 Alg.CoreFunSem raw=
 ((Bit.zero,literal_split128_low raw),(Bit.zero,literal_split128_high raw)).
Proof.
 assert (Rebuild:forall
  (s:Ty.tySem (Ty.Prod C.jet_secp_wnaf_literal.literal_wnaf_state C.jet_secp_wnaf_literal.literal_wnaf_state))
  (lo hi:Ty.tySem (Word 7)),s=((Bit.zero,lo),(Bit.zero,hi)) ->
  s=((Bit.zero,snd (fst s)),(Bit.zero,snd (snd s)))).
 { intros s lo hi Equal;rewrite Equal;reflexivity. }
 exact (Rebuild _ _ _ (literal_scalar_split128_step raw)).
Qed.
Lemma secp_strauss_combination_split (p:secp_group_point) (raw ng:Ty.tySem (Word 8)):
 secp_strauss_combination p
 ((secp_wnaf5_state_value (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)),
   secp_wnaf5_state_value (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw))),
  (@toZ (WordToZ 7) (literal_split128_low ng),@toZ (WordToZ 7) (literal_split128_high ng)))=
 secp_group_signed_power p (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))⊕
 secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)).
Proof.
 pose proof (secp_literal_split_group p raw) as Split.
 change (secp_group_signed_power p (secp_wnaf5_state_value (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw)))⊕
  secp_group_signed_power (secp_group_endomorphism p)
   (secp_wnaf5_state_value (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw)))=
  secp_group_signed_power p (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))) in Split.
 unfold secp_strauss_combination;cbn [fst snd];apply f_equal2;[exact Split|].
 rewrite (secp_generator_base_signed_action Datatypes.true (@toZ (WordToZ 7) (literal_split128_high ng))).
 transitivity (secp_group_signed_power secp_group_generator
  (@toZ (WordToZ 7) (literal_split128_low ng)+2^128*@toZ (WordToZ 7) (literal_split128_high ng))).
 - symmetry;apply secp_group_signed_power_add.
 - f_equal;destruct (literal_scalar_split128_numeric ng) as [Low High];rewrite Low,High.
   pose proof (Z.div_mod (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng)) (2^128) ltac:(lia));nia.
Qed.
Lemma secp_strauss_context_correct_group (c:Ty.tySem (Word 8))
 (point:Ty.tySem literal_table_gej) (p:secp_group_point):
 secp_jacobian_word_rep (secp_field_word c) point p ->
 secp_jacobian_word_rep (GZnZ.one feP)
  (fst point,@literal_fe_multiply Alg.CoreFunSem (c,snd point)) p.
Proof.
 destruct point as [[x y] z];intro Represented.
 unfold secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep in *;cbn [fst snd] in *.
 rewrite secp_field_word_mul.
 assert (Unit:forall t:secp_group_field,GZnZ.mul feP (GZnZ.one feP) t=t).
 { intro t;unfold secp_group_field in *;ring. }
 rewrite Unit;exact Represented.
Qed.
Theorem secp_literal_strauss_body_affine_group (raw ng ax ay:Ty.tySem (Word 8)) (p:secp_group_point):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 secp_jacobian_word_rep (GZnZ.one feP) ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt) p ->
 secp_jacobian_word_rep (GZnZ.one feP)
 (@literal_strauss_body Alg.CoreFunSem ((raw,((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)),ng))
 (secp_group_signed_power p (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem raw))⊕
  secp_group_signed_power secp_group_generator (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem ng))).
Proof.
 intros Valid Represented.
 set (context:=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)).
 destruct (secp_literal_scalar_table5_group ax ay p Valid Represented) as [Nonzero Table].
 fold context in Nonzero,Table.
 pose proof (secp_literal_strauss_window_group (fst context) (snd context) p
  (fst (@literal_scalar_split_lambda Alg.CoreFunSem raw))
  (snd (@literal_scalar_split_lambda Alg.CoreFunSem raw))
  (literal_split128_low ng) (literal_split128_high ng) Nonzero Table) as Window.
 rewrite secp_strauss_combination_split in Window.
 rewrite literal_strauss_body_value,literal_strauss_split_lambda_value,literal_strauss_split128_value,
  secp_literal_split128_rebuild.
 cbn [fst snd];fold context.
 apply secp_strauss_context_correct_group;exact Window.
Qed.
