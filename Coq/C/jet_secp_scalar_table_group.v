(** Compose the actual scalarTable5 seed, pass1 tree and balanced pass2. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_field_word_group C.jet_secp_jacobian_word_group
 C.jet_secp_jacobian_word_transforms C.jet_secp_jacobian_mixed_word_group
 C.jet_secp_table_walk_group C.jet_secp_table_pass2_group C.jet_secp_scalar_table_literal
 C.jet_secp_table_affine_nonzero C.jet_secp_table_affine_seed C.jet_secp_literal_add_program
 C.jet_secp_double_literal C.jet_secp_rescale_literal C.jet_secp_curve_literal.
Require Import C.jet_secp_table_pass1_group.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_scalar_table_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque literal_gej_double literal_gej_zinv literal_pass1_8 literal_pass2_8
 literal_fe_one256 C.jet_secp_negate_literal_contract.literal_fe_multiply
 literal_scalar_table5 secp_field_word SMain.add EGroup.gpow secp_curve_group.
Lemma literal_scalar_table5_step (ax ay az:Ty.tySem (Word 8)):
 let d:=@literal_gej_double Alg.CoreFunSem ((ax,ay),az) in
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d) in
 let firstPass:=@literal_pass1_8 Alg.CoreFunSem ((seed,az),fst d) in
 @literal_scalar_table5 Alg.CoreFunSem ((ax,ay),az)=
 (@C.jet_secp_negate_literal_contract.literal_fe_multiply Alg.CoreFunSem (snd d,snd firstPass),
  @literal_pass2_8 Alg.CoreFunSem (fst firstPass)).
Proof. reflexivity. Qed.
Lemma secp_scalar_table_context_field (ax ay:Ty.tySem (Word 8)):
 let d:=@literal_gej_double Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt) in
 let seed:=@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d) in
 secp_field_word (fst (@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)))=
 GZnZ.mul feP (secp_field_word (snd d))
  (secp_field_word (snd (literal_table_advance 7 (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d)))).
Proof.
 cbn zeta;rewrite literal_scalar_table5_step;cbn zeta;cbn [fst snd].
 rewrite secp_field_word_mul.
 apply (f_equal2 (GZnZ.mul feP));[reflexivity|].
 apply f_equal;apply literal_table_pass1_last.
Qed.
Local Transparent secp_group_table_advance.
Lemma secp_group_table_advance_odd (n:nat) (p:secp_group_point):
 secp_group_table_advance n p (SMain.add secp_group_theory p p)=
 EGroup.gpow p secp_curve_group (2*Z.of_nat n+1).
Proof.
 induction n as [|n IH];cbn [secp_group_table_advance].
 - symmetry;apply secp_group_power_one.
 - rewrite IH,Nat2Z.inj_succ.
   replace (2*Z.succ (Z.of_nat n)+1) with ((2*Z.of_nat n+1)+2) by ring.
   symmetry.
   transitivity (secp_group_add (EGroup.gpow p secp_curve_group (2*Z.of_nat n+1))
     (EGroup.gpow p secp_curve_group 2)).
   { exact (secp_group_power_add p (2*Z.of_nat n+1) 2 ltac:(lia) ltac:(lia)). }
   assert (Two:EGroup.gpow p secp_curve_group 2=SMain.add secp_group_theory p p).
   { transitivity (C.jet_secp_curve_group_power.secp_group_add
      (EGroup.gpow p secp_curve_group 1) (EGroup.gpow p secp_curve_group 1)).
     - exact (secp_group_power_add p 1 1 ltac:(lia) ltac:(lia)).
     - rewrite !secp_group_power_one;reflexivity. }
   unfold secp_group_add;apply f_equal;exact Two.
Qed.
Local Opaque secp_group_table_advance.
Theorem secp_literal_scalar_table5_group (ax ay:Ty.tySem (Word 8)) (p:secp_group_point):
 Bit.toBool (@literal_ge_is_on_curve Alg.CoreFunSem (ax,ay))=Datatypes.true ->
 secp_jacobian_word_rep (GZnZ.one feP) ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt) p ->
 let result:=@literal_scalar_table5 Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt) in
 secp_field_word (fst result)<>GZnZ.zero feP /\
 secp_table_vector_group 3 (snd result)
 (((EGroup.gpow p secp_curve_group 1,EGroup.gpow p secp_curve_group 3),
   (EGroup.gpow p secp_curve_group 5,EGroup.gpow p secp_curve_group 7)),
  ((EGroup.gpow p secp_curve_group 9,EGroup.gpow p secp_curve_group 11),
   (EGroup.gpow p secp_curve_group 13,EGroup.gpow p secp_curve_group 15)))
 (secp_field_word (fst result)).
Proof.
 intros Valid Represented;cbn zeta.
 pose proof (secp_field_word_flag_false _ (literal_affine_scalar_table_nonzero ax ay Valid)) as OutputNonzero.
 destruct (literal_table_affine_seed ax ay Valid) as [_ [_ DoubleFlag]].
 set (d:=@literal_gej_double Alg.CoreFunSem ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)) in *.
 set (seed:=@literal_gej_zinv Alg.CoreFunSem ((ax,ay),snd d)).
 pose proof (secp_field_word_flag_false _ DoubleFlag) as DoubleNonzero.
 pose proof (secp_literal_zinv_context_group (GZnZ.one feP) ax ay
  (@literal_fe_one256 Alg.CoreFunSem tt) (snd d) p DoubleNonzero Represented) as Start.
 rewrite secp_field_word_one in Start.
 assert (UnitProduct:forall t:secp_group_field,GZnZ.mul feP (GZnZ.mul feP (GZnZ.one feP) (GZnZ.one feP)) t=t).
 { intro t;unfold secp_group_field in *;ring. }
 rewrite UnitProduct in Start.
 pose proof (secp_literal_double_group (GZnZ.one feP) ax ay (@literal_fe_one256 Alg.CoreFunSem tt) p Represented) as Double.
 change (secp_jacobian_word_rep (GZnZ.one feP) d (SMain.add secp_group_theory p p)) in Double.
 pose proof (secp_affine_from_jacobian (GZnZ.one feP) d (SMain.add secp_group_theory p p) Double) as Increment.
 assert (UnitLeft:forall t:secp_group_field,GZnZ.mul feP (GZnZ.one feP) t=t).
 { intro t;unfold secp_group_field in *;ring. }
 rewrite UnitLeft in Increment.
 assert (Finite:forall j,(j<7)%nat ->
  @C.jet_secp_literal_gej_predicate.literal_gej_is_infinity Alg.CoreFunSem
   (literal_table_advance j (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d))=inl tt).
 { intros j Range;apply secp_literal_affine_table_walk_finite;[exact Valid|lia]. }
 pose proof (secp_literal_pass1_tree_group (secp_field_word (snd d))
  (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d) p (SMain.add secp_group_theory p p)
  DoubleNonzero Start Increment Finite) as Tree.
 pose proof (secp_scalar_table_context_field ax ay) as Context.
 change (secp_field_word (fst (@literal_scalar_table5 Alg.CoreFunSem
  ((ax,ay),@literal_fe_one256 Alg.CoreFunSem tt)))=
  GZnZ.mul feP (secp_field_word (snd d))
  (secp_field_word (snd (literal_table_advance 7 (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d))))) in Context.
 assert (LastNonzero:GZnZ.mul feP (secp_field_word (snd d))
  (secp_field_word (snd (literal_table_advance 7 (seed,@literal_fe_one256 Alg.CoreFunSem tt) (fst d))))<>GZnZ.zero feP)
  by (rewrite <-Context;exact OutputNonzero).
 pose proof (secp_pass2_oct_group _ _ _ _ Tree LastNonzero) as Table.
 rewrite !secp_group_table_advance_odd in Table.
 split;[exact OutputNonzero|].
 refine (eq_ind_r (fun ctx=>secp_table_vector_group 3 _ _ ctx) _ Context).
 rewrite literal_scalar_table5_step;cbn zeta;fold d seed;cbn [fst snd].
 exact Table.
Qed.
