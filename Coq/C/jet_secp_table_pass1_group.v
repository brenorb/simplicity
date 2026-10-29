(** Construct the balanced pass1 relation from the actual walk and ratios. *)
From Coq Require Import ZArith Lia Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_field_word_group C.jet_secp_jacobian_word_group C.jet_secp_table_pass2_group
 C.jet_secp_table_walk_group C.jet_secp_scalar_table_literal C.jet_secp_add_literal
 C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_table_pass1_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Local Opaque secp_field_word literal_gej_ge_add_ex literal_gej_ge_add literal_table_ratio
 literal_pass1_8 literal_fe_one256 SMain.add.
Lemma secp_affine_from_jacobian (c:secp_group_field) (a:Ty.tySem literal_table_gej) (p:secp_group_point):
 secp_jacobian_word_rep c a p ->
 secp_affine_word_rep (GZnZ.mul feP c (secp_field_word (snd a))) (fst a) p.
Proof.
 destruct a as [[x y] z].
 unfold secp_affine_word_rep,secp_jacobian_word_rep,secp_jacobian_word_fields,secp_jacobian_context_rep;
 cbn [fst snd];rewrite secp_field_word_one.
 replace (GZnZ.mul feP (GZnZ.mul feP c (secp_field_word z)) (GZnZ.one feP))
 with (GZnZ.mul feP c (secp_field_word z)) by (unfold secp_group_field in *;ring).
 exact (fun R=>R).
Qed.
Lemma secp_table_tree_group_leaf (a:Ty.tySem literal_table_ge) (p:secp_group_point) (c:secp_group_field):
 secp_affine_word_rep c a p ->secp_table_tree_group 0 a p c c.
Proof. exact (fun R=>conj eq_refl R). Qed.
Lemma secp_table_tree_group_node (n:nat) (r:Ty.tySem (Word 8))
 (left right:Ty.tySem (literal_table_tree n)) (pl pr:secp_group_vector n)
 (first last ll rf:secp_group_field):
 secp_table_tree_group n left pl first ll ->secp_table_tree_group n right pr rf last ->
 rf=GZnZ.mul feP ll (secp_field_word r) ->
 secp_table_tree_group (S n) (r,(left,right)) (pl,pr) first last.
Proof.
 intros Left Right Link;exists ll,rf;exact (conj Left (conj Right Link)).
Qed.
Theorem secp_literal_pass1_tree_group (c:secp_group_field)
 (a:Ty.tySem literal_table_gej) (b:Ty.tySem literal_table_ge) (p q:secp_group_point):
 c<>GZnZ.zero feP ->secp_jacobian_word_rep c a p ->
 secp_jacobian_word_rep c (b,@literal_fe_one256 Alg.CoreFunSem tt) q ->
 (forall j,(j<7)%nat ->@C.jet_secp_literal_gej_predicate.literal_gej_is_infinity Alg.CoreFunSem
  (literal_table_advance j a b)=inl tt) ->
 secp_table_tree_group 3 (fst (@literal_pass1_8 Alg.CoreFunSem (a,b)))
 (((secp_group_table_advance 0 p q,secp_group_table_advance 1 p q),
   (secp_group_table_advance 2 p q,secp_group_table_advance 3 p q)),
  ((secp_group_table_advance 4 p q,secp_group_table_advance 5 p q),
   (secp_group_table_advance 6 p q,secp_group_table_advance 7 p q)))
 (GZnZ.mul feP c (secp_field_word (snd a)))
 (GZnZ.mul feP c (secp_field_word (snd (literal_table_advance 7 a b)))).
Proof.
 intros Nonzero Start Increment Finite.
 set (ctx:=fun j=>GZnZ.mul feP c (secp_field_word (snd (literal_table_advance j a b)))).
 assert (Leaves:forall j,secp_affine_word_rep (ctx j) (fst (literal_table_advance j a b))
  (secp_group_table_advance j p q)).
 { intro j;apply secp_affine_from_jacobian;apply secp_literal_table_advance_group;assumption. }
 assert (Links:forall j,(j<7)%nat ->ctx (S j)=GZnZ.mul feP (ctx j) (secp_field_word (literal_table_ratio j a b))).
 { intros j Range;apply secp_literal_table_ratio_context;apply Finite;exact Range. }
 rewrite literal_pass1_8_step;cbn [fst].
 eapply secp_table_tree_group_node with (ll:=ctx 3%nat) (rf:=ctx 4%nat).
 - eapply secp_table_tree_group_node with (ll:=ctx 1%nat) (rf:=ctx 2%nat).
   + eapply secp_table_tree_group_node with (ll:=ctx 0%nat) (rf:=ctx 1%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 0%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 1%nat).
     * apply Links;lia.
   + eapply secp_table_tree_group_node with (ll:=ctx 2%nat) (rf:=ctx 3%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 2%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 3%nat).
     * apply Links;lia.
   + apply Links;lia.
 - eapply secp_table_tree_group_node with (ll:=ctx 5%nat) (rf:=ctx 6%nat).
   + eapply secp_table_tree_group_node with (ll:=ctx 4%nat) (rf:=ctx 5%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 4%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 5%nat).
     * apply Links;lia.
   + eapply secp_table_tree_group_node with (ll:=ctx 6%nat) (rf:=ctx 7%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 6%nat).
     * apply secp_table_tree_group_leaf;exact (Leaves 7%nat).
     * apply Links;lia.
   + apply Links;lia.
 - apply Links;lia.
Qed.
