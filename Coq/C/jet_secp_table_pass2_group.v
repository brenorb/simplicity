(** The original balanced pass2 shares a denominator without changing the
    represented points. The tree premise records the original pass1 ratios;
    its construction for scalarTable5 is a separate remaining obligation. *)
From Coq Require Import ZArith Field.
From Coqprime.elliptic Require Import GZnZ SMain.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_fe_math C.jet_secp_field_prime C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_jacobian_group C.jet_secp_jacobian_word_group C.jet_secp_jacobian_word_transforms
 C.jet_secp_field_word_group C.jet_secp_scalar_table_literal C.jet_secp_scalar_table_pass2
 C.jet_secp_rescale_literal C.jet_secp_literal_add_program C.jet_secp_negate_literal_contract.
Local Open Scope Z_scope.
Set Default Timeout 10.
Add Field secp_table_pass2_field : (GZnZ.FZpZ feP secp256k1_field_prime).
Definition secp_affine_word_rep (c:secp_group_field) (a:Ty.tySem literal_table_ge) (p:secp_group_point):=
 secp_jacobian_word_rep c (a,@literal_fe_one256 Alg.CoreFunSem tt) p.
Fixpoint secp_group_vector (n:nat):Set:=match n with
 | Datatypes.O=>secp_group_point
 | Datatypes.S k=>(secp_group_vector k*secp_group_vector k)%type end.
Fixpoint secp_table_vector_group (n:nat):
 Ty.tySem (literal_table_vector n) ->secp_group_vector n ->secp_group_field ->Prop:=
 match n with
 | Datatypes.O=>fun a p c=>secp_affine_word_rep c a p
 | Datatypes.S k=>fun a p c=>secp_table_vector_group k (fst a) (fst p) c /\
   secp_table_vector_group k (snd a) (snd p) c end.
Lemma secp_table_vector_group_pair (n:nat) (a b:Ty.tySem (literal_table_vector n))
 (p q:secp_group_vector n) (c:secp_group_field):
 secp_table_vector_group n a p c ->secp_table_vector_group n b q c ->
 secp_table_vector_group (S n) (a,b) (p,q) c.
Proof. exact (fun Left Right=>conj Left Right). Qed.
Fixpoint secp_table_tree_group (n:nat):
 Ty.tySem (literal_table_tree n) ->secp_group_vector n ->secp_group_field ->secp_group_field ->Prop:=
 match n with
 | Datatypes.O=>fun a p first last=>first=last /\secp_affine_word_rep last a p
 | Datatypes.S k=>fun t p first last=>exists left_last right_first,
   secp_table_tree_group k (fst (snd t)) (fst p) first left_last /\
   secp_table_tree_group k (snd (snd t)) (snd p) right_first last /\
   right_first=GZnZ.mul feP left_last (secp_field_word (fst t)) end.
Local Opaque secp_affine_word_rep secp_field_word literal_pass2_1 literal_pass2_2 literal_pass2_4 literal_pass2_8
 literal_fe_multiply literal_gej_zinv literal_fe_one256.
Lemma secp_pass2_leaf_group (c:secp_group_field) (a:Ty.tySem literal_table_ge) (s:Ty.tySem (Word 8)) (p:secp_group_point):
 secp_field_word s<>GZnZ.zero feP ->secp_affine_word_rep c a p ->
 secp_affine_word_rep (GZnZ.mul feP c (secp_field_word s)) (@literal_gej_zinv Alg.CoreFunSem (a,s)) p.
Proof.
 destruct a as [x y];intros Nonzero Represented.
 pose proof (secp_literal_zinv_context_group c x y (@literal_fe_one256 Alg.CoreFunSem tt) s p Nonzero Represented) as Scaled.
 rewrite secp_field_word_one in Scaled.
 replace (GZnZ.mul feP c (GZnZ.one feP)) with c in Scaled by (unfold secp_group_field in *;ring).
 exact Scaled.
Qed.
Lemma secp_pass2_join_scale (left_last right_first last root carry scale:secp_group_field):
 right_first=GZnZ.mul feP left_last root ->
 GZnZ.mul feP right_first carry=GZnZ.mul feP last scale ->
 last<>GZnZ.zero feP ->scale<>GZnZ.zero feP ->
 GZnZ.mul feP left_last (GZnZ.mul feP root carry)=GZnZ.mul feP last scale /\
 left_last<>GZnZ.zero feP /\GZnZ.mul feP root carry<>GZnZ.zero feP.
Proof.
 intros Link Carry NonzeroLast NonzeroScale.
 assert (Equation:GZnZ.mul feP left_last (GZnZ.mul feP root carry)=GZnZ.mul feP last scale).
 { rewrite Link in Carry;unfold secp_group_field in *;ring [Carry]. }
 assert (Product:GZnZ.mul feP last scale<>GZnZ.zero feP)
  by (apply (SMain.Kmult_integral_contrapositive secp_group_theory);assumption).
 split;[exact Equation|];split;intro Zero;
 apply Product;rewrite <-Equation,Zero;unfold secp_group_field in *;ring.
Qed.
Theorem secp_pass2_pair_group (t:Ty.tySem (literal_table_tree 1)) (points:secp_group_vector 1)
 (first last:secp_group_field) (s:Ty.tySem (Word 8)):
 secp_table_tree_group 1 t points first last ->last<>GZnZ.zero feP ->secp_field_word s<>GZnZ.zero feP ->
 let result:=@literal_pass2_2 Alg.CoreFunSem (t,s) in
 secp_table_vector_group 1 (fst result) points (GZnZ.mul feP last (secp_field_word s)) /\
 GZnZ.mul feP first (secp_field_word (snd result))=GZnZ.mul feP last (secp_field_word s) /\
 secp_field_word (snd result)<>GZnZ.zero feP.
Proof.
 destruct t as [r [a b]],points as [p q];intros Tree LastNonzero ScaleNonzero.
 cbn [secp_table_tree_group fst snd] in Tree.
 destruct Tree as [left_last [right_first [[First LeftRep] [[Last RightRep] Link]]]].
 subst left_last right_first.
 destruct (secp_pass2_join_scale first last last (secp_field_word r) (secp_field_word s) (secp_field_word s)
  Link eq_refl LastNonzero ScaleNonzero) as [Common [FirstNonzero ScaleLeft]].
 rewrite literal_pass2_2_step;cbn [fst snd secp_table_vector_group].
 rewrite !secp_field_word_mul.
 split.
 - split.
   + pose proof (secp_pass2_leaf_group first a (@literal_fe_multiply Alg.CoreFunSem (r,s)) p)
      as LeftScaled.
     rewrite secp_field_word_mul in LeftScaled.
     specialize (LeftScaled ScaleLeft LeftRep);rewrite Common in LeftScaled;exact LeftScaled.
   + apply secp_pass2_leaf_group;assumption.
 - split;assumption.
Qed.
Theorem secp_pass2_quad_group (t:Ty.tySem (literal_table_tree 2)) (points:secp_group_vector 2)
 (first last:secp_group_field) (s:Ty.tySem (Word 8)):
 secp_table_tree_group 2 t points first last ->last<>GZnZ.zero feP ->secp_field_word s<>GZnZ.zero feP ->
 let result:=@literal_pass2_4 Alg.CoreFunSem (t,s) in
 secp_table_vector_group 2 (fst result) points (GZnZ.mul feP last (secp_field_word s)) /\
 GZnZ.mul feP first (secp_field_word (snd result))=GZnZ.mul feP last (secp_field_word s) /\
 secp_field_word (snd result)<>GZnZ.zero feP.
Proof.
 destruct t as [r [left right]],points as [pl pr];intros Tree LastNonzero ScaleNonzero.
 change (exists ll rf,secp_table_tree_group 1 left pl first ll /\
  secp_table_tree_group 1 right pr rf last /\rf=GZnZ.mul feP ll (secp_field_word r)) in Tree.
 destruct Tree as [ll [rf [LeftTree [RightTree Link]]]].
 pose proof (secp_pass2_pair_group right pr rf last s RightTree LastNonzero ScaleNonzero) as RightFacts.
 cbn zeta in RightFacts.
 set (rr:=@literal_pass2_2 Alg.CoreFunSem (right,s)) in *.
 destruct RightFacts as [RightVector [RightCarry RightNonzero]].
 destruct (secp_pass2_join_scale ll rf last (secp_field_word r) (secp_field_word (snd rr)) (secp_field_word s)
  Link RightCarry LastNonzero ScaleNonzero) as [Common [LeftLastNonzero LeftScaleNonzero]].
 set (ls:=@literal_fe_multiply Alg.CoreFunSem (r,snd rr)).
 assert (LeftScale:secp_field_word ls=GZnZ.mul feP (secp_field_word r) (secp_field_word (snd rr)))
  by (unfold ls;apply secp_field_word_mul).
 assert (LeftScaleNZ:secp_field_word ls<>GZnZ.zero feP) by (rewrite LeftScale;exact LeftScaleNonzero).
 pose proof (secp_pass2_pair_group left pl first ll ls LeftTree LeftLastNonzero LeftScaleNZ) as LeftFacts.
 cbn zeta in LeftFacts.
 destruct LeftFacts as [LeftVector [LeftCarry LeftNonzero]].
 rewrite LeftScale,Common in LeftVector,LeftCarry.
 set (lr:=@literal_pass2_2 Alg.CoreFunSem (left,ls)) in *.
 rewrite literal_pass2_4_step;cbn zeta;fold rr ls lr.
 (* Keep the computed words abstract after their contracts are established. *)
 clearbody rr ls lr.
 split.
 - exact (secp_table_vector_group_pair 1 (fst lr) (fst rr) pl pr
    (GZnZ.mul feP last (secp_field_word s)) LeftVector RightVector).
 - exact (conj LeftCarry LeftNonzero).
Qed.
Theorem secp_pass2_oct_group (t:Ty.tySem (literal_table_tree 3)) (points:secp_group_vector 3)
 (first last:secp_group_field):
 secp_table_tree_group 3 t points first last ->last<>GZnZ.zero feP ->
 secp_table_vector_group 3 (@literal_pass2_8 Alg.CoreFunSem t) points last.
Proof.
 destruct t as [r [left right]],points as [pl pr];intros Tree LastNonzero.
 change (exists ll rf,secp_table_tree_group 2 left pl first ll /\
  secp_table_tree_group 2 right pr rf last /\rf=GZnZ.mul feP ll (secp_field_word r)) in Tree.
 destruct Tree as [ll [rf [LeftTree [RightTree Link]]]].
 assert (ScaleNonzero:secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt)<>GZnZ.zero feP).
 { rewrite secp_field_word_one;exact (SMain.one_not_zero secp_group_theory). }
 assert (LastScale:GZnZ.mul feP last (secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt))=last).
 { rewrite secp_field_word_one;unfold secp_group_field in *;ring. }
 pose proof (secp_pass2_quad_group right pr rf last (@literal_fe_one256 Alg.CoreFunSem tt)
  RightTree LastNonzero ScaleNonzero) as RightFacts.
 cbn zeta in RightFacts.
 set (rr:=@literal_pass2_4 Alg.CoreFunSem (right,@literal_fe_one256 Alg.CoreFunSem tt)) in *.
 destruct RightFacts as [RightVector [RightCarry RightNonzero]].
 destruct (secp_pass2_join_scale ll rf last (secp_field_word r) (secp_field_word (snd rr))
  (secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt))
  Link RightCarry LastNonzero ScaleNonzero) as [Common [LeftLastNonzero LeftScaleNonzero]].
 set (ls:=@literal_fe_multiply Alg.CoreFunSem (r,snd rr)).
 assert (LeftScale:secp_field_word ls=GZnZ.mul feP (secp_field_word r) (secp_field_word (snd rr)))
  by (unfold ls;apply secp_field_word_mul).
 assert (LeftScaleNZ:secp_field_word ls<>GZnZ.zero feP) by (rewrite LeftScale;exact LeftScaleNonzero).
 pose proof (secp_pass2_quad_group left pl first ll ls LeftTree LeftLastNonzero LeftScaleNZ) as LeftFacts.
 cbn zeta in LeftFacts.
 destruct LeftFacts as [LeftVector [LeftCarry LeftNonzero]].
 rewrite LeftScale,Common in LeftVector.
 set (lr:=@literal_pass2_4 Alg.CoreFunSem (left,ls)) in *.
 rewrite literal_pass2_8_step;cbn zeta;fold rr ls lr.
 (* Keep the computed words abstract after their contracts are established. *)
 clearbody rr ls lr.
 assert (Vector:secp_table_vector_group 3 (fst lr,fst rr) (pl,pr)
  (GZnZ.mul feP last (secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt)))).
 { change (secp_table_vector_group 2 (fst lr) pl
    (GZnZ.mul feP last (secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt))) /\
   secp_table_vector_group 2 (fst rr) pr
    (GZnZ.mul feP last (secp_field_word (@literal_fe_one256 Alg.CoreFunSem tt)))).
   exact (conj LeftVector RightVector). }
 rewrite LastScale in Vector;exact Vector.
Qed.
