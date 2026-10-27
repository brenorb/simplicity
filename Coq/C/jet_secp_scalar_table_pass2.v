(** The fixed balanced second pass respects field representation. In
    particular it consumes the normalized tree established by the C first
    pass with exactly the result of the unchanged raw-ratio specification. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_secp_scalar_table_literal C.jet_secp_table_field_equiv
 C.jet_secp_odd_table_pass1_bridge C.jet_secp_canonical_normalize C.jet_secp_rescale_literal
 C.jet_secp_negate_literal_contract C.jet_secp_literal_add_program.
Set Default Timeout 10.
Local Opaque literal_fe_multiply literal_gej_zinv canonical_fe_normalize literal_fe_one256.

Lemma literal_pass2_1_step (p:Ty.tySem literal_table_ge) (s:Ty.tySem (Word 8)) :
 @literal_pass2_1 Alg.CoreFunSem (p,s)=@literal_gej_zinv Alg.CoreFunSem (p,s).
Proof. destruct p as [x y];reflexivity. Qed.
Lemma literal_pass2_2_step (r s:Ty.tySem (Word 8)) (p q:Ty.tySem literal_table_ge) :
 @literal_pass2_2 Alg.CoreFunSem ((r,(p,q)),s)=
 ((@literal_gej_zinv Alg.CoreFunSem (p,@literal_fe_multiply Alg.CoreFunSem (r,s)),
   @literal_gej_zinv Alg.CoreFunSem (q,s)),@literal_fe_multiply Alg.CoreFunSem (r,s)).
Proof. destruct p as [x y];destruct q as [u v];reflexivity. Qed.
Local Opaque literal_pass2_1 literal_pass2_2.
Lemma literal_pass2_4_step (r s:Ty.tySem (Word 8)) (left right:Ty.tySem (literal_table_tree 1)) :
 @literal_pass2_4 Alg.CoreFunSem ((r,(left,right)),s)=
 let rr:Ty.tySem (Ty.Prod (literal_table_vector 1) (Word 8)):=@literal_pass2_2 Alg.CoreFunSem (right,s) in
 let lr:Ty.tySem (Ty.Prod (literal_table_vector 1) (Word 8)):=@literal_pass2_2 Alg.CoreFunSem
  (left,@literal_fe_multiply Alg.CoreFunSem (r,snd rr)) in
 ((fst lr,fst rr),snd lr).
Proof. reflexivity. Qed.
Local Opaque literal_pass2_4.
Lemma literal_pass2_8_step (r:Ty.tySem (Word 8)) (left right:Ty.tySem (literal_table_tree 2)) :
 @literal_pass2_8 Alg.CoreFunSem (r,(left,right))=
 let rr:Ty.tySem (Ty.Prod (literal_table_vector 2) (Word 8)):=
  @literal_pass2_4 Alg.CoreFunSem (right,@literal_fe_one256 Alg.CoreFunSem tt) in
 let lr:Ty.tySem (Ty.Prod (literal_table_vector 2) (Word 8)):=
  @literal_pass2_4 Alg.CoreFunSem (left,@literal_fe_multiply Alg.CoreFunSem (r,snd rr)) in
 (fst lr,fst rr).
Proof. reflexivity. Qed.
Local Opaque literal_pass2_8.

Fixpoint table_tree_equiv n : Ty.tySem (literal_table_tree n) -> Ty.tySem (literal_table_tree n) -> Prop :=
 match n as k return Ty.tySem (literal_table_tree k) -> Ty.tySem (literal_table_tree k) -> Prop with
 | Datatypes.O=>fun p q=>table_word_equiv (fst p) (fst q) /\ table_word_equiv (snd p) (snd q)
 | Datatypes.S k=>fun p q=>table_word_equiv (fst p) (fst q) /\
   table_tree_equiv k (fst (snd p)) (fst (snd q)) /\ table_tree_equiv k (snd (snd p)) (snd (snd q)) end.

Lemma table_tree_normalize_equiv n : forall t,
 table_tree_equiv n (literal_table_normalize_tree n t) t.
Proof.
 induction n as [|n IH];intro t.
 - destruct t as [x y];split;apply table_word_normalize_equiv.
 - destruct t as [r [left right]];split;[apply table_word_normalize_equiv|];split;apply IH.
Qed.
Lemma literal_pass2_1_equiv (p q:Ty.tySem literal_table_ge) (s t:Ty.tySem (Word 8)) :
 table_tree_equiv 0 p q -> table_word_equiv s t ->
 @literal_pass2_1 Alg.CoreFunSem (p,s)=@literal_pass2_1 Alg.CoreFunSem (q,t).
Proof.
 intros [HX HY] HS;rewrite !literal_pass2_1_step;apply table_zinv_equiv;assumption.
Qed.
Theorem literal_pass2_2_equiv (p q:Ty.tySem (literal_table_tree 1)) (s t:Ty.tySem (Word 8)) :
 table_tree_equiv 1 p q -> table_word_equiv s t ->
 @literal_pass2_2 Alg.CoreFunSem (p,s)=@literal_pass2_2 Alg.CoreFunSem (q,t).
Proof.
 destruct p as [r [left right]];destruct q as [r' [left' right']].
 intros [ER [EL EH]] HS;destruct EL as [LX LY];destruct EH as [HX HY].
 pose proof (table_multiply_equiv r r' s t ER HS) as Factor.
 rewrite !literal_pass2_2_step,Factor.
 set (f:=@literal_fe_multiply Alg.CoreFunSem (r',t)).
 rewrite (table_zinv_equiv left left' f f LX LY (table_word_equiv_refl f)),
  (table_zinv_equiv right right' s t HX HY HS);reflexivity.
Qed.
Theorem literal_pass2_4_equiv (p q:Ty.tySem (literal_table_tree 2)) (s t:Ty.tySem (Word 8)) :
 table_tree_equiv 2 p q -> table_word_equiv s t ->
 @literal_pass2_4 Alg.CoreFunSem (p,s)=@literal_pass2_4 Alg.CoreFunSem (q,t).
Proof.
 destruct p as [r [left right]];destruct q as [r' [left' right']];intros [ER [EL EH]] HS.
 pose proof (literal_pass2_2_equiv right right' s t EH HS) as Right.
 rewrite !literal_pass2_4_step;cbv zeta;rewrite Right.
 set (rr:=@literal_pass2_2 Alg.CoreFunSem (right',t)).
 change (((fst (@literal_pass2_2 Alg.CoreFunSem (left,@literal_fe_multiply Alg.CoreFunSem (r,snd rr))),fst rr),
  snd (@literal_pass2_2 Alg.CoreFunSem (left,@literal_fe_multiply Alg.CoreFunSem (r,snd rr))))=
 ((fst (@literal_pass2_2 Alg.CoreFunSem (left',@literal_fe_multiply Alg.CoreFunSem (r',snd rr))),fst rr),
  snd (@literal_pass2_2 Alg.CoreFunSem (left',@literal_fe_multiply Alg.CoreFunSem (r',snd rr))))).
 pose proof (table_multiply_equiv r r' (snd rr) (snd rr) ER (table_word_equiv_refl (snd rr))) as Factor.
 refine (eq_trans (f_equal (fun f:Ty.tySem (Word 8)=>
  ((fst (@literal_pass2_2 Alg.CoreFunSem (left,f)),fst rr),
    snd (@literal_pass2_2 Alg.CoreFunSem (left,f)))) Factor) _).
 set (f:=@literal_fe_multiply Alg.CoreFunSem (r',snd rr)).
 exact (f_equal (fun lr:Ty.tySem (Ty.Prod (literal_table_vector 1) (Word 8))=>
  ((fst lr,fst rr),snd lr))
  (literal_pass2_2_equiv left left' f f EL (table_word_equiv_refl f))).
Qed.
Theorem literal_pass2_8_equiv (p q:Ty.tySem (literal_table_tree 3)) : table_tree_equiv 3 p q ->
 @literal_pass2_8 Alg.CoreFunSem p=@literal_pass2_8 Alg.CoreFunSem q.
Proof.
 destruct p as [r [left right]];destruct q as [r' [left' right']];intros [ER [EL EH]].
 set (one:=@literal_fe_one256 Alg.CoreFunSem tt).
 pose proof (literal_pass2_4_equiv right right' one one EH (table_word_equiv_refl one)) as Right.
 rewrite !literal_pass2_8_step;cbv zeta.
 refine (eq_trans (f_equal (fun rr:Ty.tySem (Ty.Prod (literal_table_vector 2) (Word 8))=>
  (fst (@literal_pass2_4 Alg.CoreFunSem
    (left,@literal_fe_multiply Alg.CoreFunSem (r,snd rr))),fst rr)) Right) _).
 set (rr:=@literal_pass2_4 Alg.CoreFunSem (right',one)).
 change ((fst (@literal_pass2_4 Alg.CoreFunSem (left,@literal_fe_multiply Alg.CoreFunSem (r,snd rr))),fst rr)=
 (fst (@literal_pass2_4 Alg.CoreFunSem (left',@literal_fe_multiply Alg.CoreFunSem (r',snd rr))),fst rr)).
 pose proof (table_multiply_equiv r r' (snd rr) (snd rr) ER (table_word_equiv_refl (snd rr))) as Factor.
 refine (eq_trans (f_equal (fun f:Ty.tySem (Word 8)=>
  (fst (@literal_pass2_4 Alg.CoreFunSem (left,f)),fst rr)) Factor) _).
 set (f:=@literal_fe_multiply Alg.CoreFunSem (r',snd rr)).
 exact (f_equal (fun lr:Ty.tySem (Ty.Prod (literal_table_vector 2) (Word 8))=>
  (fst lr,fst rr))
  (literal_pass2_4_equiv left left' f f EL (table_word_equiv_refl f))).
Qed.

Theorem literal_pass2_8_normalize (t:Ty.tySem (literal_table_tree 3)) :
 @literal_pass2_8 Alg.CoreFunSem (literal_table_normalize_tree 3 t)=@literal_pass2_8 Alg.CoreFunSem t.
Proof. apply literal_pass2_8_equiv;apply table_tree_normalize_equiv. Qed.

(** Instantiate the consumer result at the representation established by
    exec_odd_table_pass1_eight, without weakening the raw literal target. *)
Corollary table_pass1_consumed s a b :
 table_state_tree s=literal_table_normalize_tree 3 (fst (@literal_pass1_8 Alg.CoreFunSem (a,b))) ->
 @literal_pass2_8 Alg.CoreFunSem (table_state_tree s)=
 @literal_pass2_8 Alg.CoreFunSem (fst (@literal_pass1_8 Alg.CoreFunSem (a,b))).
Proof. intro FirstPass;rewrite FirstPass;apply literal_pass2_8_normalize. Qed.
