(** Representation congruence for the actual table consumers' literal field
    operations. It justifies consuming C's normalized field encodings without
    changing the fixed raw-ratio table program or restricting its inputs. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_negate_literal_contract
 C.jet_secp_multiply_literal_spec C.jet_secp_square_execution C.jet_secp_rescale_literal
 C.jet_secp_canonical_normalize C.jet_secp_scalar_table_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_multiply literal_fe_square literal_fe_cube literal_gej_zinv canonical_fe_normalize.

Definition table_word_equiv (x y:Ty.tySem (Word 8)) :=
 @toZ (WordToZ 8) x mod feP=@toZ (WordToZ 8) y mod feP.
Lemma table_word_equiv_refl x : table_word_equiv x x.
Proof. reflexivity. Qed.
Lemma table_word_normalize_equiv x : table_word_equiv (@canonical_fe_normalize Alg.CoreFunSem x) x.
Proof.
 unfold table_word_equiv;rewrite canonical_fe_normalize_numeric,canonical_field_order_matches_limb_model.
 rewrite Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.
Lemma table_multiply_equiv x x' y y' : table_word_equiv x x' -> table_word_equiv y y' ->
 @literal_fe_multiply Alg.CoreFunSem (x,y)=@literal_fe_multiply Alg.CoreFunSem (x',y').
Proof.
 intros HX HY;apply (toZ_injective (WordToZ 8));rewrite !literal_multiply_numeric.
 rewrite (Z.mul_mod (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y)),
  (Z.mul_mod (@toZ (WordToZ 8) x') (@toZ (WordToZ 8) y')) by (unfold feP,feR;lia).
 unfold table_word_equiv in HX,HY;rewrite HX,HY;reflexivity.
Qed.
Lemma table_square_equiv x y : table_word_equiv x y ->
 @literal_fe_square Alg.CoreFunSem x=@literal_fe_square Alg.CoreFunSem y.
Proof. intro E;rewrite !literal_square_step;apply table_multiply_equiv;exact E. Qed.
Lemma table_cube_step x : @literal_fe_cube Alg.CoreFunSem x=
 @literal_fe_multiply Alg.CoreFunSem (x,@literal_fe_square Alg.CoreFunSem x).
Proof. reflexivity. Qed.
Lemma table_cube_equiv x y : table_word_equiv x y ->
 @literal_fe_cube Alg.CoreFunSem x=@literal_fe_cube Alg.CoreFunSem y.
Proof.
 intro E;rewrite !table_cube_step;apply table_multiply_equiv;[exact E|].
 rewrite (table_square_equiv x y E);reflexivity.
Qed.
Lemma table_zinv_step (p:Ty.tySem literal_table_ge) s :
 @literal_gej_zinv Alg.CoreFunSem (p,s)=
 (@literal_fe_multiply Alg.CoreFunSem (fst p,@literal_fe_square Alg.CoreFunSem s),
  @literal_fe_multiply Alg.CoreFunSem (snd p,@literal_fe_cube Alg.CoreFunSem s)).
Proof. destruct p as [x y];reflexivity. Qed.
Lemma table_zinv_equiv (p q:Ty.tySem literal_table_ge) s t :
 table_word_equiv (fst p) (fst q) -> table_word_equiv (snd p) (snd q) -> table_word_equiv s t ->
 @literal_gej_zinv Alg.CoreFunSem (p,s)=@literal_gej_zinv Alg.CoreFunSem (q,t).
Proof.
 intros HX HY HS;rewrite !table_zinv_step;apply f_equal2.
 - apply table_multiply_equiv;[exact HX|rewrite (table_square_equiv s t HS);reflexivity].
 - apply table_multiply_equiv;[exact HY|rewrite (table_cube_equiv s t HS);reflexivity].
Qed.
