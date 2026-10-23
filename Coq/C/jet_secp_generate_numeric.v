(** Fast structural evaluation of the literal signed generator via the checked
    numeric point operations. The raw input bits and exact affine output stay
    unchanged; in particular the negative-sign recursion is evaluated. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_generate_literal
 C.jet_secp_generator_point_numeric C.jet_secp_double_literal C.jet_secp_add_literal
 C.jet_secp_literal_infinity C.jet_secp_literal_add_program C.jet_secp_literal_add_numeric
 C.jet_secp_gej_negate_literal C.jet_secp_canonical_normalize
 C.jet_secp_negate_literal_contract C.jet_secp_curve_literal C.jet_secp_gej_norm_literal
 C.jet_secp_eea_fast C.jet_predicate_spec C.jet_secp_invert_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_gej_double literal_gej_ge_add literal_gej_infinity
 literal_ge_negate literal_fe_one256 literal_gej_norm literal_fe_negate canonical_fe_normalize.

Definition literal_affine_denote (a : Ty.tySem literal_generator_point) :=
 (@toZ (WordToZ 8) (fst a),@toZ (WordToZ 8) (snd a)).
Definition literal_double_eval (a : Z*Z*Z) :=
 let '(x,y,z):=a in literal_double_numeric x y z.
Definition literal_mixed_eval (a : Z*Z*Z) (b : Z*Z) :=
 let '(x,y,z):=a in let '(bx,byword):=b in literal_mixed_numeric x y z bx byword.
Definition literal_norm_eval (a : Z*Z*Z) :=
 let '(x,y,z):=a in literal_gej_norm_numeric_value x y z.

Fixpoint literal_scale_numeric n (base : Z*Z) : Ty.tySem (Word n) -> (Z*Z*Z) -> (Z*Z*Z) :=
 match n as k return Ty.tySem (Word k) -> (Z*Z*Z) -> (Z*Z*Z) with
 | Datatypes.O => fun bit a =>
     let doubled:=literal_double_eval a in
     match bit with inl _ => doubled | inr _ => literal_mixed_eval doubled base end
 | Datatypes.S k => fun word a =>
     literal_scale_numeric k base (snd word) (literal_scale_numeric k base (fst word) a)
 end.
Fixpoint literal_generate_signed_numeric n (base : Z*Z) : Ty.tySem (Word n) -> (Z*Z*Z) :=
 match n as k return Ty.tySem (Word k) -> (Z*Z*Z) with
 | Datatypes.O => fun bit =>
     match bit with
     | inl _ => ((0,0),0)
     | inr _ => ((fst base mod feP,(feP-snd base) mod feP),1)
     end
 | Datatypes.S k => fun word =>
     literal_scale_numeric k base (snd word) (literal_generate_signed_numeric k base (fst word))
 end.
Definition literal_generate_small_numeric second word :=
 literal_norm_eval (literal_generate_signed_numeric 4
   (literal_affine_denote (literal_generator_base_word second)) word).

Lemma literal_double_eval_matches (a : Ty.tySem literal_generator_jacobian) :
 literal_jacobian_denote (@literal_gej_double Alg.CoreFunSem a)=
 literal_double_eval (literal_jacobian_denote a).
Proof. destruct a as [[x y] z];apply literal_double_numeric_matches. Qed.
Lemma literal_mixed_eval_matches (a : Ty.tySem literal_generator_jacobian)
 (b : Ty.tySem literal_generator_point) :
 literal_jacobian_denote (@literal_gej_ge_add Alg.CoreFunSem (a,b))=
 literal_mixed_eval (literal_jacobian_denote a) (literal_affine_denote b).
Proof. destruct a as [[x y] z];destruct b as [bx byword];apply literal_mixed_numeric_matches. Qed.
Lemma literal_norm_eval_matches (a : Ty.tySem literal_generator_jacobian) :
 literal_affine_denote (@literal_gej_norm Alg.CoreFunSem a)=
 literal_norm_eval (literal_jacobian_denote a).
Proof.
 destruct a as [[x y] z];pose proof (literal_gej_norm_numeric x y z) as Values.
 change ((@toZ (WordToZ 8) (fst (@literal_gej_norm Alg.CoreFunSem ((x,y),z))),
   @toZ (WordToZ 8) (snd (@literal_gej_norm Alg.CoreFunSem ((x,y),z))))=
   literal_gej_norm_numeric_value (@toZ (WordToZ 8) x) (@toZ (WordToZ 8) y) (@toZ (WordToZ 8) z)).
 destruct (@literal_gej_norm Alg.CoreFunSem ((x,y),z)) as [rx ry];exact Values.
Qed.

Lemma literal_scale_numeric_matches n (base : Ty.tySem literal_generator_point)
 (word : Ty.tySem (Word n)) (a : Ty.tySem literal_generator_jacobian) :
 literal_jacobian_denote (literal_scale_run n base word a)=
 literal_scale_numeric n (literal_affine_denote base) word (literal_jacobian_denote a).
Proof.
 revert word a;induction n as [|n IH];intros word a.
 - destruct word as [u | u];destruct u;cbn [literal_scale_run literal_scale_numeric].
   + apply literal_double_eval_matches.
   + rewrite literal_mixed_eval_matches,literal_double_eval_matches;reflexivity.
 - destruct word as [hi lo];cbn [literal_scale_run literal_scale_numeric fst snd].
   rewrite !IH;reflexivity.
Qed.

Lemma literal_generate_signed_numeric_matches n (base : Ty.tySem literal_generator_point)
 (word : Ty.tySem (Word n)) :
 literal_jacobian_denote (literal_generate_signed_run n base word)=
 literal_generate_signed_numeric n (literal_affine_denote base) word.
Proof.
 revert word;induction n as [|n IH];intro word.
 - destruct word as [u | u];destruct u;cbn [literal_generate_signed_run literal_generate_signed_numeric].
   + Local Transparent literal_gej_infinity.
     unfold literal_jacobian_denote,literal_gej_infinity,literal_fe_zero256;
       cbn [fst snd];rewrite Word.zero_correct;reflexivity.
   + Local Transparent literal_ge_negate.
     destruct base as [bx byword].
     unfold literal_jacobian_denote,literal_affine_denote,literal_ge_negate;cbn [fst snd].
     change ((@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem bx),
       @toZ (WordToZ 8) (@literal_fe_negate Alg.CoreFunSem byword),
       @toZ (WordToZ 8) (@literal_fe_one256 Alg.CoreFunSem tt))=
       (@toZ (WordToZ 8) bx mod feP,(feP-@toZ (WordToZ 8) byword) mod feP,1)).
     rewrite canonical_fe_normalize_numeric,literal_curve_negate_numeric,
       literal_fe_one256_value,canonical_field_order_matches_limb_model;reflexivity.
 - destruct word as [hi lo];cbn [literal_generate_signed_run literal_generate_signed_numeric fst snd].
   rewrite literal_scale_numeric_matches,IH;reflexivity.
Qed.

Theorem literal_generate_small_numeric_matches second (word : Ty.tySem (Word 4)) :
 literal_affine_denote (@literal_generate_small second Alg.CoreFunSem word)=
 literal_generate_small_numeric second word.
Proof.
 rewrite literal_generate_small_run,literal_norm_eval_matches,literal_generate_signed_numeric_matches;reflexivity.
Qed.

Theorem literal_generate_small_word second (word : Ty.tySem (Word 4)) :
 @literal_generate_small second Alg.CoreFunSem word=
 (@fromZ (WordToZ 8) (fst (literal_generate_small_numeric second word)),
  @fromZ (WordToZ 8) (snd (literal_generate_small_numeric second word))).
Proof.
 pose proof (literal_generate_small_numeric_matches second word) as Values.
 unfold literal_affine_denote in Values.
 destruct (@literal_generate_small second Alg.CoreFunSem word) as [rx ry].
 destruct (literal_generate_small_numeric second word) as [nx ny].
 injection Values as HX HY;cbn [fst snd] in *.
 rewrite <-HX,<-HY,!from_toZ;reflexivity.
Qed.

Definition literal_norm_fast (a : Z*Z*Z) :=
 let '(x,y,z):=a in let iz:=literal_invert_fast z in
 ((x*iz*iz) mod feP,(y*iz*iz*iz) mod feP).
Definition literal_generate_small_fast second word :=
 literal_norm_fast (literal_generate_signed_numeric 4
   (literal_affine_denote (literal_generator_base_word second)) word).

Lemma literal_generated_z_nonnegative n base word :
 0<=snd (literal_generate_signed_numeric n (literal_affine_denote base) word).
Proof.
 rewrite <-literal_generate_signed_numeric_matches.
 unfold literal_jacobian_denote;cbn [snd];apply (proj1 (word_value_bounds 8 _)).
Qed.

Lemma literal_generate_small_fast_matches second word :
 literal_generate_small_fast second word=literal_generate_small_numeric second word.
Proof.
 pose proof (literal_generated_z_nonnegative 4 (literal_generator_base_word second) word) as ZRange.
 unfold literal_generate_small_fast,literal_generate_small_numeric.
 destruct (literal_generate_signed_numeric 4 (literal_affine_denote (literal_generator_base_word second)) word)
   as [[x y] z];cbn [snd] in ZRange.
 unfold literal_norm_fast,literal_norm_eval,literal_gej_norm_numeric_value.
 rewrite literal_invert_fast_matches by exact ZRange;reflexivity.
Qed.

Theorem literal_generate_small_fast_word second (word : Ty.tySem (Word 4)) :
 @literal_generate_small second Alg.CoreFunSem word=
 (@fromZ (WordToZ 8) (fst (literal_generate_small_fast second word)),
  @fromZ (WordToZ 8) (snd (literal_generate_small_fast second word))).
Proof. rewrite literal_generate_small_fast_matches;apply literal_generate_small_word. Qed.
