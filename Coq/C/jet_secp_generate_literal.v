(** Exact signed generator and scaleConstant trees at every word width.
    Constants and routing follow LibSecp256k1.hs:446--466,795--812. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_secp_double_literal C.jet_secp_add_literal
 C.jet_secp_gej_negate_literal C.jet_secp_gej_negate_parametric
 C.jet_secp_literal_infinity C.jet_secp_literal_gej_predicate
 C.jet_secp_gej_norm_literal C.jet_secp_literal_add_program.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_generator_point := Ty.Prod (Word 8) (Word 8).
Definition literal_generator_jacobian := Ty.Prod literal_generator_point (Word 8).
Definition literal_generator_base_word (second : bool) : Ty.tySem literal_generator_point :=
 if second then
  (@fromZ (WordToZ 8) 0x8f68b9d2f63b5f339239c1ad981f162ee88c5678723ea3351b7b444c9ec4c0da,
   @fromZ (WordToZ 8) 0x662a9f2dba063986de1d90c2b6be215dbbea2cfe95510bfdf23cbf79501fff82)
 else
  (@fromZ (WordToZ 8) 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798,
   @fromZ (WordToZ 8) 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8).
Definition literal_generator_base second {term : Alg.Core.Algebra} :
 term Ty.Unit literal_generator_point := Alg.scribe (literal_generator_base_word second).

Fixpoint literal_scale_constant n {term : Alg.Core.Algebra}
 (base : term Ty.Unit literal_generator_point) :
 term (Ty.Prod (Word n) literal_generator_jacobian) literal_generator_jacobian :=
 match n as k return term (Ty.Prod (Word k) literal_generator_jacobian) literal_generator_jacobian with
 | Datatypes.O => Bit.cond
     ((@literal_gej_double term &&& (unit >>> base)) >>> @literal_gej_ge_add term)
     (@literal_gej_double term)
 | Datatypes.S k =>
     let rec := @literal_scale_constant k term base in
     (O (I H) &&& ((O (O H) &&& I H) >>> rec)) >>> rec
 end.
Fixpoint literal_generate_signed n {term : Alg.Core.Algebra}
 (base : term Ty.Unit literal_generator_point) : term (Word n) literal_generator_jacobian :=
 match n as k return term (Word k) literal_generator_jacobian with
 | Datatypes.O => Alg.Core.Combinators.copair (@literal_gej_infinity term)
     ((base >>> @literal_ge_negate term) &&& @literal_fe_one256 term)
 | Datatypes.S k =>
     (I H &&& O (@literal_generate_signed k term base)) >>> @literal_scale_constant k term base
 end.
Definition literal_generate_small second {term : Alg.Core.Algebra} :
 term (Word 4) literal_generator_point :=
 @literal_generate_signed 4 term (@literal_generator_base second term) >>> @literal_gej_norm term.

Local Opaque literal_gej_double literal_gej_ge_add literal_gej_infinity literal_ge_negate literal_fe_one256.
Fixpoint literal_scale_run n (base : Ty.tySem literal_generator_point)
 : Ty.tySem (Word n) -> Ty.tySem literal_generator_jacobian -> Ty.tySem literal_generator_jacobian :=
 match n as k return Ty.tySem (Word k) -> Ty.tySem literal_generator_jacobian -> Ty.tySem literal_generator_jacobian with
 | Datatypes.O => fun bit a =>
     let doubled:=@literal_gej_double Alg.CoreFunSem a in
     match bit with
     | inl _ => doubled
     | inr _ => @literal_gej_ge_add Alg.CoreFunSem (doubled,base)
     end
 | Datatypes.S k => fun word a =>
     literal_scale_run k base (snd word) (literal_scale_run k base (fst word) a)
 end.
Fixpoint literal_generate_signed_run n (base : Ty.tySem literal_generator_point)
 : Ty.tySem (Word n) -> Ty.tySem literal_generator_jacobian :=
 match n as k return Ty.tySem (Word k) -> Ty.tySem literal_generator_jacobian with
 | Datatypes.O => fun bit =>
     match bit with
     | inl _ => @literal_gej_infinity Alg.CoreFunSem tt
     | inr _ => (@literal_ge_negate Alg.CoreFunSem base,@literal_fe_one256 Alg.CoreFunSem tt)
     end
 | Datatypes.S k => fun word =>
     literal_scale_run k base (snd word) (literal_generate_signed_run k base (fst word))
 end.

Lemma literal_generator_base_fun second :
 @literal_generator_base second Alg.CoreFunSem tt=literal_generator_base_word second.
Proof. unfold literal_generator_base;apply Alg.scribe_correct. Qed.

Lemma literal_scale_constant_run n base word a :
 @literal_scale_constant n Alg.CoreFunSem base (word,a)=literal_scale_run n (base tt) word a.
Proof.
 revert word a;induction n as [|n IH];intros word a.
 - destruct word as [u | u];destruct u;reflexivity.
 - destruct word as [hi lo].
   change (@literal_scale_constant n Alg.CoreFunSem base
     (lo,@literal_scale_constant n Alg.CoreFunSem base (hi,a))=
     literal_scale_run n (base tt) lo (literal_scale_run n (base tt) hi a)).
   rewrite !IH;reflexivity.
Qed.

Lemma literal_generate_signed_run_matches n base word :
 @literal_generate_signed n Alg.CoreFunSem base word=literal_generate_signed_run n (base tt) word.
Proof.
 revert word;induction n as [|n IH];intro word.
 - destruct word as [u | u];destruct u;reflexivity.
 - destruct word as [hi lo].
   change (@literal_scale_constant n Alg.CoreFunSem base
     (lo,@literal_generate_signed n Alg.CoreFunSem base hi)=
     literal_scale_run n (base tt) lo (literal_generate_signed_run n (base tt) hi)).
   rewrite literal_scale_constant_run,IH;reflexivity.
Qed.

Lemma literal_generate_small_run second word :
 @literal_generate_small second Alg.CoreFunSem word=
 @literal_gej_norm Alg.CoreFunSem
   (literal_generate_signed_run 4 (literal_generator_base_word second) word).
Proof.
 change (@literal_gej_norm Alg.CoreFunSem
   (@literal_generate_signed 4 Alg.CoreFunSem (@literal_generator_base second Alg.CoreFunSem) word)=
   @literal_gej_norm Alg.CoreFunSem
     (literal_generate_signed_run 4 (literal_generator_base_word second) word)).
 rewrite literal_generate_signed_run_matches,literal_generator_base_fun;reflexivity.
Qed.

Lemma literal_generator_base_parametric second : Alg.Core.Parametric (@literal_generator_base second).
Proof. intros t1 t2 R;unfold literal_generator_base;apply Alg.scribe_Parametric. Qed.

Lemma literal_scale_constant_parametric n
 (base : forall term : Alg.Core.Algebra, term Ty.Unit literal_generator_point) :
 Alg.Core.Parametric base ->
 Alg.Core.Parametric (fun term => @literal_scale_constant n term (base term)).
Proof.
 intro HB;induction n as [|n IH];intros t1 t2 R;cbn [literal_scale_constant].
 - apply Bit.cond_Parametric.
   + apply Alg.comp_Parametric.
     { apply Alg.pair_Parametric.
       { apply literal_gej_double_parametric. }
       { apply Alg.comp_Parametric;[apply Alg.unit_Parametric|apply HB]. } }
     { apply literal_gej_ge_add_parametric. }
   + apply literal_gej_double_parametric.
 - apply Alg.comp_Parametric.
   { apply Alg.pair_Parametric.
     { apply Alg.take_Parametric;apply Alg.drop_Parametric;apply Alg.iden_Parametric. }
     { apply Alg.comp_Parametric.
       { apply Alg.pair_Parametric;
          [apply Alg.take_Parametric;apply Alg.take_Parametric;apply Alg.iden_Parametric|
           apply Alg.drop_Parametric;apply Alg.iden_Parametric]. }
       { apply IH. } } }
   { apply IH. }
Qed.

Lemma literal_generate_signed_parametric n
 (base : forall term : Alg.Core.Algebra, term Ty.Unit literal_generator_point) :
 Alg.Core.Parametric base ->
 Alg.Core.Parametric (fun term => @literal_generate_signed n term (base term)).
Proof.
 intro HB;induction n as [|n IH];intros t1 t2 R;cbn [literal_generate_signed].
 - apply Alg.copair_Parametric.
   { apply literal_gej_infinity_parametric. }
   { apply Alg.pair_Parametric.
     { apply Alg.comp_Parametric;[apply HB|apply literal_ge_negate_parametric]. }
     { apply literal_fe_one256_parametric. } }
 - apply Alg.comp_Parametric.
   { apply Alg.pair_Parametric.
     { apply Alg.drop_Parametric;apply Alg.iden_Parametric. }
     { apply Alg.take_Parametric;apply IH. } }
   { apply literal_scale_constant_parametric;exact HB. }
Qed.

Lemma literal_generate_small_parametric second : Alg.Core.Parametric (@literal_generate_small second).
Proof.
 intros t1 t2 R;unfold literal_generate_small;apply Alg.comp_Parametric;
   [apply literal_generate_signed_parametric;apply literal_generator_base_parametric|
    apply literal_gej_norm_parametric].
Qed.
