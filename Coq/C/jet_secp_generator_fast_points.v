(** Verified evaluator functions; the original numeric/literal programs are
    unchanged. Every equality holds for all integer inputs. *)
From Coq Require Import ZArith List.
Require Import C.jet_secp_generator_point_numeric C.jet_secp_generate_numeric
 C.jet_secp_fe_math C.jet_secp_generator_normalization_check C.jet_secp_generator_bits.
Require Import C.jet_secp_generator_fast_field.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque generator_mod_fast.

Definition generator_halve_fast x :=
 if Z.eqb (x mod 2) 0 then x/2 else generator_mod_fast ((feP+1)/2+x/2).
Definition generator_double_body_fast x y z :=
 let s:=generator_mod_fast (y*y) in
 let l:=generator_halve_fast (generator_mod_fast (3*generator_mod_fast (x*x))) in
 let t:=generator_mod_fast (feP-generator_mod_fast (s*x)) in
 let rx:=generator_mod_fast (generator_mod_fast (2*t)+generator_mod_fast (l*l)) in
 ((rx,generator_mod_fast (feP-generator_mod_fast
    (generator_mod_fast (l*generator_mod_fast (rx+t))+generator_mod_fast (s*s)))),
  generator_mod_fast (y*z)).
Definition generator_double_fast x y z :=
 if orb (Z.eqb z 0) (Z.eqb z feP) then ((0,0),0) else generator_double_body_fast x y z.
Lemma generator_halve_fast_matches x : generator_halve_fast x=literal_halve_numeric x.
Proof. unfold generator_halve_fast,literal_halve_numeric;rewrite generator_mod_fast_matches;reflexivity. Qed.
Lemma generator_double_body_fast_matches x y z :
 generator_double_body_fast x y z=literal_double_body_numeric x y z.
Proof.
 unfold generator_double_body_fast,literal_double_body_numeric.
 repeat first [rewrite generator_halve_fast_matches | rewrite generator_mod_fast_matches];reflexivity.
Qed.
Lemma generator_double_fast_matches x y z : generator_double_fast x y z=literal_double_numeric x y z.
Proof.
 unfold generator_double_fast,literal_double_numeric;
 destruct (orb (Z.eqb z 0) (Z.eqb z feP));[reflexivity|apply generator_double_body_fast_matches].
Qed.

Definition generator_mixed_values_fast x y z bx byword :=
 let u:=generator_mod_fast (x*generator_mod_fast (1*1)) in
 let v:=generator_mod_fast (y*generator_mod_fast (1*1*1)) in
 let h:=generator_mod_fast (u+generator_mod_fast
   (generator_mod_fast (feP-bx)*generator_mod_fast (z*z))) in
 let i:=generator_mod_fast (v+generator_mod_fast
   (generator_mod_fast (feP-byword)*generator_mod_fast (z*z*z))) in (u,v,h,i).
Definition generator_mixed_nonzero_fast u v h i z :=
 let t:=generator_mod_fast (generator_mod_fast (h*h)*u) in
 let g:=generator_mod_fast (h*h*h) in
 let rx:=generator_mod_fast (generator_mod_fast (g+generator_mod_fast (-2*t))+generator_mod_fast (i*i)) in
 ((rx,generator_mod_fast (generator_mod_fast (g*v)+generator_mod_fast
    (i*generator_mod_fast (rx+generator_mod_fast (feP-t))))),
  generator_mod_fast (generator_mod_fast (h*z)*generator_mod_fast (feP-1))).
Definition generator_mixed_fast x y z bx byword :=
 if literal_zero_numeric z then ((generator_mod_fast bx,generator_mod_fast byword),1) else
 let '(u,v,h,i):=generator_mixed_values_fast x y z bx byword in
 if literal_zero_numeric h then
   if literal_zero_numeric i then generator_double_fast x y z else ((0,0),0)
 else generator_mixed_nonzero_fast u v h i z.
Lemma generator_mixed_values_fast_matches x y z bx byword :
 generator_mixed_values_fast x y z bx byword=literal_mixed_values x y z bx byword.
Proof.
 unfold generator_mixed_values_fast,literal_mixed_values;repeat rewrite generator_mod_fast_matches;reflexivity.
Qed.
Lemma generator_mixed_nonzero_fast_matches u v h i z :
 generator_mixed_nonzero_fast u v h i z=literal_mixed_nonzero_numeric u v h i z.
Proof.
 unfold generator_mixed_nonzero_fast,literal_mixed_nonzero_numeric;repeat rewrite generator_mod_fast_matches;reflexivity.
Qed.
Lemma generator_mixed_fast_matches x y z bx byword :
 generator_mixed_fast x y z bx byword=literal_mixed_numeric x y z bx byword.
Proof.
 unfold generator_mixed_fast,literal_mixed_numeric.
 rewrite generator_mixed_values_fast_matches.
 destruct (literal_zero_numeric z).
 - rewrite !generator_mod_fast_matches;reflexivity.
 - destruct (literal_mixed_values x y z bx byword) as [[[u v] h] i].
   destruct (literal_zero_numeric h), (literal_zero_numeric i);
     first [apply generator_double_fast_matches|apply generator_mixed_nonzero_fast_matches|reflexivity].
Qed.

Definition generator_normalization_fast x y z tx ty :=
 andb (0<=?z) (andb (z<?generator_mod_word_modulus) (andb (negb (Z.eqb (generator_mod_fast z) 0))
 (andb (0<=?tx) (andb (tx<?feP) (andb (0<=?ty) (andb (ty<?feP)
 (andb (Z.eqb (generator_mod_fast (tx*z*z)) (generator_mod_fast x))
       (Z.eqb (generator_mod_fast (ty*z*z*z)) (generator_mod_fast y))))))))).
Lemma generator_normalization_fast_matches x y z tx ty :
 generator_normalization_fast x y z tx ty=generator_normalization_check x y z tx ty.
Proof.
 unfold generator_normalization_fast,generator_normalization_check;repeat rewrite generator_mod_fast_matches;reflexivity.
Qed.

Definition generator_double_fast_eval (a : Z*Z*Z) := let '(x,y,z):=a in generator_double_fast x y z.
Definition generator_mixed_fast_eval (a : Z*Z*Z) (b : Z*Z) :=
 let '(x,y,z):=a in let '(bx,byword):=b in generator_mixed_fast x y z bx byword.
Lemma generator_double_fast_eval_matches a : generator_double_fast_eval a=literal_double_eval a.
Proof. destruct a as [[x y] z];apply generator_double_fast_matches. Qed.
Lemma generator_mixed_fast_eval_matches a b : generator_mixed_fast_eval a b=literal_mixed_eval a b.
Proof. destruct a as [[x y] z];destruct b as [bx byword];apply generator_mixed_fast_matches. Qed.

Definition generator_bit_fast base a (bit : bool) :=
 let doubled:=generator_double_fast_eval a in if bit then generator_mixed_fast_eval doubled base else doubled.
Lemma generator_bit_fast_matches base a bit : generator_bit_fast base a bit=literal_generate_bit base a bit.
Proof. unfold generator_bit_fast,literal_generate_bit;rewrite generator_double_fast_eval_matches;
 destruct bit;[apply generator_mixed_fast_eval_matches|reflexivity]. Qed.

Lemma generator_fold_fast_matches base bits a :
 fold_left (generator_bit_fast base) bits a=fold_left (literal_generate_bit base) bits a.
Proof.
 revert a;induction bits as [|bit bits IH];intro a;[reflexivity|].
 cbn [fold_left];rewrite generator_bit_fast_matches,IH;reflexivity.
Qed.
Definition generator_bits_fast base (bits : list bool) :=
 match bits with
 | nil => ((0,0),0)
 | cons sign tail => fold_left (generator_bit_fast base) tail
     (if sign then ((generator_mod_fast (fst base),generator_mod_fast (feP-snd base)),1) else ((0,0),0))
 end.
Lemma generator_bits_fast_matches base bits : generator_bits_fast base bits=literal_generate_bits base bits.
Proof.
 destruct bits as [|sign tail];[reflexivity|].
 unfold generator_bits_fast,literal_generate_bits;rewrite generator_fold_fast_matches.
 destruct sign;[rewrite !generator_mod_fast_matches|];reflexivity.
Qed.
