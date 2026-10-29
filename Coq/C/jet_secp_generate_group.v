(** Interpret the original signed generator recursion, without table substitution. *)
From Coq Require Import ZArith Lia.
From Coqprime.elliptic Require Import GZnZ SMain.
From Coqprime Require Import EGroup.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg Simplicity.Util.Arith.
Require Import C.jet_secp_fe_math C.jet_secp_curve_group C.jet_secp_curve_group_sign
 C.jet_secp_curve_group_power C.jet_secp_curve_group_scalar_sign C.jet_secp_signed_group_action
 C.jet_secp_lookup5_group C.jet_secp_table_pass2_group C.jet_secp_table_walk_group
 C.jet_secp_jacobian_word_group C.jet_secp_jacobian_word_transforms
 C.jet_secp_generate_literal C.jet_secp_literal_add_program C.jet_secp_double_literal
 C.jet_secp_add_literal C.jet_secp_gej_negate_literal C.jet_secp_literal_infinity C.jet_word_repr.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_group_signed_power literal_gej_double literal_gej_ge_add literal_gej_infinity
 literal_ge_negate literal_fe_one256 EGroup.gpow SMain.add SMain.opp.
Definition secp_generator_modulus n:=2^Z.of_nat (Nat.pow 2 n).
Lemma secp_generator_modulus_succ n:
 secp_generator_modulus (S n)=secp_generator_modulus n*secp_generator_modulus n.
Proof.
 unfold secp_generator_modulus;cbn [Nat.pow].
 replace (2*2^n)%nat with (2^n+2^n)%nat by lia;rewrite Nat2Z.inj_add.
 rewrite Z.pow_add_r by lia;reflexivity.
Qed.
Lemma secp_generator_word_pair n (hi lo:Ty.tySem (Word n)):
 @toZ (WordToZ (S n)) (hi,lo)=@toZ (WordToZ n) hi*secp_generator_modulus n+@toZ (WordToZ n) lo.
Proof.
 change (@toZ (WordToZ n) hi*two_power_nat (ToZ.Theory.bitSize (WordToZ n))+@toZ (WordToZ n) lo=
  @toZ (WordToZ n) hi*secp_generator_modulus n+@toZ (WordToZ n) lo).
 rewrite two_power_nat_equiv,word_bitSize;reflexivity.
Qed.
Lemma secp_generator_signed_one (p:secp_group_point):secp_group_signed_power p 1=p.
Proof. rewrite secp_group_signed_power_nonnegative by lia;apply secp_group_power_one. Qed.
Lemma secp_literal_generator_bit_group (base:Ty.tySem literal_generator_point)
 (point:secp_group_point) (bit:Ty.tySem Bit) (a:Ty.tySem literal_generator_jacobian) (m:Z):
 secp_affine_word_rep (GZnZ.one feP) base point ->
 secp_jacobian_word_rep (GZnZ.one feP) a (secp_group_signed_power point m) ->
 secp_jacobian_word_rep (GZnZ.one feP) (literal_scale_run 0 base bit a)
 (secp_group_signed_power point (2*m+@toZ BitToZ bit)).
Proof.
 destruct a as [[x y] z];intros Base Start.
 pose proof (secp_literal_double_group (GZnZ.one feP) x y z _ Start) as Doubled.
 assert (Twice:SMain.add secp_group_theory (secp_group_signed_power point m) (secp_group_signed_power point m)=
  secp_group_signed_power point (2*m)).
 { rewrite <-secp_group_signed_power_add;f_equal;ring. }
 rewrite Twice in Doubled.
 destruct bit as [u|u];destruct u.
 - change (secp_jacobian_word_rep (GZnZ.one feP) (@literal_gej_double Alg.CoreFunSem ((x,y),z))
   (secp_group_signed_power point (2*m+0))).
   rewrite Z.add_0_r;exact Doubled.
 - pose proof (secp_literal_mixed_group_pair (GZnZ.one feP)
    (@literal_gej_double Alg.CoreFunSem ((x,y),z)) base _ point
    (SMain.one_not_zero secp_group_theory) Doubled Base) as Added.
   rewrite secp_literal_mixed_value_snd in Added.
   assert (Sum:SMain.add secp_group_theory (secp_group_signed_power point (2*m)) point=
    secp_group_signed_power point (2*m+1)).
   { rewrite <-(secp_generator_signed_one point) at 2.
     symmetry;apply secp_group_signed_power_add. }
   rewrite Sum in Added;exact Added.
Qed.
Theorem secp_literal_scale_run_group n (base:Ty.tySem literal_generator_point) (point:secp_group_point)
 (word:Ty.tySem (Word n)) (a:Ty.tySem literal_generator_jacobian) (m:Z):
 secp_affine_word_rep (GZnZ.one feP) base point ->
 secp_jacobian_word_rep (GZnZ.one feP) a (secp_group_signed_power point m) ->
 secp_jacobian_word_rep (GZnZ.one feP) (literal_scale_run n base word a)
 (secp_group_signed_power point (m*secp_generator_modulus n+@toZ (WordToZ n) word)).
Proof.
 revert word a m;induction n as [|n IH];intros word a m Base Start.
 - change (secp_jacobian_word_rep (GZnZ.one feP) (literal_scale_run 0 base word a)
   (secp_group_signed_power point (m*2+@toZ BitToZ word))).
   replace (m*2) with (2*m) by ring;apply secp_literal_generator_bit_group;assumption.
 - destruct word as [hi lo];cbn [literal_scale_run fst snd].
   pose proof (IH hi a m Base Start) as First.
   pose proof (IH lo (literal_scale_run n base hi a)
    (m*secp_generator_modulus n+@toZ (WordToZ n) hi) Base First) as Last.
   rewrite secp_generator_modulus_succ,secp_generator_word_pair.
   replace (m*(secp_generator_modulus n*secp_generator_modulus n)+
     (@toZ (WordToZ n) hi*secp_generator_modulus n+@toZ (WordToZ n) lo))
   with ((m*secp_generator_modulus n+@toZ (WordToZ n) hi)*secp_generator_modulus n+@toZ (WordToZ n) lo) by ring.
   exact Last.
Qed.
Definition secp_generator_signed_word n (word:Ty.tySem (Word n)):=
 @toZ (WordToZ n) word-secp_generator_modulus n*@toZ BitToZ (@Word.leftmost Bit n Alg.CoreFunSem word).
Lemma secp_generator_signed_pair n (hi lo:Ty.tySem (Word n)):
 secp_generator_signed_word (S n) (hi,lo)=
 secp_generator_signed_word n hi*secp_generator_modulus n+@toZ (WordToZ n) lo.
Proof.
 unfold secp_generator_signed_word;rewrite secp_generator_modulus_succ,secp_generator_word_pair.
 replace (@Word.leftmost Bit (S n) Alg.CoreFunSem (hi,lo)) with
  (@Word.leftmost Bit n Alg.CoreFunSem hi) by reflexivity.
 ring.
Qed.
Lemma secp_generator_signed_zero (p:secp_group_point):secp_group_signed_power p 0=secp_group_infinity.
Proof. rewrite secp_group_signed_power_nonnegative by lia;apply secp_group_power_zero. Qed.
Local Transparent secp_group_signed_power.
Lemma secp_generator_signed_minus_one (p:secp_group_point):
 secp_group_signed_power p (-1)=SMain.opp secp_group_theory p.
Proof.
 change (SMain.opp secp_group_theory (EGroup.gpow p secp_curve_group 1)=SMain.opp secp_group_theory p).
 apply f_equal;apply secp_group_power_one.
Qed.
Local Opaque secp_group_signed_power.
Theorem secp_literal_generate_run_group n (base:Ty.tySem literal_generator_point) (point:secp_group_point)
 (word:Ty.tySem (Word n)):
 secp_affine_word_rep (GZnZ.one feP) base point ->
 secp_jacobian_word_rep (GZnZ.one feP) (literal_generate_signed_run n base word)
 (secp_group_signed_power point (secp_generator_signed_word n word)).
Proof.
 revert word;induction n as [|n IH];intros word Base.
 - destruct word as [u|u];destruct u.
   + change (secp_jacobian_word_rep (GZnZ.one feP) (@literal_gej_infinity Alg.CoreFunSem tt)
     (secp_group_signed_power point 0)).
     rewrite secp_generator_signed_zero;apply secp_literal_infinity_group.
   + change (secp_jacobian_word_rep (GZnZ.one feP)
     (@literal_ge_negate Alg.CoreFunSem base,@literal_fe_one256 Alg.CoreFunSem tt)
     (secp_group_signed_power point (-1))).
     rewrite secp_generator_signed_minus_one;apply secp_affine_negate_group;exact Base.
 - destruct word as [hi lo];cbn [literal_generate_signed_run fst snd].
   rewrite secp_generator_signed_pair.
   apply secp_literal_scale_run_group;[exact Base|apply IH;exact Base].
Qed.
Require Import C.jet_secp_generator_base_group.
Theorem secp_literal_generate_signed_group n second (word:Ty.tySem (Word n)):
 secp_jacobian_word_rep (GZnZ.one feP)
  (@literal_generate_signed n Alg.CoreFunSem (@literal_generator_base second Alg.CoreFunSem) word)
  (secp_group_signed_power
   (EGroup.gpow secp_group_generator secp_curve_group (if second then 2^128 else 1))
   (secp_generator_signed_word n word)).
Proof.
 rewrite literal_generate_signed_run_matches,literal_generator_base_fun.
 apply secp_literal_generate_run_group;apply secp_literal_generator_base_group.
Qed.
