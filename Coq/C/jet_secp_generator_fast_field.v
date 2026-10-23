(** Verified evaluator-only reduction for the fixed pseudo-Mersenne modulus.
    It equals Z.modulo for every integer, including negative/unbounded values;
    the fallback retains that total behavior. No C or literal term is changed. *)
From Coq Require Import ZArith Lia.
Require Import C.jet_secp_fe_math.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_mod_word_modulus : Z := 2^256.
Definition generator_mod_mask : Z := generator_mod_word_modulus-1.
Definition generator_mod_fold x := Z.land x generator_mod_mask+feR*Z.shiftr x 256.
Definition generator_mod_clip x :=
 if x<?0 then
   if -feP<=?x then x+feP else if -2*feP<=?x then x+2*feP else x mod feP
 else if x<?feP then x else if x<?2*feP then x-feP else x mod feP.
Fixpoint generator_mod_reduce fuel x :=
 if x<?0 then generator_mod_clip x else if x<?2*feP then generator_mod_clip x else
 match fuel with Datatypes.O => x mod feP | Datatypes.S k => generator_mod_reduce k (generator_mod_fold x) end.
Definition generator_mod_fast x := generator_mod_reduce 3 x.

Lemma generator_mod_fold_matches x : generator_mod_fold x mod feP=x mod feP.
Proof.
 unfold generator_mod_fold,generator_mod_mask,generator_mod_word_modulus;
   rewrite land_ones_mod,Z.shiftr_div_pow2 by lia.
 pose proof (Z.div_mod x (2^256) ltac:(discriminate)) as Division.
 replace (x mod 2^256+feR*(x/2^256)) with (x+(-(x/2^256))*feP)
   by (unfold feP in *;nia).
 apply Z.mod_add;unfold feP,feR;lia.
Qed.
Lemma generator_mod_clip_matches x : generator_mod_clip x=x mod feP.
Proof.
 unfold generator_mod_clip;destruct (Z.ltb_spec x 0).
 - destruct (Z.leb_spec (-feP) x).
   + apply (Z.mod_unique x feP (-1) (x+feP));[left;lia|ring].
   + destruct (Z.leb_spec (-2*feP) x);[|reflexivity].
     apply (Z.mod_unique x feP (-2) (x+2*feP));[left;lia|ring].
 - destruct (Z.ltb_spec x feP);[symmetry;apply Z.mod_small;lia|].
 destruct (Z.ltb_spec x (2*feP));[|reflexivity].
 apply (Z.mod_unique x feP 1 (x-feP));[left;lia|ring].
Qed.
Lemma generator_mod_reduce_matches fuel x : generator_mod_reduce fuel x=x mod feP.
Proof.
 revert x;induction fuel as [|fuel IH];intro x;cbn [generator_mod_reduce];
   destruct (x<?0), (x<?2*feP);try apply generator_mod_clip_matches;try reflexivity.
 rewrite IH;apply generator_mod_fold_matches.
Qed.
Theorem generator_mod_fast_matches x : generator_mod_fast x=x mod feP.
Proof. apply generator_mod_reduce_matches. Qed.
