(** Literal LibSecp256k1.fe_invert (line493), evaluated through the faithful
    word-exact EEA simulation. No mathematical inverse is assumed. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_eea_literal C.jet_secp_eea_numeric C.jet_secp_canonical_normalize
 C.jet_secp_canonical_negate C.jet_secp_negate_literal_contract C.jet_predicate_spec C.jet_toZ.
Local Open Scope Z_scope.
Local Open Scope term_scope.
Set Default Timeout 10.
Local Opaque literal_bezout literal_fe_negate canonical_field_word.

Definition literal_inverse_body W {term : Alg.Core.Algebra} (p : Ty.tySem W)
 (bez : term (Ty.Prod W W) (Ty.Sum (Ty.Prod W W) (Ty.Prod W W))) (neg : term W W) : term W W :=
 ((unit >>> Alg.scribe p) &&& iden) >>> bez >>> Alg.Core.Combinators.copair (I neg) (I H).
Definition inverse_select W (neg : Ty.Arrow W W)
 (v : Ty.tySem (Ty.Sum (Ty.Prod W W) (Ty.Prod W W))) :=
 match v with inl (_,b) => neg b | inr (_,e) => e end.
Lemma literal_inverse_body_fun W p bez neg (x : Ty.tySem W) :
 @literal_inverse_body W Alg.CoreFunSem p bez neg x=inverse_select W neg (bez (p,x)).
Proof.
 unfold literal_inverse_body,inverse_select.
 cbn -[Alg.scribe];rewrite Alg.scribe_correct.
 destruct (bez (p,x)) as [[a b] | [d e]];reflexivity.
Qed.
Definition literal_fe_invert {term : Alg.Core.Algebra} : term (Word 8) (Word 8) :=
 @literal_inverse_body (Word 8) term canonical_field_word (@literal_bezout 8 term) (@literal_fe_negate term).
Definition literal_invert_numeric x :=
 match eea_bezout_numeric (eea_run_numeric (2^256) 512
   (((1,0),canonical_field_order),((0,1),x))) with
 | inl (_,b) => (canonical_field_order-b) mod canonical_field_order
 | inr (_,e) => e
 end.
Local Opaque literal_fe_invert.
Definition literal_inverse_select := inverse_select (Word 8) (@literal_fe_negate Alg.CoreFunSem).
Local Opaque literal_inverse_select.

Lemma eea_word_modulus256 : word_modulus 8=2^256.
Proof. reflexivity. Qed.

Lemma literal_fe_invert_step (x : Ty.tySem (Word 8)) :
 @literal_fe_invert Alg.CoreFunSem x=
 literal_inverse_select (@literal_bezout 8 Alg.CoreFunSem (canonical_field_word,x)).
Proof.
 Local Transparent literal_fe_invert literal_inverse_select.
 unfold literal_fe_invert,literal_inverse_select;apply literal_inverse_body_fun.
Qed.
Local Opaque literal_fe_invert.

Theorem literal_fe_invert_numeric (x : Ty.tySem (Word 8)) :
 @toZ (WordToZ 8) (@literal_fe_invert Alg.CoreFunSem x)=literal_invert_numeric (@toZ (WordToZ 8) x).
Proof.
 Local Transparent literal_inverse_select.
 rewrite literal_fe_invert_step.
 pose proof (literal_bezout_numeric 8 canonical_field_word x) as Bezout.
 rewrite canonical_field_word_value,eea_word_modulus256 in Bezout.
 change (Nat.pow 2 (S 8)) with 512%nat in Bezout.
 unfold literal_invert_numeric;rewrite <-Bezout.
 destruct (@literal_bezout 8 Alg.CoreFunSem (canonical_field_word,x)) as [[a b] | [d e]].
 - unfold literal_inverse_select,inverse_select;cbn [eea_bezout_denote];rewrite literal_fe_negate_matches;apply canonical_fe_negate_numeric.
 - reflexivity.
Qed.

Lemma literal_invert_numeric_zero : literal_invert_numeric 0=0.
Proof. vm_compute;reflexivity. Qed.
Lemma literal_invert_numeric_one : literal_invert_numeric 1=1.
Proof. vm_compute;reflexivity. Qed.
Lemma literal_invert_numeric_two : literal_invert_numeric 2=(canonical_field_order+1)/2.
Proof. vm_compute;reflexivity. Qed.

Theorem literal_fe_invert_word (x : Ty.tySem (Word 8)) :
 @literal_fe_invert Alg.CoreFunSem x=@fromZ (WordToZ 8) (literal_invert_numeric (@toZ (WordToZ 8) x)).
Proof.
 rewrite <- (from_toZ (@literal_fe_invert Alg.CoreFunSem x)) at 1.
 rewrite literal_fe_invert_numeric;reflexivity.
Qed.

Lemma literal_fe_invert_zero :
 @literal_fe_invert Alg.CoreFunSem (@Word.zero 8 Alg.CoreFunSem tt)=@Word.zero 8 Alg.CoreFunSem tt.
Proof.
 apply (toZ_injective (WordToZ 8));rewrite literal_fe_invert_numeric,!Word.zero_correct.
 apply literal_invert_numeric_zero.
Qed.

Lemma literal_fe_invert_one :
 @literal_fe_invert Alg.CoreFunSem (@literal_eea_one 8 Alg.CoreFunSem tt)=@literal_eea_one 8 Alg.CoreFunSem tt.
Proof.
 apply (toZ_injective (WordToZ 8));rewrite literal_fe_invert_numeric,!literal_eea_one_numeric.
 apply literal_invert_numeric_one.
Qed.

Lemma literal_fe_invert_two :
 @literal_fe_invert Alg.CoreFunSem (@fromZ (WordToZ 8) 2)=
 @fromZ (WordToZ 8) ((canonical_field_order+1)/2).
Proof.
 rewrite literal_fe_invert_word,to_fromZ.
 change (two_power_nat (ToZ.Theory.bitSize (WordToZ 8))) with (2^256).
 rewrite Z.mod_small by (split;[lia|change (2^256) with
   115792089237316195423570985008687907853269984665640564039457584007913129639936;lia]).
 rewrite literal_invert_numeric_two;reflexivity.
Qed.
