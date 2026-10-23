(** A word-exact numeric simulation of the literal EEA. Coefficients wrap
    modulo the word modulus exactly as the low full-multiplier outputs do. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_secp_eea_literal C.jet_predicate_spec C.jet_order_spec
 C.jet_literal_division_add C.jet_division_result_spec C.jet_division_value C.jet_test_value_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eea_row_denote n (r : Ty.tySem (literal_eea_row n)) : (Z*Z)*Z :=
 ((@toZ (WordToZ n) (fst (fst r)),@toZ (WordToZ n) (snd (fst r))),@toZ (WordToZ n) (snd r)).
Definition eea_state_denote n (s : Ty.tySem (literal_eea_state n)) :=
 (eea_row_denote n (fst s),eea_row_denote n (snd s)).
Definition eea_row_step_numeric modulus (r t : (Z*Z)*Z) :=
 let '((a,b),c):=r in let '((d,e),f):=t in
 let q:=division_numeric Datatypes.false c f in
 (((a+q*d) mod modulus,(b+q*e) mod modulus),division_numeric Datatypes.true c f).
Definition eea_step_numeric modulus (s : ((Z*Z)*Z)*((Z*Z)*Z)) :=
 let '(r,t):=s in if snd t <? snd r then (eea_row_step_numeric modulus r t,t)
 else (r,eea_row_step_numeric modulus t r).
Fixpoint eea_run_numeric modulus count (s : ((Z*Z)*Z)*((Z*Z)*Z)) :=
 match count with Datatypes.O => s | Datatypes.S k => eea_run_numeric modulus k (eea_step_numeric modulus s) end.

Lemma eea_low_word_numeric n (p : Ty.tySem (Word (S n))) :
 @toZ (WordToZ n) (snd p)=@toZ (WordToZ (S n)) p mod word_modulus n.
Proof.
 destruct p as [hi lo].
 change (@toZ (WordToZ n) lo=
   (@toZ (WordToZ n) hi*word_modulus n+@toZ (WordToZ n) lo) mod word_modulus n).
 rewrite Z.add_comm,Z.mod_add by (pose proof (word_modulus_positive n);lia).
 symmetry;apply Z.mod_small;apply word_value_bounds.
Qed.

Lemma eea_multiply_low_numeric n (q d a : Ty.tySem (Word n)) :
 @toZ (WordToZ n) (snd (@Word.fullMultiplier n Alg.CoreFunSem ((q,d),(a,@Word.zero n Alg.CoreFunSem tt))))=
 (@toZ (WordToZ n) a+@toZ (WordToZ n) q*@toZ (WordToZ n) d) mod word_modulus n.
Proof.
 rewrite eea_low_word_numeric,Word.fullMultiplier_correct,Word.zero_correct.
 f_equal;ring.
Qed.

Theorem literal_eea_row_step_numeric n r t :
 eea_row_denote n (@literal_eea_row_step n Alg.CoreFunSem (r,t))=
 eea_row_step_numeric (word_modulus n) (eea_row_denote n r) (eea_row_denote n t).
Proof.
 destruct r as [[a b] c],t as [[d e] f];rewrite literal_eea_row_step_expansion.
 pose proof (div_mod_word_numeric n c f) as Div.
 rewrite <-literal_div_mod_matches in Div.
 change (@toZ (WordToZ n) (fst (@literal_div_mod_word_spec n Alg.CoreFunSem (c,f)))=
   division_numeric Datatypes.false (@toZ (WordToZ n) c) (@toZ (WordToZ n) f) /\
   @toZ (WordToZ n) (snd (@literal_div_mod_word_spec n Alg.CoreFunSem (c,f)))=
   division_numeric Datatypes.true (@toZ (WordToZ n) c) (@toZ (WordToZ n) f)) in Div.
 destruct (@literal_div_mod_word_spec n Alg.CoreFunSem (c,f)) as [q rem] eqn:QR.
 cbn [fst snd] in Div;destruct Div as [Quot Rem].
 unfold eea_row_denote,eea_row_step_numeric;cbn [fst snd].
 match goal with
 | |- context [match ?qr with (_,_) => _ end] =>
   change (qr=(q,rem)) in QR;rewrite QR
 end;cbn [fst snd].
 change (((@toZ (WordToZ n) (snd (@Word.fullMultiplier n Alg.CoreFunSem ((q,d),(a,@Word.zero n Alg.CoreFunSem tt)))),
   @toZ (WordToZ n) (snd (@Word.fullMultiplier n Alg.CoreFunSem ((q,e),(b,@Word.zero n Alg.CoreFunSem tt))))),
   @toZ (WordToZ n) rem)=
   (((@toZ (WordToZ n) a+division_numeric Datatypes.false (@toZ (WordToZ n) c) (@toZ (WordToZ n) f)*@toZ (WordToZ n) d) mod word_modulus n,
     (@toZ (WordToZ n) b+division_numeric Datatypes.false (@toZ (WordToZ n) c) (@toZ (WordToZ n) f)*@toZ (WordToZ n) e) mod word_modulus n),
     division_numeric Datatypes.true (@toZ (WordToZ n) c) (@toZ (WordToZ n) f))).
 rewrite !eea_multiply_low_numeric,Quot,Rem;reflexivity.
Qed.

Theorem literal_eea_step_numeric n s :
 eea_state_denote n (@literal_eea_step n Alg.CoreFunSem s)=
 eea_step_numeric (word_modulus n) (eea_state_denote n s).
Proof.
 destruct s as [[[a b] c] [[d e] f]].
 rewrite literal_eea_step_expansion.
 pose proof (lt_word_spec_numeric n f c) as Compare.
 unfold eea_step_numeric,eea_state_denote;cbn [fst snd].
 change (snd (eea_row_denote n ((d,e),f))) with (@toZ (WordToZ n) f).
 change (snd (eea_row_denote n ((a,b),c))) with (@toZ (WordToZ n) c).
 match goal with
 | |- context [match ?guard with inl _ => _ | inr _ => _ end] =>
   change (Bit.toBool guard=(@toZ (WordToZ n) f <? @toZ (WordToZ n) c)) in Compare;
   destruct guard as [[] | []]
 end;
   cbn [Bit.toBool] in Compare;rewrite <-Compare;
   cbn [fst snd];rewrite literal_eea_row_step_numeric;reflexivity.
Qed.

Theorem literal_eea_run_numeric n count s :
 eea_state_denote n (literal_eea_run n count s)=
 eea_run_numeric (word_modulus n) count (eea_state_denote n s).
Proof.
 revert s;induction count;intro s;cbn [literal_eea_run eea_run_numeric];[reflexivity|].
 rewrite IHcount,literal_eea_step_numeric;reflexivity.
Qed.

Theorem literal_eea_iterate_numeric n depth s :
 eea_state_denote n (@literal_eea_iterate n depth Alg.CoreFunSem s)=
 eea_run_numeric (word_modulus n) (Nat.pow 2 (S depth)) (eea_state_denote n s).
Proof. rewrite literal_eea_iterate_run;apply literal_eea_run_numeric. Qed.

Lemma eea_fill_zero n (x : Ty.tySem Bit) :
 @Word.fill Bit Bit n Alg.CoreFunSem (fun _ => Bit.zero) x=@Word.zero n Alg.CoreFunSem tt.
Proof.
 induction n;[reflexivity|].
 change ((@Word.fill Bit Bit n Alg.CoreFunSem (fun _ => Bit.zero) x,
   @Word.fill Bit Bit n Alg.CoreFunSem (fun _ => Bit.zero) x)=
   (@Word.zero n Alg.CoreFunSem tt,@Word.zero n Alg.CoreFunSem tt)).
 rewrite IHn;reflexivity.
Qed.

Lemma literal_eea_one_successor n : @literal_eea_one (S n) Alg.CoreFunSem tt=
 (@Word.zero n Alg.CoreFunSem tt,@literal_eea_one n Alg.CoreFunSem tt).
Proof.
 change ((@Word.fill Bit Bit n Alg.CoreFunSem (fun _ => Bit.zero) Bit.one,
   @literal_eea_one n Alg.CoreFunSem tt)=
   (@Word.zero n Alg.CoreFunSem tt,@literal_eea_one n Alg.CoreFunSem tt)).
 rewrite eea_fill_zero;reflexivity.
Qed.

Lemma literal_eea_one_numeric n : @toZ (WordToZ n) (@literal_eea_one n Alg.CoreFunSem tt)=1.
Proof.
 induction n;[reflexivity|].
 rewrite literal_eea_one_successor.
 change (@toZ (WordToZ n) (@Word.zero n Alg.CoreFunSem tt)*word_modulus n+
   @toZ (WordToZ n) (@literal_eea_one n Alg.CoreFunSem tt)=1).
 rewrite Word.zero_correct,IHn;ring.
Qed.

Lemma literal_eea_pre_numeric n (x y : Ty.tySem (Word n)) : eea_state_denote n (@literal_eea_pre n Alg.CoreFunSem (x,y))=
 (((1,0),@toZ (WordToZ n) x),((0,1),@toZ (WordToZ n) y)).
Proof.
 rewrite literal_eea_pre_expansion;unfold eea_state_denote,eea_row_denote;cbn [fst snd].
 rewrite !Word.zero_correct,!literal_eea_one_numeric;reflexivity.
Qed.

Definition eea_bezout_denote n (v : Ty.tySem (Ty.Sum (Ty.Prod (Word n) (Word n)) (Ty.Prod (Word n) (Word n)))) :=
 match v with
 | inl (a,b) => inl (@toZ (WordToZ n) a,@toZ (WordToZ n) b)
 | inr (d,e) => inr (@toZ (WordToZ n) d,@toZ (WordToZ n) e)
 end.
Definition eea_bezout_numeric (s : ((Z*Z)*Z)*((Z*Z)*Z)) :=
 let '(((a,b),c),((d,e),f)):=s in if Z.eqb f 0 then inl (a,b) else inr (d,e).

Lemma literal_eea_post_numeric n s :
 eea_bezout_denote n (fst (fst (@literal_eea_post n Alg.CoreFunSem s)))=
 eea_bezout_numeric (eea_state_denote n s).
Proof.
 destruct s as [[[a b] c] [[d e] f]];rewrite literal_eea_post_expansion.
 pose proof (is_zero_word_spec_numeric n f) as Zero.
 unfold eea_bezout_numeric,eea_state_denote,eea_row_denote;cbn [fst snd].
 match goal with
 | |- context [match ?guard with inl _ => _ | inr _ => _ end] =>
   change (Bit.toBool guard=Z.eqb (@toZ (WordToZ n) f) 0) in Zero;
   destruct guard as [[] | []]
 end;cbn [Bit.toBool] in Zero;rewrite <-Zero;reflexivity.
Qed.

Theorem literal_bezout_numeric n (x y : Ty.tySem (Word n)) :
 eea_bezout_denote n (@literal_bezout n Alg.CoreFunSem (x,y))=
 eea_bezout_numeric (eea_run_numeric (word_modulus n) (Nat.pow 2 (S n))
   (((1,0),@toZ (WordToZ n) x),((0,1),@toZ (WordToZ n) y))).
Proof.
 rewrite literal_bezout_run,literal_eea_post_numeric,literal_eea_run_numeric,literal_eea_pre_numeric.
 reflexivity.
Qed.
