(** Structural port of Programs.Arith.eeaStep, eeaStep_iterate, eea and
    bezout (Arith.hs:364--414). This is the missing literal normalization
    component for the C generate proof, not another specification target. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_order_spec C.jet_literal_division_add C.jet_test_value_spec C.jet_extend_word_spec.
Import ListNotations.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition literal_eea_row n := Ty.Prod (Ty.Prod (Word n) (Word n)) (Word n).
Definition literal_eea_state n := Ty.Prod (literal_eea_row n) (literal_eea_row n).
Definition literal_eea_result n := Ty.Prod
 (Ty.Prod (Ty.Sum (Ty.Prod (Word n) (Word n)) (Ty.Prod (Word n) (Word n)))
          (Ty.Prod (Word n) (Word n))) (Word n).

Definition literal_eea_row_step n {term : Alg.Core.Algebra} :
 term (literal_eea_state n) (literal_eea_row n) :=
 ((O I H &&& I I H >>> @literal_div_mod_word_spec n term) &&& (O O H &&& I O H)) >>>
 ((((O O H &&& I I O H) &&& (I O O H &&& (unit >>> @Word.zero n term)) >>> @Word.fullMultiplier n term >>> I H) &&&
   ((O O H &&& I I I H) &&& (I O I H &&& (unit >>> @Word.zero n term)) >>> @Word.fullMultiplier n term >>> I H)) &&& O I H).

Definition literal_eea_step n {term : Alg.Core.Algebra} :
 term (literal_eea_state n) (literal_eea_state n) :=
 ((I I H &&& O I H >>> @lt_word_spec term n) &&& iden) >>>
 Bit.cond (@literal_eea_row_step n term &&& I H)
   (O H &&& (I H &&& O H >>> @literal_eea_row_step n term)).

Fixpoint literal_eea_iterate n depth {term : Alg.Core.Algebra} :
 term (literal_eea_state n) (literal_eea_state n) :=
 match depth with
 | Datatypes.O => @literal_eea_step n term >>> @literal_eea_step n term
 | Datatypes.S d => @literal_eea_iterate n d term >>> @literal_eea_iterate n d term
 end.

Definition literal_eea_one n {term : Alg.Core.Algebra} : term Ty.Unit (Word n) :=
 Bit.true >>> @left_pad_word_spec 0 n Datatypes.false term.
Definition literal_eea_pre n {term : Alg.Core.Algebra} :
 term (Ty.Prod (Word n) (Word n)) (literal_eea_state n) :=
 (((unit >>> @literal_eea_one n term) &&& (unit >>> @Word.zero n term)) &&& O H) &&&
 (((unit >>> @Word.zero n term) &&& (unit >>> @literal_eea_one n term)) &&& I H).
Definition literal_eea_post n {term : Alg.Core.Algebra} :
 term (literal_eea_state n) (literal_eea_result n) :=
 (I (I (@is_zero_word_spec n term)) &&& iden) >>>
 Bit.cond ((injl (O O H) &&& I O H) &&& O I H)
          ((injr (I O H) &&& O O H) &&& I I H).
Definition literal_eea n {term : Alg.Core.Algebra} :
 term (Ty.Prod (Word n) (Word n)) (literal_eea_result n) :=
 @literal_eea_pre n term >>> @literal_eea_iterate n n term >>> @literal_eea_post n term.
Definition literal_bezout n {term : Alg.Core.Algebra} :
 term (Ty.Prod (Word n) (Word n))
   (Ty.Sum (Ty.Prod (Word n) (Word n)) (Ty.Prod (Word n) (Word n))) :=
 @literal_eea n term >>> O O H.

Lemma literal_eea_row_step_expansion n (a b c d e f : Ty.tySem (Word n)) :
 @literal_eea_row_step n Alg.CoreFunSem (((a,b),c),((d,e),f))=
 let '(q,r):=@literal_div_mod_word_spec n Alg.CoreFunSem (c,f) in
 ((snd (@Word.fullMultiplier n Alg.CoreFunSem ((q,d),(a,@Word.zero n Alg.CoreFunSem tt))),
   snd (@Word.fullMultiplier n Alg.CoreFunSem ((q,e),(b,@Word.zero n Alg.CoreFunSem tt)))),r).
Proof.
 unfold literal_eea_row_step.
 change ((let qr:=@literal_div_mod_word_spec n Alg.CoreFunSem (c,f) in
   ((snd (@Word.fullMultiplier n Alg.CoreFunSem ((fst qr,d),(a,@Word.zero n Alg.CoreFunSem tt))),
     snd (@Word.fullMultiplier n Alg.CoreFunSem ((fst qr,e),(b,@Word.zero n Alg.CoreFunSem tt)))),snd qr))=
   let '(q,r):=@literal_div_mod_word_spec n Alg.CoreFunSem (c,f) in
   ((snd (@Word.fullMultiplier n Alg.CoreFunSem ((q,d),(a,@Word.zero n Alg.CoreFunSem tt))),
     snd (@Word.fullMultiplier n Alg.CoreFunSem ((q,e),(b,@Word.zero n Alg.CoreFunSem tt)))),r)).
 destruct (@literal_div_mod_word_spec n Alg.CoreFunSem (c,f));reflexivity.
Qed.

Lemma literal_eea_step_expansion n (a b c d e f : Ty.tySem (Word n)) :
 @literal_eea_step n Alg.CoreFunSem (((a,b),c),((d,e),f))=
 match @lt_word_spec Alg.CoreFunSem n (f,c) with
 | inr _ => (@literal_eea_row_step n Alg.CoreFunSem (((a,b),c),((d,e),f)),((d,e),f))
 | inl _ => (((a,b),c),@literal_eea_row_step n Alg.CoreFunSem (((d,e),f),((a,b),c)))
 end.
Proof. reflexivity. Qed.

Fixpoint literal_eea_run n count (s : Ty.tySem (literal_eea_state n)) :=
 match count with Datatypes.O => s | Datatypes.S k => literal_eea_run n k (@literal_eea_step n Alg.CoreFunSem s) end.

Lemma literal_eea_run_add n a b s :
 literal_eea_run n (a+b) s=literal_eea_run n b (literal_eea_run n a s).
Proof. revert s;induction a;intro s;cbn [Nat.add literal_eea_run];[reflexivity|apply IHa]. Qed.

Theorem literal_eea_iterate_run n depth s :
 @literal_eea_iterate n depth Alg.CoreFunSem s=literal_eea_run n (Nat.pow 2 (S depth)) s.
Proof.
 revert s;induction depth;intro s.
 - reflexivity.
 - cbn [literal_eea_iterate];change
   (@literal_eea_iterate n depth Alg.CoreFunSem (@literal_eea_iterate n depth Alg.CoreFunSem s)=
    literal_eea_run n (Nat.pow 2 (S (S depth))) s).
   rewrite !IHdepth,<-literal_eea_run_add.
   f_equal;cbn [Nat.pow];lia.
Qed.

Lemma literal_eea_pre_expansion n (x y : Ty.tySem (Word n)) :
 @literal_eea_pre n Alg.CoreFunSem (x,y)=
 (((@literal_eea_one n Alg.CoreFunSem tt,@Word.zero n Alg.CoreFunSem tt),x),
  ((@Word.zero n Alg.CoreFunSem tt,@literal_eea_one n Alg.CoreFunSem tt),y)).
Proof. reflexivity. Qed.

Lemma literal_eea_post_expansion n (a b c d e f : Ty.tySem (Word n)) :
 @literal_eea_post n Alg.CoreFunSem (((a,b),c),((d,e),f))=
 match @is_zero_word_spec n Alg.CoreFunSem f with
 | inr _ => ((inl (a,b),(d,e)),c)
 | inl _ => ((inr (d,e),(a,b)),f)
 end.
Proof. reflexivity. Qed.

Theorem literal_bezout_run n (x y : Ty.tySem (Word n)) :
 @literal_bezout n Alg.CoreFunSem (x,y)=
 fst (fst (@literal_eea_post n Alg.CoreFunSem
   (literal_eea_run n (Nat.pow 2 (S n)) (@literal_eea_pre n Alg.CoreFunSem (x,y))))).
Proof.
 unfold literal_bezout,literal_eea.
 change (fst (fst (@literal_eea_post n Alg.CoreFunSem
   (@literal_eea_iterate n n Alg.CoreFunSem (@literal_eea_pre n Alg.CoreFunSem (x,y)))))=
   fst (fst (@literal_eea_post n Alg.CoreFunSem
   (literal_eea_run n (Nat.pow 2 (S n)) (@literal_eea_pre n Alg.CoreFunSem (x,y)))))).
 rewrite literal_eea_iterate_run;reflexivity.
Qed.
