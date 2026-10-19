(** Literal-add division ports and semantic bridge to the existing executor ports. *)
From Coq Require Import FunctionalExtensionality.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_order_spec C.jet_subtract_spec C.jet_multiply_spec C.jet_division_core_spec.
Require Import C.jet_division_normalize_spec C.jet_test_value_spec C.jet_canonical_add_adapter.
Local Open Scope term_scope.
Set Default Timeout 10.

Lemma canonical_add_function_matches n :
  @canonical_add_word n Alg.CoreFunSem = @Word.adder n Alg.CoreFunSem.
Proof. apply functional_extensionality; apply canonical_add_word_matches_adder. Qed.

Definition literal_div3n2n_approx_spec n {term : Alg.Core.Algebra}
    (rec : term (Ty.Prod (Word (S n)) (Word n)) (Word (S n))) :
  term (Ty.Prod (Word (S n)) (Word n)) (Ty.Prod Bit (Word (S n))) :=
    (((O O H &&& I H) >>> @lt_word_spec term n) &&& H) >>>
    Bit.cond (Bit.false &&& rec)
      (((O I H &&& I H) >>> @canonical_add_word n term) >>>
        O H &&& ((Alg.Core.Combinators.unit >>> @division_high_word n term) &&& I H)).

Definition literal_div3n2n_loop2_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S n)) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
  let dec := @decrement_word_spec term n in
  let add2w := @canonical_add_word (S n) term in
  (I (O (dec >>> I H))) &&& ((O H &&& I I H) >>> add2w >>> I H).

Definition literal_div3n2n_loop1_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S n)) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
  let dec := @decrement_word_spec term n in
  let add2w := @canonical_add_word (S n) term in
  (((O H &&& I I H) >>> add2w) &&& I ((O (dec >>> I H)) &&& I H)) >>>
    O O H &&& (O I H &&& I H) >>>
      Bit.cond (I O H &&& O H) (@literal_div3n2n_loop2_spec n term).

Definition literal_div3n2n_loop0_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod Bit (Word (S n))) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
  (O O H &&& (O I H &&& I H)) >>>
    Bit.cond (@literal_div3n2n_loop1_spec n term) (I O H &&& O H).

Definition literal_div3n2n_body_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Ty.Prod Bit (Word (S n))) (Ty.Prod (Word n) (Word (S n))))
       (Ty.Prod (Word n) (Word (S n))) :=
    (O O H &&&
      ((((O I I H &&& I O H) &&& ((O I O H &&& I I I H) >>> @multiply_word_spec n term)) >>>
          @subtract_word_spec term (S n)) &&& (O I O H &&& I I H))) >>>
      Bit.cond (I O H &&& O I H) (@literal_div3n2n_loop0_spec n term).

Definition literal_div3n2n_word_builder n {term : Alg.Core.Algebra}
    (rec : term (Ty.Prod (Word (S n)) (Word n)) (Word (S n))) :
  term (Ty.Prod (Ty.Prod (Word (S n)) (Word n)) (Word (S n)))
       (Ty.Prod (Word n) (Word (S n))) :=
  (((O O H &&& I O H) >>> @literal_div3n2n_approx_spec n term rec) &&& (O I H &&& I H)) >>>
    @literal_div3n2n_body_spec n term.

Fixpoint literal_div2n1n_word_spec n {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (S n)) (Word n)) (Word (S n)) :=
  match n as n return term (Ty.Prod (Word (S n)) (Word n)) (Word (S n)) with
  | Datatypes.O => @div2n1n_bit_spec term
  | Datatypes.S n =>
      let rec := @literal_div3n2n_word_builder n term (@literal_div2n1n_word_spec n term) in
      let body :=
        ((((O O H &&& O I O H) &&& I H) >>> rec) &&& (O I I H &&& I H)) >>>
        (O O H &&& (((O I H &&& I O H) &&& I I H) >>> rec)) >>>
        ((O H &&& I O H) &&& I I H) in
      (@div2n1n_conditions (S n) term &&& H) >>>
        Bit.cond body (Alg.Core.Combinators.unit >>> @division_high_word (S (S n)) term)
  end.

Definition literal_div3n2n_word_spec n {term : Alg.Core.Algebra} :=
  @literal_div3n2n_word_builder n term (@literal_div2n1n_word_spec n term).

Definition literal_div_mod_word_spec n {term : Alg.Core.Algebra} :
  term (Word (S n)) (Word (S n)) :=
  (I (@is_zero_word_spec n term) &&& H) >>>
  Bit.cond (I H &&& O H)
    (((((Alg.Core.Combinators.unit >>> @Word.zero n term) &&& O H) &&& I H) >>>
      @division_pre_shift_spec n 0 term >>> @literal_div2n1n_word_spec n term) &&& I H >>>
    O O H &&& ((O I H &&& I H) >>> @division_post_shift_spec n 0 term >>> O H)).

Definition literal_modulo_word_spec n {term : Alg.Core.Algebra} :=
  @literal_div_mod_word_spec n term >>> I H.

Lemma literal_approx_matches n (rec : Ty.Arrow (Ty.Prod (Word (S n)) (Word n)) (Word (S n))) :
  @literal_div3n2n_approx_spec n Alg.CoreFunSem rec = @div3n2n_approx_spec n Alg.CoreFunSem rec.
Proof.
  unfold literal_div3n2n_approx_spec, div3n2n_approx_spec.
  rewrite canonical_add_function_matches. reflexivity.
Qed.
Lemma literal_loop2_matches n :
  @literal_div3n2n_loop2_spec n Alg.CoreFunSem = @div3n2n_loop2_spec n Alg.CoreFunSem.
Proof.
  unfold literal_div3n2n_loop2_spec, div3n2n_loop2_spec.
  rewrite canonical_add_function_matches. reflexivity.
Qed.
Lemma literal_loop1_matches n :
  @literal_div3n2n_loop1_spec n Alg.CoreFunSem = @div3n2n_loop1_spec n Alg.CoreFunSem.
Proof.
  unfold literal_div3n2n_loop1_spec, div3n2n_loop1_spec.
  rewrite canonical_add_function_matches, literal_loop2_matches. reflexivity.
Qed.
Lemma literal_loop0_matches n :
  @literal_div3n2n_loop0_spec n Alg.CoreFunSem = @div3n2n_loop0_spec n Alg.CoreFunSem.
Proof.
  unfold literal_div3n2n_loop0_spec, div3n2n_loop0_spec.
  rewrite literal_loop1_matches. reflexivity.
Qed.
Lemma literal_body_matches n :
  @literal_div3n2n_body_spec n Alg.CoreFunSem = @div3n2n_body_spec n Alg.CoreFunSem.
Proof.
  unfold literal_div3n2n_body_spec, div3n2n_body_spec.
  rewrite literal_loop0_matches. reflexivity.
Qed.
Lemma literal_builder_matches n (rec : Ty.Arrow (Ty.Prod (Word (S n)) (Word n)) (Word (S n))) :
  @literal_div3n2n_word_builder n Alg.CoreFunSem rec = @div3n2n_word_builder n Alg.CoreFunSem rec.
Proof.
  unfold literal_div3n2n_word_builder, div3n2n_word_builder.
  rewrite literal_approx_matches, literal_body_matches. reflexivity.
Qed.
Lemma literal_div2n1n_matches n :
  @literal_div2n1n_word_spec n Alg.CoreFunSem = @div2n1n_word_spec n Alg.CoreFunSem.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - cbn [literal_div2n1n_word_spec div2n1n_word_spec].
    rewrite IH, literal_builder_matches. reflexivity.
Qed.
Lemma literal_div3n2n_matches n :
  @literal_div3n2n_word_spec n Alg.CoreFunSem = @div3n2n_word_spec n Alg.CoreFunSem.
Proof.
  unfold literal_div3n2n_word_spec, div3n2n_word_spec.
  rewrite literal_div2n1n_matches, literal_builder_matches. reflexivity.
Qed.
Lemma literal_div_mod_matches n :
  @literal_div_mod_word_spec n Alg.CoreFunSem = @div_mod_word_spec n Alg.CoreFunSem.
Proof.
  unfold literal_div_mod_word_spec, div_mod_word_spec.
  rewrite literal_div2n1n_matches. reflexivity.
Qed.
Lemma literal_modulo_matches n :
  @literal_modulo_word_spec n Alg.CoreFunSem = @modulo_word_spec n Alg.CoreFunSem.
Proof.
  unfold literal_modulo_word_spec, modulo_word_spec.
  rewrite literal_div_mod_matches. reflexivity.
Qed.
Print Assumptions literal_modulo_matches.
