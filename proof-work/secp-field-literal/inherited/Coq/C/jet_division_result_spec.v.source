(** Quotient/remainder observations of canonical recursive division.
    These connect normalization and the checked recursive core; not C coverage. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_predicate_spec C.jet_test_value_spec C.jet_division_core_spec.
Require Import C.jet_division_normalize_spec C.jet_division_approx_spec C.jet_division_recursive_spec.
Require Import C.jet_division_correction_spec.
Require Import C.jet_division_value C.jet_toZ.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma division_euclidean_observation N D Q R :
  Q*D+R=N -> 0 <= R < D -> Q=N/D /\ R=N mod D.
Proof.
  intros HE HR. split.
  - apply Z.div_unique with (r := R); [left; exact HR|nia].
  - apply Z.mod_unique with (q := Q); [left; exact HR|nia].
Qed.

Lemma div2n1n_normalized_observation n (a : Ty.tySem (Word (S n))) (b : Ty.tySem (Word n)) :
  word_modulus n <= 2 * @toZ (WordToZ n) b ->
  @toZ (WordToZ (S n)) a < @toZ (WordToZ n) b * word_modulus n ->
  let qr := @div2n1n_word_spec n Alg.CoreFunSem (a,b) in
  @toZ (WordToZ n) (fst qr) = @toZ (WordToZ (S n)) a / @toZ (WordToZ n) b /\
  @toZ (WordToZ n) (snd qr) = @toZ (WordToZ (S n)) a mod @toZ (WordToZ n) b.
Proof.
  intros Hnorm Hbound. destruct (div2n1n_normalized_value n a b Hnorm Hbound) as [HE HR].
  apply division_euclidean_observation; assumption.
Qed.

Lemma div2n1n_invalid_result n (a : Ty.tySem (Word (S n))) (b : Ty.tySem (Word n)) :
  @div2n1n_conditions n Alg.CoreFunSem (a,b) = Bit.zero ->
  @div2n1n_word_spec n Alg.CoreFunSem (a,b) = @division_high_word (S n) Alg.CoreFunSem tt.
Proof.
  destruct n as [|n].
  - destruct a as [a1 a2]. destruct a1 as [[] | []], a2 as [[] | []], b as [[] | []];
      cbn; intros; try discriminate; reflexivity.
  - destruct a as [[a1 a2] [a3 a4]], b as [b1 b2]. intros HG.
    rewrite div2n1n_successor_unfold.
    match goal with
    | |- context [match ?guard with inl _ => _ | inr _ => _ end] =>
      assert (HGexact : guard = (Bit.zero : Ty.tySem Bit)) by exact HG;
      rewrite HGexact
    end. reflexivity.
Qed.

Lemma division_descaling_euclidean a b k q r :
  0 < k -> 0 < b -> q*(b*k)+r=a*k -> 0 <= r < b*k ->
  q=a/b /\ r/k=a mod b.
Proof.
  intros HK HB HE HR.
  assert (Hrem : r = (a-q*b)*k) by nia.
  assert (Hsmall : 0 <= a-q*b < b) by nia.
  destruct (division_euclidean_observation a b q (a-q*b)) as [HQ HM]; [ring|exact Hsmall|].
  split; [exact HQ|]. rewrite Hrem, Z.div_mul by lia. exact HM.
Qed.

Lemma div_mod_nonzero_unfold n (a b : Ty.tySem (Word n)) :
  @is_zero_word_spec n Alg.CoreFunSem b = Bit.zero ->
  @div_mod_word_spec n Alg.CoreFunSem (a,b) =
  let p := @division_pre_shift_spec n 0 Alg.CoreFunSem ((@Word.zero n Alg.CoreFunSem tt,a),b) in
  let qr := @div2n1n_word_spec n Alg.CoreFunSem p in
  (fst qr,fst (@division_post_shift_spec n 0 Alg.CoreFunSem (snd qr,b))).
Proof.
  intros HG. unfold div_mod_word_spec.
  cbn -[is_zero_word_spec division_pre_shift_spec div2n1n_word_spec division_post_shift_spec Word.zero].
  match goal with
  | |- context [match ?guard with inl _ => _ | inr _ => _ end] =>
    assert (HGexact : guard = (Bit.zero : Ty.tySem Bit)) by exact HG;
    rewrite HGexact
  end. reflexivity.
Qed.

Lemma div2n1n_state_value n
    (p : Ty.tySem (Ty.Prod (Word (S n)) (Word n))) :
  word_modulus n <= 2 * @toZ (WordToZ n) (snd p) ->
  @toZ (WordToZ (S n)) (fst p) < @toZ (WordToZ n) (snd p) * word_modulus n ->
  let qr := @div2n1n_word_spec n Alg.CoreFunSem p in
  @toZ (WordToZ n) (fst qr) * @toZ (WordToZ n) (snd p) + @toZ (WordToZ n) (snd qr) =
    @toZ (WordToZ (S n)) (fst p) /\
  0 <= @toZ (WordToZ n) (snd qr) < @toZ (WordToZ n) (snd p).
Proof. destruct p as [a b]. apply div2n1n_normalized_value. Qed.

Lemma division_is_zero_positive n (b : Ty.tySem (Word n)) :
  0 < @toZ (WordToZ n) b -> @is_zero_word_spec n Alg.CoreFunSem b = Bit.zero.
Proof.
  intros HB. pose proof (is_zero_word_spec_numeric n b) as HG.
  assert (HE : Z.eqb (@toZ (WordToZ n) b) 0 = Datatypes.false) by (apply Z.eqb_neq; lia).
  rewrite HE in HG.
  destruct (@is_zero_word_spec n Alg.CoreFunSem b) as [[] | []]; [reflexivity|discriminate].
Qed.

Lemma div_mod_word_nonzero n (a b : Ty.tySem (Word n)) :
  0 < @toZ (WordToZ n) b ->
  let qr := @div_mod_word_spec n Alg.CoreFunSem (a,b) in
  @toZ (WordToZ n) (fst qr) = @toZ (WordToZ n) a / @toZ (WordToZ n) b /\
  @toZ (WordToZ n) (snd qr) = @toZ (WordToZ n) a mod @toZ (WordToZ n) b.
Proof.
  intros HB. cbn zeta. rewrite div_mod_nonzero_unfold by (apply division_is_zero_positive; exact HB).
  match goal with
  | |- context [@division_pre_shift_spec ?depth ?outer ?alg ?input] =>
    set (p := @division_pre_shift_spec depth outer alg input)
  end.
  cbv beta iota zeta delta [fst snd].
  match goal with
  | |- context [@div2n1n_word_spec ?depth ?alg ?input] =>
    set (qr := @div2n1n_word_spec depth alg input)
  end.
  assert (Hnormal : exists k, 0 < k /\
    @toZ (WordToZ (S n)) (fst p) = @toZ (WordToZ n) a * k /\
    @toZ (WordToZ n) (snd p) = @toZ (WordToZ n) b * k /\
    @toZ (WordToZ n) (fst (@division_post_shift_spec n 0 Alg.CoreFunSem (snd qr,b))) =
      @toZ (WordToZ n) (snd qr) / k /\
    @toZ (WordToZ n) (snd (@division_post_shift_spec n 0 Alg.CoreFunSem (snd qr,b))) =
      @toZ (WordToZ n) (snd p) /\
    word_modulus n <= 2 * @toZ (WordToZ n) (snd p) /\
    @toZ (WordToZ (S n)) (fst p) < @toZ (WordToZ n) (snd p) * word_modulus n).
  { exact (division_plain_input_normalization n a (snd qr) b HB). }
  destruct Hnormal as [k [HK [HA [HD [Hpost [Hsame [Hnorm Hbound]]]]]]].
  assert (Hcore : @toZ (WordToZ n) (fst qr) * @toZ (WordToZ n) (snd p) +
    @toZ (WordToZ n) (snd qr) = @toZ (WordToZ (S n)) (fst p) /\
    0 <= @toZ (WordToZ n) (snd qr) < @toZ (WordToZ n) (snd p)).
  { exact (div2n1n_state_value n p Hnorm Hbound). }
  destruct Hcore as [Hbalance Hrange].
  assert (Hscaled : @toZ (WordToZ n) (fst qr) * (@toZ (WordToZ n) b * k) +
    @toZ (WordToZ n) (snd qr) = @toZ (WordToZ n) a * k).
  { rewrite <- HD, <- HA. exact Hbalance. }
  assert (Hscaled_range : 0 <= @toZ (WordToZ n) (snd qr) < @toZ (WordToZ n) b * k).
  { rewrite <- HD. exact Hrange. }
  destruct (division_descaling_euclidean (@toZ (WordToZ n) a) (@toZ (WordToZ n) b)
    k (@toZ (WordToZ n) (fst qr)) (@toZ (WordToZ n) (snd qr)) HK HB Hscaled Hscaled_range)
    as [HQ HR].
  split; [exact HQ|]. etransitivity; [exact Hpost|exact HR].
Qed.

Lemma div_mod_word_numeric n (a b : Ty.tySem (Word n)) :
  let qr := @div_mod_word_spec n Alg.CoreFunSem (a,b) in
  @toZ (WordToZ n) (fst qr) =
    division_numeric Datatypes.false (@toZ (WordToZ n) a) (@toZ (WordToZ n) b) /\
  @toZ (WordToZ n) (snd qr) =
    division_numeric Datatypes.true (@toZ (WordToZ n) a) (@toZ (WordToZ n) b).
Proof.
  cbn zeta. unfold division_numeric.
  destruct (Z.eqb (@toZ (WordToZ n) b) 0) eqn:HB.
  - apply Z.eqb_eq in HB.
    assert (HZ : b = @Word.zero n Alg.CoreFunSem tt).
    { apply (toZ_injective (WordToZ n)). rewrite Word.zero_correct. exact HB. }
    rewrite HZ, div_mod_word_zero. cbn [fst snd]. split; [apply Word.zero_correct|reflexivity].
  - apply Z.eqb_neq in HB.
    apply div_mod_word_nonzero.
    pose proof (word_value_bounds n b) as HR. lia.
Qed.

Definition division_word_spec n (remainder : bool) {term : Alg.Core.Algebra} :=
  if remainder then @modulo_word_spec n term else @divide_word_spec n term.

Lemma division_word_spec_parametric n remainder : Alg.Core.Parametric (@division_word_spec n remainder).
Proof. destruct remainder; [apply modulo_word_spec_parametric|apply divide_word_spec_parametric]. Qed.

Lemma division_word_spec_numeric n remainder (a b : Ty.tySem (Word n)) :
  @toZ (WordToZ n) (@division_word_spec n remainder Alg.CoreFunSem (a,b)) =
    division_numeric remainder (@toZ (WordToZ n) a) (@toZ (WordToZ n) b).
Proof.
  destruct (div_mod_word_numeric n a b) as [HQ HR].
  destruct remainder; [exact HR|exact HQ].
Qed.

Lemma division_word_representation n remainder (a b : Ty.tySem (Word n)) :
  @fromZ (WordToZ n) (division_numeric remainder (@toZ (WordToZ n) a) (@toZ (WordToZ n) b)) =
    @division_word_spec n remainder Alg.CoreFunSem (a,b).
Proof.
  transitivity (@fromZ (WordToZ n)
    (@toZ (WordToZ n) (@division_word_spec n remainder Alg.CoreFunSem (a,b)))).
  - f_equal. symmetry. apply division_word_spec_numeric.
  - apply from_toZ.
Qed.
