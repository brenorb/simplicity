(** Numeric observations of the literal div3n2n correction programs.
    These are shared canonical bridges, not additional C jet coverage. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg Simplicity.Bit.
Require Import C.jet_division_core_spec C.jet_borrow_unary_word.
Require Import C.jet_order_spec C.jet_multiply_spec.
Require Import C.jet_predicate_spec C.jet_subtract_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma division_high_word_value n :
  @toZ (WordToZ n) (@division_high_word n Alg.CoreFunSem tt) = word_modulus n - 1.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - change (@toZ (WordToZ n) (@division_high_word n Alg.CoreFunSem tt) * word_modulus n +
      @toZ (WordToZ n) (@division_high_word n Alg.CoreFunSem tt) = word_modulus (S n) - 1).
    rewrite IH, word_modulus_S. ring.
Qed.

Lemma div3n2n_loop1_unfold n (r b : Ty.tySem (Word (S n))) (q : Ty.tySem (Word n)) :
  @div3n2n_loop1_spec n Alg.CoreFunSem (r,(q,b)) =
  let s := @Word.adder (S n) Alg.CoreFunSem (r,b) in
  let d := snd (@decrement_word_spec Alg.CoreFunSem n q) in
  match fst s with
  | inl _ => @div3n2n_loop2_spec n Alg.CoreFunSem (snd s,(d,b))
  | inr _ => (d,snd s)
  end.
Proof. reflexivity. Qed.


Lemma div3n2n_loop0_unfold n (r b : Ty.tySem (Word (S n))) (q : Ty.tySem (Word n)) c :
  @div3n2n_loop0_spec n Alg.CoreFunSem ((c,r),(q,b)) =
  match c with
  | inl _ => (q,r)
  | inr _ => @div3n2n_loop1_spec n Alg.CoreFunSem (r,(q,b))
  end.
Proof. destruct c as [[] | []]; reflexivity. Qed.

Lemma division_add_balance n (x y : Ty.tySem (Word n)) :
  let z := @Word.adder n Alg.CoreFunSem (x,y) in
  word_modulus n * @toZ BitToZ (fst z) + @toZ (WordToZ n) (snd z) =
    @toZ (WordToZ n) x + @toZ (WordToZ n) y.
Proof.
  pose proof (Word.adder_correct n x y) as Hsum.
  destruct (@Word.adder n Alg.CoreFunSem (x,y)) as [c r].
  change (@toZ BitToZ c * word_modulus n + @toZ (WordToZ n) r =
    @toZ (WordToZ n) x + @toZ (WordToZ n) y) in Hsum.
  cbn [fst snd]. nia.
Qed.

Lemma division_decrement_positive n (q : Ty.tySem (Word n)) :
  0 < @toZ (WordToZ n) q ->
  @toZ (WordToZ n) (snd (@decrement_word_spec Alg.CoreFunSem n q)) =
    @toZ (WordToZ n) q - 1.
Proof.
  intros HQ.
  pose proof (unary_borrow_spec_numeric UDecrement n q) as Hdec.
  change (borrow_word_balance n (@decrement_word_spec Alg.CoreFunSem n q) =
    @toZ (WordToZ n) q - 1) in Hdec.
  destruct (@decrement_word_spec Alg.CoreFunSem n q) as [c r].
  pose proof (word_value_bounds n r) as HR.
  unfold borrow_word_balance in Hdec. cbn [fst snd] in Hdec |- *.
  destruct c as [[] | []].
  - change (@toZ (WordToZ n) r - word_modulus n * 0 = @toZ (WordToZ n) q - 1) in Hdec.
    lia.
  - change (@toZ (WordToZ n) r - word_modulus n * 1 = @toZ (WordToZ n) q - 1) in Hdec.
    lia.
Qed.

Lemma div3n2n_loop2_value n (r b : Ty.tySem (Word (S n))) (q : Ty.tySem (Word n)) delta :
  0 < @toZ (WordToZ n) q ->
  @toZ (WordToZ (S n)) r = delta + word_modulus (S n) ->
  0 <= delta + @toZ (WordToZ (S n)) b < word_modulus (S n) ->
  let z := @div3n2n_loop2_spec n Alg.CoreFunSem (r,(q,b)) in
  @toZ (WordToZ n) (fst z) = @toZ (WordToZ n) q - 1 /\
  @toZ (WordToZ (S n)) (snd z) = delta + @toZ (WordToZ (S n)) b.
Proof.
  intros HQ HR HB.
  change (@toZ (WordToZ n) (snd (@decrement_word_spec Alg.CoreFunSem n q)) =
    @toZ (WordToZ n) q - 1 /\
    @toZ (WordToZ (S n)) (snd (@Word.adder (S n) Alg.CoreFunSem (r,b))) =
      delta + @toZ (WordToZ (S n)) b).
  split; [apply division_decrement_positive; exact HQ|].
  pose proof (division_add_balance (S n) r b) as Hsum.
  destruct (@Word.adder (S n) Alg.CoreFunSem (r,b)) as [c t].
  pose proof (word_value_bounds (S n) t) as HT.
  cbn [fst snd] in Hsum |- *.
  destruct c as [[] | []].
  - change (word_modulus (S n) * 0 + @toZ (WordToZ (S n)) t =
      @toZ (WordToZ (S n)) r + @toZ (WordToZ (S n)) b) in Hsum. lia.
  - change (word_modulus (S n) * 1 + @toZ (WordToZ (S n)) t =
      @toZ (WordToZ (S n)) r + @toZ (WordToZ (S n)) b) in Hsum. lia.
Qed.

Lemma div3n2n_loop1_value n (r b : Ty.tySem (Word (S n))) (q : Ty.tySem (Word n)) delta :
  @toZ (WordToZ (S n)) r = delta + word_modulus (S n) ->
  -2 * @toZ (WordToZ (S n)) b <= delta < 0 ->
  0 <= @toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + delta ->
  let z := @div3n2n_loop1_spec n Alg.CoreFunSem (r,(q,b)) in
  @toZ (WordToZ n) (fst z) * @toZ (WordToZ (S n)) b +
    @toZ (WordToZ (S n)) (snd z) =
    @toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + delta /\
  0 <= @toZ (WordToZ (S n)) (snd z) < @toZ (WordToZ (S n)) b.
Proof.
  intros HR Hdelta HN. cbn zeta. rewrite div3n2n_loop1_unfold.
  pose proof (word_value_bounds n q) as HQ.
  pose proof (word_value_bounds (S n) b) as HB.
  assert (HQpos : 0 < @toZ (WordToZ n) q) by nia.
  set (q1 := snd (@decrement_word_spec Alg.CoreFunSem n q)).
  assert (Hq1 : @toZ (WordToZ n) q1 = @toZ (WordToZ n) q - 1)
    by (apply division_decrement_positive; exact HQpos).
  pose proof (division_add_balance (S n) r b) as Hsum.
  destruct (@Word.adder (S n) Alg.CoreFunSem (r,b)) as [c t].
  pose proof (word_value_bounds (S n) t) as HT.
  cbn [fst snd] in Hsum |- *. fold q1.
  destruct c as [[] | []].
  - change (word_modulus (S n) * 0 + @toZ (WordToZ (S n)) t =
      @toZ (WordToZ (S n)) r + @toZ (WordToZ (S n)) b) in Hsum.
    assert (Hneg : delta + @toZ (WordToZ (S n)) b < 0) by lia.
    assert (Hpos1 : 0 < @toZ (WordToZ n) q1) by nia.
    assert (Ht : @toZ (WordToZ (S n)) t =
      (delta + @toZ (WordToZ (S n)) b) + word_modulus (S n)) by lia.
    assert (Hnext : 0 <= (delta + @toZ (WordToZ (S n)) b) + @toZ (WordToZ (S n)) b <
      word_modulus (S n)) by lia.
    destruct (div3n2n_loop2_value n t b q1 (delta + @toZ (WordToZ (S n)) b)
      Hpos1 Ht Hnext) as [HQ2 HR2].
    change (@toZ (WordToZ n) (fst (@div3n2n_loop2_spec n Alg.CoreFunSem (t,(q1,b)))) *
      @toZ (WordToZ (S n)) b +
      @toZ (WordToZ (S n)) (snd (@div3n2n_loop2_spec n Alg.CoreFunSem (t,(q1,b)))) =
      @toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + delta /\
      0 <= @toZ (WordToZ (S n)) (snd (@div3n2n_loop2_spec n Alg.CoreFunSem (t,(q1,b)))) <
        @toZ (WordToZ (S n)) b).
    cbv beta iota zeta delta [Ty.tySem Word.Vector] in HQ2, HR2 |- *.
    rewrite HQ2, HR2, Hq1. split; [ring|lia].
  - change (word_modulus (S n) * 1 + @toZ (WordToZ (S n)) t =
      @toZ (WordToZ (S n)) r + @toZ (WordToZ (S n)) b) in Hsum.
    change (@toZ (WordToZ n) q1 * @toZ (WordToZ (S n)) b + @toZ (WordToZ (S n)) t =
      @toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + delta /\
      0 <= @toZ (WordToZ (S n)) t < @toZ (WordToZ (S n)) b).
    rewrite Hq1. split; nia.
Qed.

Lemma div3n2n_loop0_value n (r b : Ty.tySem (Word (S n))) (q : Ty.tySem (Word n)) c delta :
  borrow_word_balance (S n) (c,r) = delta ->
  -2 * @toZ (WordToZ (S n)) b <= delta < @toZ (WordToZ (S n)) b ->
  0 <= @toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + delta ->
  let z := @div3n2n_loop0_spec n Alg.CoreFunSem ((c,r),(q,b)) in
  @toZ (WordToZ n) (fst z) * @toZ (WordToZ (S n)) b +
    @toZ (WordToZ (S n)) (snd z) =
    @toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + delta /\
  0 <= @toZ (WordToZ (S n)) (snd z) < @toZ (WordToZ (S n)) b.
Proof.
  intros HR Hdelta HN. cbn zeta. rewrite div3n2n_loop0_unfold.
  pose proof (word_value_bounds (S n) r) as Hrange.
  unfold borrow_word_balance in HR. cbn [fst snd] in HR.
  destruct c as [[] | []].
  - change (@toZ (WordToZ (S n)) r - word_modulus (S n) * 0 = delta) in HR.
    change (@toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + @toZ (WordToZ (S n)) r =
      @toZ (WordToZ n) q * @toZ (WordToZ (S n)) b + delta /\
      0 <= @toZ (WordToZ (S n)) r < @toZ (WordToZ (S n)) b).
    split; lia.
  - change (@toZ (WordToZ (S n)) r - word_modulus (S n) * 1 = delta) in HR.
    apply div3n2n_loop1_value; lia.
Qed.

Lemma div3n2n_body_unfold n (q rho a3 b1 b2 : Ty.tySem (Word n)) c :
  @div3n2n_body_spec n Alg.CoreFunSem ((c,(q,rho)),(a3,(b1,b2))) =
  let s := @subtract_word_spec Alg.CoreFunSem (S n)
    ((rho,a3),@multiply_word_spec n Alg.CoreFunSem (q,b2)) in
  match c with
  | inl _ => @div3n2n_loop0_spec n Alg.CoreFunSem (s,(q,(b1,b2)))
  | inr _ => (q,snd s)
  end.
Proof. reflexivity. Qed.

Lemma div3n2n_body_value n (q rho a3 b1 b2 : Ty.tySem (Word n)) c delta :
  delta = @toZ (WordToZ n) rho * word_modulus n + @toZ (WordToZ n) a3 -
    @toZ (WordToZ n) q * @toZ (WordToZ n) b2 +
    word_modulus (S n) * @toZ BitToZ c ->
  -2 * @toZ (WordToZ (S n)) (b1,b2) <= delta < @toZ (WordToZ (S n)) (b1,b2) ->
  0 <= @toZ (WordToZ n) q * @toZ (WordToZ (S n)) (b1,b2) + delta ->
  let z := @div3n2n_body_spec n Alg.CoreFunSem ((c,(q,rho)),(a3,(b1,b2))) in
  @toZ (WordToZ n) (fst z) * @toZ (WordToZ (S n)) (b1,b2) +
    @toZ (WordToZ (S n)) (snd z) =
    @toZ (WordToZ n) q * @toZ (WordToZ (S n)) (b1,b2) + delta /\
  0 <= @toZ (WordToZ (S n)) (snd z) < @toZ (WordToZ (S n)) (b1,b2).
Proof.
  intros Hdelta Hbound HN. cbn zeta. rewrite div3n2n_body_unfold.
  set (s := @subtract_word_spec Alg.CoreFunSem (S n)
    ((rho,a3),@multiply_word_spec n Alg.CoreFunSem (q,b2))).
  assert (Hs : borrow_word_balance (S n) s = delta - word_modulus (S n) * @toZ BitToZ c).
  { unfold s. rewrite subtract_word_spec_numeric, multiply_word_spec_numeric.
    change (@toZ (WordToZ n) rho * word_modulus n + @toZ (WordToZ n) a3 -
      @toZ (WordToZ n) q * @toZ (WordToZ n) b2 =
      delta - word_modulus (S n) * @toZ BitToZ c). lia. }
  fold s. destruct s as [borrow r]. destruct c as [[] | []].
  - change (borrow_word_balance (S n) (borrow,r) = delta - word_modulus (S n) * 0) in Hs.
    apply (div3n2n_loop0_value n r (b1,b2) q borrow delta).
    + rewrite Z.mul_0_r, Z.sub_0_r in Hs. exact Hs.
    + exact Hbound.
    + exact HN.
  - change (borrow_word_balance (S n) (borrow,r) = delta - word_modulus (S n) * 1) in Hs.
    pose proof (word_value_bounds (S n) r) as HR.
    pose proof (word_value_bounds (S n) (b1,b2)) as HB.
    unfold borrow_word_balance in Hs. cbn [fst snd] in Hs |- *.
    change (@toZ (WordToZ n) q * @toZ (WordToZ (S n)) (b1,b2) + @toZ (WordToZ (S n)) r =
      @toZ (WordToZ n) q * @toZ (WordToZ (S n)) (b1,b2) + delta /\
      0 <= @toZ (WordToZ (S n)) r < @toZ (WordToZ (S n)) (b1,b2)).
    destruct borrow as [[] | []].
    + change (@toZ (WordToZ (S n)) r - word_modulus (S n) * 0 =
        delta - word_modulus (S n) * 1) in Hs. lia.
    + change (@toZ (WordToZ (S n)) r - word_modulus (S n) * 1 =
        delta - word_modulus (S n) * 1) in Hs. split; lia.
Qed.
