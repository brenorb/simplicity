(** Numeric observations of the literal full_left/right_shift1 programs.
    Their base item may itself be a word, as in division normalization.
    These representation bridges are internal, not C jet coverage. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Util.Arith.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint vector_bits (T : ToZ.type) n : nat :=
  match n with O => ToZ.Theory.bitSize T | S n => (vector_bits T n + vector_bits T n)%nat end.
Fixpoint vector_value (T : ToZ.type) n : Ty.tySem (Vector T n) -> Z :=
  match n return Ty.tySem (Vector T n) -> Z with
  | O => fun x => @toZ T x
  | S n => fun x => vector_value T n (fst x) * two_power_nat (vector_bits T n) +
      vector_value T n (snd x)
  end.

Lemma vector_modulus_positive (T : ToZ.type) n : 0 < two_power_nat (vector_bits T n).
Proof. rewrite two_power_nat_equiv. apply Z.pow_pos_nonneg; lia. Qed.

Lemma vector_value_range (T : ToZ.type) n (v : Ty.tySem (Vector T n)) :
  0 <= vector_value T n v < two_power_nat (vector_bits T n).
Proof.
  revert v. induction n as [|n IH]; intros v.
  - change (0 <= @toZ T v < two_power_nat (ToZ.Theory.bitSize T)).
    rewrite (@toZ_mod T v).
    apply Z.mod_pos_bound. apply vector_modulus_positive with (n := 0%nat).
  - destruct v as [hi lo]. pose proof (IH hi) as HH; pose proof (IH lo) as HL.
    pose proof (vector_modulus_positive T n) as HP.
    cbn [vector_value vector_bits fst snd]. rewrite two_power_nat_plus. nia.
Qed.

Lemma full_left_shift1_value (T : ToZ.type) n (v : Ty.tySem (Vector T n)) (x : Ty.tySem T) :
  let result := @Word.full_left_shift1 T n Alg.CoreFunSem (v,x) in
  vector_value T n v * two_power_nat (ToZ.Theory.bitSize T) + @toZ T x =
    @toZ T (fst result) * two_power_nat (vector_bits T n) + vector_value T n (snd result).
Proof.
  revert v x. induction n as [|n IH]; intros v x.
  - reflexivity.
  - destruct v as [hi lo].
    pose proof (IH lo x) as HL.
    destruct (@Word.full_left_shift1 T n Alg.CoreFunSem (lo,x)) as [middle last] eqn:EL.
    pose proof (IH hi middle) as HH.
    destruct (@Word.full_left_shift1 T n Alg.CoreFunSem (hi,middle)) as [first front] eqn:EH.
    cbn [fst snd] in HL, HH.
    cbn [Word.full_left_shift1 Word.build_full_left_shift1].
    cbn -[Word.full_left_shift1 vector_value vector_bits toZ].
    rewrite EL. cbn [fst snd]. rewrite EH.
    change ((vector_value T n hi * two_power_nat (vector_bits T n) + vector_value T n lo) *
      two_power_nat (ToZ.Theory.bitSize T) + @toZ T x =
      @toZ T first * two_power_nat (vector_bits T (S n)) +
      (vector_value T n front * two_power_nat (vector_bits T n) + vector_value T n last)).
    cbn [vector_bits]. rewrite two_power_nat_plus. nia.
Qed.

Lemma full_right_shift1_value (T : ToZ.type) n (x : Ty.tySem T) (v : Ty.tySem (Vector T n)) :
  let result := @Word.full_right_shift1 T n Alg.CoreFunSem (x,v) in
  @toZ T x * two_power_nat (vector_bits T n) + vector_value T n v =
    vector_value T n (fst result) * two_power_nat (ToZ.Theory.bitSize T) + @toZ T (snd result).
Proof.
  revert x v. induction n as [|n IH]; intros x v.
  - reflexivity.
  - destruct v as [hi lo].
    pose proof (IH x hi) as HH.
    destruct (@Word.full_right_shift1 T n Alg.CoreFunSem (x,hi)) as [front middle] eqn:EH.
    pose proof (IH middle lo) as HL.
    destruct (@Word.full_right_shift1 T n Alg.CoreFunSem (middle,lo)) as [last final] eqn:EL.
    cbn [fst snd] in HH, HL.
    cbn [Word.full_right_shift1 Word.build_full_right_shift1].
    cbn -[Word.full_right_shift1 vector_value vector_bits toZ].
    rewrite EH. cbn [fst snd]. rewrite EL.
    change (@toZ T x * two_power_nat (vector_bits T (S n)) +
      (vector_value T n hi * two_power_nat (vector_bits T n) + vector_value T n lo) =
      (vector_value T n front * two_power_nat (vector_bits T n) + vector_value T n last) *
      two_power_nat (ToZ.Theory.bitSize T) + @toZ T final).
    cbn [vector_bits]. rewrite two_power_nat_plus. nia.
Qed.

Lemma full_left_shift1_quotient (T : ToZ.type) n v x :
  @toZ T (fst (@Word.full_left_shift1 T n Alg.CoreFunSem (v,x))) =
    (vector_value T n v * two_power_nat (ToZ.Theory.bitSize T) + @toZ T x) /
      two_power_nat (vector_bits T n).
Proof.
  pose proof (full_left_shift1_value T n v x) as H.
  eapply Z.div_unique with (r := vector_value T n
    (snd (@Word.full_left_shift1 T n Alg.CoreFunSem (v,x)))).
  - left; apply vector_value_range.
  - cbn zeta in H. rewrite (Z.mul_comm (two_power_nat (vector_bits T n))). exact H.
Qed.

Lemma full_left_shift1_remainder (T : ToZ.type) n v x :
  vector_value T n (snd (@Word.full_left_shift1 T n Alg.CoreFunSem (v,x))) =
    (vector_value T n v * two_power_nat (ToZ.Theory.bitSize T) + @toZ T x) mod
      two_power_nat (vector_bits T n).
Proof.
  pose proof (full_left_shift1_value T n v x) as H.
  eapply Z.mod_unique with (q := @toZ T
    (fst (@Word.full_left_shift1 T n Alg.CoreFunSem (v,x)))).
  - left; apply vector_value_range.
  - cbn zeta in H. rewrite (Z.mul_comm (two_power_nat (vector_bits T n))). exact H.
Qed.

Lemma full_right_shift1_quotient (T : ToZ.type) n x v :
  vector_value T n (fst (@Word.full_right_shift1 T n Alg.CoreFunSem (x,v))) =
    (@toZ T x * two_power_nat (vector_bits T n) + vector_value T n v) /
      two_power_nat (ToZ.Theory.bitSize T).
Proof.
  pose proof (full_right_shift1_value T n x v) as H.
  eapply Z.div_unique with (r := @toZ T
    (snd (@Word.full_right_shift1 T n Alg.CoreFunSem (x,v)))).
  - left; apply (vector_value_range T 0%nat).
  - cbn zeta in H. rewrite (Z.mul_comm (two_power_nat (ToZ.Theory.bitSize T))). exact H.
Qed.

Lemma full_right_shift1_remainder (T : ToZ.type) n x v :
  @toZ T (snd (@Word.full_right_shift1 T n Alg.CoreFunSem (x,v))) =
    (@toZ T x * two_power_nat (vector_bits T n) + vector_value T n v) mod
      two_power_nat (ToZ.Theory.bitSize T).
Proof.
  pose proof (full_right_shift1_value T n x v) as H.
  eapply Z.mod_unique with (q := vector_value T n
    (fst (@Word.full_right_shift1 T n Alg.CoreFunSem (x,v)))).
  - left; apply (vector_value_range T 0%nat).
  - cbn zeta in H. rewrite (Z.mul_comm (two_power_nat (ToZ.Theory.bitSize T))). exact H.
Qed.
