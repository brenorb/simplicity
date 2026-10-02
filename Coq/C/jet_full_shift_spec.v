(** Typed adapters for Programs.Word.full_shift at word-sized block boundaries.
    The actual programs are Word.full_left/right_shift1; the casts only identify
    vectorComp's nested type with the ordinary Word type. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Word Simplicity.Alg.
Require Import C.jet_vector_shift_word.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition pair_type_eq A B C D (e : A = C) (f : B = D) :
  Ty.Prod A B = Ty.Prod C D.
Proof. destruct e, f; reflexivity. Defined.

Fixpoint vector_word_eq n m : Vector (Word n) m = Word (m + n) :=
  match m as m return Vector (Word n) m = Word (m + n) with
  | Datatypes.O => eq_refl
  | Datatypes.S k => pair_type_eq _ _ _ _ (vector_word_eq n k) (vector_word_eq n k)
  end.

Lemma cast_pair_value A B C D (e : A = C) (f : B = D)
    (a : Ty.tySem A) (b : Ty.tySem B) :
  eq_rect (Ty.Prod A B) Ty.tySem (a,b) (Ty.Prod C D) (pair_type_eq A B C D e f) =
    (eq_rect A Ty.tySem a C e, eq_rect B Ty.tySem b D f).
Proof. destruct e, f; reflexivity. Qed.

Lemma vector_word_bits n m :
  vector_bits (WordToZ n) m = ToZ.Theory.bitSize (WordToZ (m + n)).
Proof.
  induction m as [|m IH]; [reflexivity|].
  change (vector_bits (WordToZ n) m + vector_bits (WordToZ n) m =
    ToZ.Theory.bitSize (WordToZ (m+n)) + ToZ.Theory.bitSize (WordToZ (m+n)))%nat.
  now rewrite IH.
Qed.

Lemma vector_word_value n m (v : Ty.tySem (Vector (Word n) m)) :
  @toZ (WordToZ (m+n))
    (eq_rect (Vector (Word n) m) Ty.tySem v (Word (m+n)) (vector_word_eq n m)) =
    vector_value (WordToZ n) m v.
Proof.
  induction m as [|m IH]; [reflexivity|].
  destruct v as [hi lo].
  change (@toZ (WordToZ (S (m+n)))
    (eq_rect (Ty.Prod (Vector (Word n) m) (Vector (Word n) m)) Ty.tySem (hi,lo)
      (Ty.Prod (Word (m+n)) (Word (m+n)))
      (pair_type_eq _ _ _ _ (vector_word_eq n m) (vector_word_eq n m))) =
    vector_value (WordToZ n) (S m) (hi,lo)).
  rewrite cast_pair_value.
  change (@toZ (WordToZ (m+n))
    (eq_rect _ Ty.tySem hi _ (vector_word_eq n m)) *
    two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))) +
    @toZ (WordToZ (m+n)) (eq_rect _ Ty.tySem lo _ (vector_word_eq n m)) =
    vector_value (WordToZ n) m hi * two_power_nat (vector_bits (WordToZ n) m) +
    vector_value (WordToZ n) m lo).
  rewrite !IH, vector_word_bits. reflexivity.
Qed.

Definition full_left_word_spec n m {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word (m+n)) (Word n)) (Ty.Prod (Word n) (Word (m+n))) :=
  eq_rect (Vector (Word n) m)
    (fun V => term (Ty.Prod V (Word n)) (Ty.Prod (Word n) V))
    (@Word.full_left_shift1 (Word n) m term) (Word (m+n)) (vector_word_eq n m).

Definition full_right_word_spec n m {term : Alg.Core.Algebra} :
  term (Ty.Prod (Word n) (Word (m+n))) (Ty.Prod (Word (m+n)) (Word n)) :=
  eq_rect (Vector (Word n) m)
    (fun V => term (Ty.Prod (Word n) V) (Ty.Prod V (Word n)))
    (@Word.full_right_shift1 (Word n) m term) (Word (m+n)) (vector_word_eq n m).

Lemma full_left_word_spec_parametric n m : Alg.Core.Parametric (@full_left_word_spec n m).
Proof.
  intros term1 term2 R. unfold full_left_word_spec.
  generalize (vector_word_eq n m). generalize (Word (m+n)).
  intros V e. destruct e. apply Word.full_left_shift1_Parametric.
Qed.

Lemma full_right_word_spec_parametric n m : Alg.Core.Parametric (@full_right_word_spec n m).
Proof.
  intros term1 term2 R. unfold full_right_word_spec.
  generalize (vector_word_eq n m). generalize (Word (m+n)).
  intros V e. destruct e. apply Word.full_right_shift1_Parametric.
Qed.

Lemma cast_value_inverse A B (e : A = B) (v : Ty.tySem B) :
  eq_rect A Ty.tySem (eq_rect B Ty.tySem v A (eq_sym e)) B e = v.
Proof. destruct e; reflexivity. Qed.

Lemma cast_full_left_core A B C (e : A = C)
    (f : Ty.Arrow (Ty.Prod A B) (Ty.Prod B A)) (v : Ty.tySem A) (x : Ty.tySem B) :
  (eq_rect A (fun V => Ty.Arrow (Ty.Prod V B) (Ty.Prod B V)) f C e)
    (eq_rect A Ty.tySem v C e, x) =
  (fst (f (v,x)), eq_rect A Ty.tySem (snd (f (v,x))) C e).
Proof. destruct e. cbn. destruct (f (v,x)); reflexivity. Qed.

Lemma cast_full_right_core A B C (e : A = C)
    (f : Ty.Arrow (Ty.Prod B A) (Ty.Prod A B)) (x : Ty.tySem B) (v : Ty.tySem A) :
  (eq_rect A (fun V => Ty.Arrow (Ty.Prod B V) (Ty.Prod V B)) f C e)
    (x, eq_rect A Ty.tySem v C e) =
  (eq_rect A Ty.tySem (fst (f (x,v))) C e, snd (f (x,v))).
Proof. destruct e. cbn. destruct (f (x,v)); reflexivity. Qed.

Lemma full_left_word_spec_core n m v x :
  @full_left_word_spec n m Alg.CoreFunSem
    (eq_rect _ Ty.tySem v _ (vector_word_eq n m), x) =
  (fst (@Word.full_left_shift1 (Word n) m Alg.CoreFunSem (v,x)),
    eq_rect _ Ty.tySem (snd (@Word.full_left_shift1 (Word n) m Alg.CoreFunSem (v,x)))
      _ (vector_word_eq n m)).
Proof. unfold full_left_word_spec. apply cast_full_left_core. Qed.

Lemma full_right_word_spec_core n m x v :
  @full_right_word_spec n m Alg.CoreFunSem
    (x, eq_rect _ Ty.tySem v _ (vector_word_eq n m)) =
  (eq_rect _ Ty.tySem (fst (@Word.full_right_shift1 (Word n) m Alg.CoreFunSem (x,v)))
      _ (vector_word_eq n m),
    snd (@Word.full_right_shift1 (Word n) m Alg.CoreFunSem (x,v))).
Proof. unfold full_right_word_spec. apply cast_full_right_core. Qed.

Lemma full_left_word_spec_value n m (v : Ty.tySem (Word (m+n))) (x : Ty.tySem (Word n)) :
  let result := @full_left_word_spec n m Alg.CoreFunSem (v,x) in
  @toZ (WordToZ (m+n)) v * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
    @toZ (WordToZ n) x =
  @toZ (WordToZ n) (fst result) * two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))) +
    @toZ (WordToZ (m+n)) (snd result).
Proof.
  set (u := eq_rect _ Ty.tySem v _ (eq_sym (vector_word_eq n m))).
  assert (HV : vector_value (WordToZ n) m u = @toZ (WordToZ (m+n)) v).
  { rewrite <- vector_word_value. unfold u. rewrite cast_value_inverse. reflexivity. }
  pose proof (full_left_shift1_value (WordToZ n) m u x) as Hvalue.
  cbn zeta in Hvalue |- *. rewrite HV in Hvalue.
  pose proof (full_left_word_spec_core n m u x) as HS.
  unfold u in HS at 1. rewrite cast_value_inverse in HS.
  pose proof (f_equal (fun r : Ty.tySem (Ty.Prod (Word n) (Word (m+n))) =>
    @toZ (WordToZ n) (fst r) * two_power_nat (vector_bits (WordToZ n) m) +
    @toZ (WordToZ (m+n)) (snd r)) HS) as Hobs.
  cbn [fst snd] in Hobs. rewrite vector_word_value in Hobs.
  rewrite <- vector_word_bits. etransitivity; [exact Hvalue|symmetry; exact Hobs].
Qed.

Lemma full_right_word_spec_value n m (x : Ty.tySem (Word n)) (v : Ty.tySem (Word (m+n))) :
  let result := @full_right_word_spec n m Alg.CoreFunSem (x,v) in
  @toZ (WordToZ n) x * two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))) +
    @toZ (WordToZ (m+n)) v =
  @toZ (WordToZ (m+n)) (fst result) * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
    @toZ (WordToZ n) (snd result).
Proof.
  set (u := eq_rect _ Ty.tySem v _ (eq_sym (vector_word_eq n m))).
  assert (HV : vector_value (WordToZ n) m u = @toZ (WordToZ (m+n)) v).
  { rewrite <- vector_word_value. unfold u. rewrite cast_value_inverse. reflexivity. }
  pose proof (full_right_shift1_value (WordToZ n) m x u) as Hvalue.
  cbn zeta in Hvalue |- *. rewrite HV in Hvalue.
  pose proof (full_right_word_spec_core n m x u) as HS.
  unfold u in HS at 1. rewrite cast_value_inverse in HS.
  pose proof (f_equal (fun r : Ty.tySem (Ty.Prod (Word (m+n)) (Word n)) =>
    @toZ (WordToZ (m+n)) (fst r) * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
    @toZ (WordToZ n) (snd r)) HS) as Hobs.
  cbn [fst snd] in Hobs. rewrite vector_word_value in Hobs.
  rewrite <- vector_word_bits. etransitivity; [exact Hvalue|symmetry; exact Hobs].
Qed.

Lemma full_left_word_spec_quotient n m v x :
  @toZ (WordToZ n) (fst (@full_left_word_spec n m Alg.CoreFunSem (v,x))) =
    (@toZ (WordToZ (m+n)) v * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) x) / two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))).
Proof.
  pose proof (full_left_word_spec_value n m v x) as Hvalue.
  eapply Z.div_unique with (r := @toZ (WordToZ (m+n))
    (snd (@full_left_word_spec n m Alg.CoreFunSem (v,x)))).
  - left; apply (vector_value_range (WordToZ (m+n)) 0%nat).
  - cbn zeta in Hvalue.
    rewrite (Z.mul_comm (two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))))).
    exact Hvalue.
Qed.

Lemma full_left_word_spec_remainder n m v x :
  @toZ (WordToZ (m+n)) (snd (@full_left_word_spec n m Alg.CoreFunSem (v,x))) =
    (@toZ (WordToZ (m+n)) v * two_power_nat (ToZ.Theory.bitSize (WordToZ n)) +
      @toZ (WordToZ n) x) mod two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))).
Proof.
  pose proof (full_left_word_spec_value n m v x) as Hvalue.
  eapply Z.mod_unique with (q := @toZ (WordToZ n)
    (fst (@full_left_word_spec n m Alg.CoreFunSem (v,x)))).
  - left; apply (vector_value_range (WordToZ (m+n)) 0%nat).
  - cbn zeta in Hvalue.
    rewrite (Z.mul_comm (two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))))).
    exact Hvalue.
Qed.

Lemma full_right_word_spec_quotient n m x v :
  @toZ (WordToZ (m+n)) (fst (@full_right_word_spec n m Alg.CoreFunSem (x,v))) =
    (@toZ (WordToZ n) x * two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))) +
      @toZ (WordToZ (m+n)) v) / two_power_nat (ToZ.Theory.bitSize (WordToZ n)).
Proof.
  pose proof (full_right_word_spec_value n m x v) as Hvalue.
  eapply Z.div_unique with (r := @toZ (WordToZ n)
    (snd (@full_right_word_spec n m Alg.CoreFunSem (x,v)))).
  - left; apply (vector_value_range (WordToZ n) 0%nat).
  - cbn zeta in Hvalue.
    rewrite (Z.mul_comm (two_power_nat (ToZ.Theory.bitSize (WordToZ n)))). exact Hvalue.
Qed.

Lemma full_right_word_spec_remainder n m x v :
  @toZ (WordToZ n) (snd (@full_right_word_spec n m Alg.CoreFunSem (x,v))) =
    (@toZ (WordToZ n) x * two_power_nat (ToZ.Theory.bitSize (WordToZ (m+n))) +
      @toZ (WordToZ (m+n)) v) mod two_power_nat (ToZ.Theory.bitSize (WordToZ n)).
Proof.
  pose proof (full_right_word_spec_value n m x v) as Hvalue.
  eapply Z.mod_unique with (q := @toZ (WordToZ (m+n))
    (fst (@full_right_word_spec n m Alg.CoreFunSem (x,v)))).
  - left; apply (vector_value_range (WordToZ n) 0%nat).
  - cbn zeta in Hvalue.
    rewrite (Z.mul_comm (two_power_nat (ToZ.Theory.bitSize (WordToZ n)))). exact Hvalue.
Qed.
