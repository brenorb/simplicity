(** Literal zero runs corresponding to C window jumps. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_next C.jet_secp_wnaf_literal_mask.
Require Import C.jet_secp_wnaf_digit.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_wnaf_run_step count state next digit :
  @literal_wnaf15_step Alg.CoreFunSem state=(next,digit) ->
  literal_wnaf_run (S count) state=
    let '(final,digits):=literal_wnaf_run count next in (final,digits++[digit]).
Proof.
  intro Step.
  exact (f_equal (fun p : Ty.tySem (Ty.Prod literal_wnaf_state literal_wnaf_digit)=>
    let '(next,digit):=p in let '(final,digits):=literal_wnaf_run count next in
      (final,digits++[digit])) Step).
Qed.

Lemma literal_wnaf_zero_power count (word : Ty.tySem (Word 7)) residual :
  @toZ (WordToZ 7) word=2^(Z.of_nat count)*residual ->
  exists final : Ty.tySem (Word 7),
    literal_wnaf_run count (Bit.zero,word)=((Bit.zero,final),repeat (inl tt) count) /\
    @toZ (WordToZ 7) final=residual.
Proof.
  revert word residual;induction count as [|count IH];intros word residual Value.
  - exists word;split;[reflexivity|].
    change (@toZ (WordToZ 7) word=1*residual) in Value;rewrite Z.mul_1_l in Value;exact Value.
  - assert (Power : 2^(Z.of_nat (S count))=2*2^(Z.of_nat count)).
    { rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;reflexivity. }
    assert (Even : Z.testbit (@toZ (WordToZ 7) word) 0=Datatypes.false).
    { rewrite Value,Power.
      replace (2*2^(Z.of_nat count)*residual) with (2*(2^(Z.of_nat count)*residual)) by ring.
      apply Z.testbit_even_0. }
    pose (next:=@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)).
    assert (Next : @toZ (WordToZ 7) next=2^(Z.of_nat count)*residual).
    { unfold next;rewrite literal_wnaf_shift128_value.
      change ((0*2^128+@toZ (WordToZ 7) word)/2=2^(Z.of_nat count)*residual).
      rewrite Z.mul_0_l,Z.add_0_l,Value,Power.
      symmetry;apply Z.div_unique with (r:=0);[lia|ring]. }
    destruct (IH next residual Next) as (final & Run & Last).
    exists final;split;[|exact Last].
    refine (eq_trans (literal_wnaf_run_step count (Bit.zero,word) (Bit.zero,next) (inl tt)
      (literal_wnaf15_even_numeric Bit.zero word Even)) _).
    refine (eq_trans (f_equal (fun p : Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf_digit)=>
      let '(st,digits):=p in (st,digits++[inl tt])) Run) _).
    f_equal.
    rewrite <-Nat.add_1_r,repeat_app;reflexivity.
Qed.

Theorem literal_wnaf_window15 n bit carry (word : Ty.tySem (Word 7)) :
  0<=bit -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  exists (final : Ty.tySem (Word 7)) (digit : Ty.tySem (Word 4)),
    literal_wnaf_run 15 (Bit.zero,word)=
      ((Bit.zero,final),repeat (inl tt) 14++[inr digit]) /\
    literal_wnaf_signed16 digit=wnaf_digit (wnaf_word n bit 15 carry) 15 /\
    @toZ (WordToZ 7) final=n/2^(bit+15)+wnaf_carry (wnaf_word n bit 15 carry) 15.
Proof.
  intros HBit Carry Different Value.
  destruct (literal_wnaf15_odd_next word (wnaf_nonzero_literal_odd n bit carry word Carry Different Value))
    as (next & digit & Step & Digit & Next).
  assert (DigitValue : literal_wnaf_signed16 digit=wnaf_digit (wnaf_word n bit 15 carry) 15).
  { refine (eq_trans Digit (f_equal (fun z=>wnaf_digit z 15) _)).
    refine (eq_trans (f_equal (fun z=>z mod 32768) Value) _).
    apply wnaf_nonzero_residual_word;assumption. }
  pose (residual:=n/2^(bit+15)+wnaf_carry (wnaf_word n bit 15 carry) 15).
  pose proof (wnaf_step_preserves_value n bit 15 15 carry HBit ltac:(lia) ltac:(lia) Carry Different) as Equation.
  assert (Power : @toZ (WordToZ 7) next=2^(Z.of_nat 14)*residual).
  { rewrite Next,DigitValue,Value.
    change ((n/2^bit+carry-wnaf_digit (wnaf_word n bit 15 carry) 15)/2=16384*residual).
    change (n/2^bit+carry=wnaf_digit (wnaf_word n bit 15 carry) 15+32768*residual) in Equation.
    symmetry;apply Z.div_unique with (r:=0);lia. }
  destruct (literal_wnaf_zero_power 14 next residual Power) as (final & Zeros & Last).
  exists final,digit;split.
  - refine (eq_trans (literal_wnaf_run_step 14 (Bit.zero,word) (Bit.zero,next) (inr digit) Step) _).
    exact (f_equal (fun p : Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf_digit)=>
      let '(st,digits):=p in (st,digits++[inr digit])) Zeros).
  - split;assumption.
Qed.
