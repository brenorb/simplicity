(** Window-5 literal zero runs and full windows corresponding to C window
    jumps, mirroring [jet_secp_wnaf_literal_zeros] for window 15. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf5_literal
  C.jet_secp_wnaf5_literal_next C.jet_word_bit_spec C.jet_secp_wnaf_digit.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_wnaf5_even_numeric bit word :
  Z.testbit (@toZ (WordToZ 7) word) 0=Datatypes.false ->
  @literal_wnaf5_step Alg.CoreFunSem (bit,word)=
    ((bit,@literal_wnaf_shift128 Alg.CoreFunSem (bit,word)),inl tt).
Proof.
  intro Even;apply literal_wnaf5_even.
  pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as HBit.
  change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
    Z.testbit (@toZ (WordToZ 7) word) 0) in HBit.
  rewrite Even in HBit;destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u | u];destruct u;
    [reflexivity|discriminate].
Qed.

Lemma literal_wnaf5_run_step count state next digit :
  @literal_wnaf5_step Alg.CoreFunSem state=(next,digit) ->
  literal_wnaf5_run (S count) state=
    let '(final,digits):=literal_wnaf5_run count next in (final,digits++[digit]).
Proof.
  intro Step.
  exact (f_equal (fun p : Ty.tySem (Ty.Prod literal_wnaf_state literal_wnaf5_digit)=>
    let '(next,digit):=p in let '(final,digits):=literal_wnaf5_run count next in
      (final,digits++[digit])) Step).
Qed.

Lemma literal_wnaf5_zero_power count (word : Ty.tySem (Word 7)) residual :
  @toZ (WordToZ 7) word=2^(Z.of_nat count)*residual ->
  exists final : Ty.tySem (Word 7),
    literal_wnaf5_run count (Bit.zero,word)=((Bit.zero,final),repeat (inl tt) count) /\
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
    refine (eq_trans (literal_wnaf5_run_step count (Bit.zero,word) (Bit.zero,next) (inl tt)
      (literal_wnaf5_even_numeric Bit.zero word Even)) _).
    refine (eq_trans (f_equal (fun p : Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf5_digit)=>
      let '(st,digits):=p in (st,digits++[inl tt])) Run) _).
    f_equal.
    rewrite <-Nat.add_1_r,repeat_app;reflexivity.
Qed.

Lemma wnaf5_nonzero_residual_word n bit carry :
  0<=bit -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  (n/2^bit+carry) mod 32=wnaf_word n bit 5 carry.
Proof.
  intros HBit Carry Different.
  pose proof (wnaf_word_bounds n bit 5 carry HBit ltac:(lia) Carry Different) as Bounds.
  destruct Bounds as [Bounds Odd].
  change (0<wnaf_word n bit 5 carry<32) in Bounds.
  rewrite <-Z.add_mod_idemp_l by lia.
  change ((wnaf_word n bit 5 carry) mod 32=wnaf_word n bit 5 carry).
  apply Z.mod_small;lia.
Qed.

(** A full five-bit C window: one literal digit then four zero steps. *)
Theorem literal_wnaf_window5 n bit carry (word : Ty.tySem (Word 7)) :
  0<=bit -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  exists (final : Ty.tySem (Word 7)) (nib : Ty.tySem (Word 2)),
    literal_wnaf5_run 5 (Bit.zero,word)=
      ((Bit.zero,final),repeat (inl tt) 4++[inr nib]) /\
    literal_wnaf5_value nib=wnaf_digit (wnaf_word n bit 5 carry) 5 /\
    @toZ (WordToZ 7) final=n/2^(bit+5)+wnaf_carry (wnaf_word n bit 5 carry) 5.
Proof.
  intros HBit Carry Different Value.
  destruct (literal_wnaf5_odd_next word (wnaf_nonzero_literal_odd n bit carry word Carry Different Value))
    as (next & nib & Step & Digit & Next).
  assert (DigitValue : literal_wnaf5_value nib=wnaf_digit (wnaf_word n bit 5 carry) 5).
  { refine (eq_trans Digit (f_equal (fun z=>wnaf_digit z 5) _)).
    refine (eq_trans (f_equal (fun z=>z mod 32) Value) _).
    apply wnaf5_nonzero_residual_word;assumption. }
  pose (residual:=n/2^(bit+5)+wnaf_carry (wnaf_word n bit 5 carry) 5).
  pose proof (wnaf_step_preserves_value n bit 5 5 carry HBit ltac:(lia) ltac:(lia) Carry Different) as Equation.
  assert (Power : @toZ (WordToZ 7) next=2^(Z.of_nat 4)*residual).
  { rewrite Next,DigitValue,Value.
    change ((n/2^bit+carry-wnaf_digit (wnaf_word n bit 5 carry) 5)/2=16*residual).
    change (n/2^bit+carry=wnaf_digit (wnaf_word n bit 5 carry) 5+32*residual) in Equation.
    symmetry;apply Z.div_unique with (r:=0);lia. }
  destruct (literal_wnaf5_zero_power 4 next residual Power) as (final & Zeros & Last).
  exists final,nib;split.
  - refine (eq_trans (literal_wnaf5_run_step 4 (Bit.zero,word) (Bit.zero,next) (inr nib) Step) _).
    exact (f_equal (fun p : Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf5_digit)=>
      let '(st,digits):=p in (st,digits++[inr nib])) Zeros).
  - split;assumption.
Qed.
