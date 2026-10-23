(** Final short windows for the positive split-scalar wNAF path. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_next C.jet_secp_wnaf_literal_zeros
  C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf_digit C.jet_predicate_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_wnaf_small_odd_digit (word : Ty.tySem (Word 7)) :
  @toZ (WordToZ 7) word<16384 ->
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one ->
  exists (next : Ty.tySem (Word 7)) (digit : Ty.tySem (Word 4)),
    @literal_wnaf15_step Alg.CoreFunSem (Bit.zero,word)=((Bit.zero,next),inr digit) /\
    literal_wnaf_signed16 digit=@toZ (WordToZ 7) word /\ @toZ (WordToZ 7) next=0.
Proof.
  intros Small Odd.
  destruct (literal_wnaf15_odd_next word Odd) as (next & digit & Step & Digit & Next).
  pose proof (word_value_bounds 7 word) as Q.
  assert (D : wnaf_digit ((@toZ (WordToZ 7) word) mod 32768) 15=@toZ (WordToZ 7) word).
  { rewrite Z.mod_small by lia;unfold wnaf_digit,wnaf_carry.
    change (@toZ (WordToZ 7) word-(@toZ (WordToZ 7) word)/16384*32768=@toZ (WordToZ 7) word).
    rewrite Z.div_small by lia;ring. }
  exists next,digit;split;[exact Step|];split;[exact (eq_trans Digit D)|].
  rewrite Next,(eq_trans Digit D),Z.sub_diag;reflexivity.
Qed.

Theorem literal_wnaf_small_odd_run count (word : Ty.tySem (Word 7)) :
  @toZ (WordToZ 7) word<16384 ->
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one ->
  exists (final : Ty.tySem (Word 7)) (digit : Ty.tySem (Word 4)),
    literal_wnaf_run (S count) (Bit.zero,word)=
      ((Bit.zero,final),repeat (inl tt) count++[inr digit]) /\
    literal_wnaf_signed16 digit=@toZ (WordToZ 7) word /\ @toZ (WordToZ 7) final=0.
Proof.
  intros Small Odd.
  destruct (literal_wnaf_small_odd_digit word Small Odd) as (next & digit & Step & Digit & Next).
  destruct (literal_wnaf_zero_power count next 0 ltac:(rewrite Next,Z.mul_0_r;reflexivity))
    as (final & Zeros & Last).
  exists final,digit;split.
  - refine (eq_trans (literal_wnaf_run_step count (Bit.zero,word) (Bit.zero,next) (inr digit) Step) _).
    exact (f_equal (fun p : Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf_digit)=>
      let '(st,digits):=p in (st,digits++[inr digit])) Zeros).
  - split;assumption.
Qed.

Theorem literal_wnaf_last_window n bit width carry (word : Ty.tySem (Word 7)) :
  0<=bit -> 1<=width<=15 -> 0<=n/2^bit<2^(width-1) ->
  (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  exists (final : Ty.tySem (Word 7)) (digit : Ty.tySem (Word 4)),
    literal_wnaf_run (Z.to_nat width) (Bit.zero,word)=
      ((Bit.zero,final),repeat (inl tt) (Z.to_nat (width-1))++[inr digit]) /\
    literal_wnaf_signed16 digit=wnaf_digit (wnaf_word n bit width carry) 15 /\
    @toZ (WordToZ 7) final=0 /\ wnaf_carry (wnaf_word n bit width carry) 15=0.
Proof.
  intros HBit Width Top Carry Different Value.
  assert (Power : 2^(width-1)<=16384).
  { change 16384 with (2^14);apply Z.pow_le_mono_r;lia. }
  destruct (wnaf_word_bounds n bit width carry HBit ltac:(lia) Carry Different) as (Bounds & Odd).
  assert (Trivial : (n/2^bit) mod 2^width=n/2^bit).
  { apply Z.mod_small;split;[lia|].
    assert (2^(width-1)<=2^width) by (apply Z.pow_le_mono_r;lia);lia. }
  assert (Word : wnaf_word n bit width carry=@toZ (WordToZ 7) word).
  { unfold wnaf_word;rewrite Trivial;lia. }
  rewrite Word in Bounds,Odd.
  assert (Small : @toZ (WordToZ 7) word<16384).
  { assert (Max : @toZ (WordToZ 7) word<=16384) by (destruct Carry;lia).
    assert (Not : @toZ (WordToZ 7) word<>16384) by (intro E;rewrite E in Odd;discriminate).
    lia. }
  assert (CarryZero : wnaf_carry (wnaf_word n bit width carry) 15=0).
  { rewrite Word;unfold wnaf_carry;change ((@toZ (WordToZ 7) word)/16384=0);apply Z.div_small;lia. }
  destruct (literal_wnaf_small_odd_run (Z.to_nat (width-1)) word Small
    (wnaf_nonzero_literal_odd n bit carry word Carry Different Value))
    as (final & digit & Run & Digit & Last).
  assert (Count : Z.to_nat width=S (Z.to_nat (width-1))).
  { rewrite <-Z2Nat.inj_succ by lia;f_equal;lia. }
  exists final,digit;split;[rewrite Count;exact Run|];split.
  - rewrite Word;unfold wnaf_digit;rewrite <-Word,CarryZero,Word,Z.mul_0_l,Z.sub_0_r;exact Digit.
  - split;assumption.
Qed.
