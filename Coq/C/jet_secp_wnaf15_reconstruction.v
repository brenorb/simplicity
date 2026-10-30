(** Arithmetic for reconstruction of the actual positive window-15 stream. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_next C.jet_secp_wnaf_literal_values
 C.jet_secp_wnaf_literal_mask C.jet_secp_wnaf_literal_array C.jet_secp_wnaf5_reconstruction
 C.jet_secp_wnaf5_signed C.jet_secp_wnaf_digit C.jet_predicate_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition secp_wnaf15_next (q:Z):=
 if q mod 2 =? 0 then q/2 else (q-wnaf_digit (q mod 32768) 15)/2.
Lemma secp_wnaf15_small_digit q:-16384<q<16384 ->wnaf_digit (q mod 32768) 15=q.
Proof.
 intro Small;change (q mod 32768-q mod 32768/16384*32768=q).
 destruct (Z_le_dec 0 q) as [Nonnegative|Negative].
 - rewrite Z.mod_small by lia;rewrite Z.div_small by lia;ring.
 - assert (Remainder:q mod 32768=q+32768).
   { symmetry;apply Z.mod_unique with (q:= -1);[left;lia|ring]. }
   rewrite Remainder.
   assert (Quotient:(q+32768)/16384=1).
   { symmetry;apply Z.div_unique with (r:=q+16384);[left;lia|ring]. }
   rewrite Quotient;ring.
Qed.
Lemma secp_wnaf15_next_bound (k:nat) q:
 -2^Z.of_nat (S k)<=q<=2^Z.of_nat (S k) ->
 -2^Z.of_nat k<=secp_wnaf15_next q<=2^Z.of_nat k.
Proof.
 intro Bound;unfold secp_wnaf15_next;destruct (q mod 2 =? 0) eqn:Even.
 - assert (Power:2^Z.of_nat (S k)=2*2^Z.of_nat k).
   { rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;ring. }
   rewrite Power in Bound;split;[apply Z.div_le_lower_bound|apply Z.div_le_upper_bound];lia.
 - apply Z.eqb_neq in Even.
   assert (Odd:q mod 2=1) by (pose proof (Z.mod_pos_bound q 2 ltac:(lia));lia).
   destruct (Nat.lt_ge_cases k 14) as [SmallK|LargeK].
   + assert (Power:2^Z.of_nat (S k)<=16384).
     { change 16384 with (2^14);apply Z.pow_le_mono_r;lia. }
     assert (Small:-16384<q<16384).
     { assert (Lower:q<> -16384) by (intro E;rewrite E in Odd;discriminate).
       assert (Upper:q<>16384) by (intro E;rewrite E in Odd;discriminate).
       lia. }
     rewrite secp_wnaf15_small_digit by exact Small;rewrite Z.sub_diag,Z.div_0_l by lia.
     pose proof (Z.pow_nonneg 2 (Z.of_nat k) ltac:(lia));lia.
   + set (u:=2^(Z.of_nat k-14)).
     assert (Power:2^Z.of_nat k=16384*u).
     { unfold u;replace (Z.of_nat k) with (14+(Z.of_nat k-14)) at 1 by lia.
       rewrite Z.pow_add_r by lia;reflexivity. }
     assert (PowerNext:2^Z.of_nat (S k)=32768*u).
     { rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;rewrite Power;ring. }
     rewrite PowerNext in Bound.
     pose proof (Z.div_mod q 32768 ltac:(lia)) as Division.
     pose proof (Z.mod_pos_bound q 32768 ltac:(lia)) as Remainder.
     pose proof (Z.div_mod (q mod 32768) 16384 ltac:(lia)) as CarryDivision.
     pose proof (Z.mod_pos_bound (q mod 32768) 16384 ltac:(lia)) as CarryRemainder.
     assert (Carry:0<=q mod 32768/16384<=1).
     { lia. }
     assert (Quotient:(q-wnaf_digit (q mod 32768) 15)/2=16384*(q/32768+q mod 32768/16384)).
     { change ((q-(q mod 32768-q mod 32768/16384*32768))/2=16384*(q/32768+q mod 32768/16384)).
       symmetry;apply Z.div_unique with (r:=0);[left;lia|nia]. }
     rewrite Quotient,Power;lia.
Qed.
Local Opaque literal_wnaf15_step literal_wnaf_signed16.
Theorem secp_wnaf15_positive_step (word:Ty.tySem (Word 7)):
 exists (next:Ty.tySem (Word 7)) (digit:Ty.tySem literal_wnaf_digit),
 @literal_wnaf15_step Alg.CoreFunSem (Bit.zero,word)=((Bit.zero,next),digit) /\
 @toZ (WordToZ 7) word=2*@toZ (WordToZ 7) next+wnaf_literal_value digit /\
 @toZ (WordToZ 7) next=secp_wnaf15_next (@toZ (WordToZ 7) word).
Proof.
 pose proof (secp_wnaf5_low_bit Bit.zero word) as Parity.
 rewrite literal_wnaf_signed_parity in Parity.
 change (@toZ (WordToZ 7) word mod 2=@toZ BitToZ (@Word.rightmost Bit 7 Alg.CoreFunSem word)) in Parity.
 pose proof (Z.div_mod (@toZ (WordToZ 7) word) 2 ltac:(lia)) as Division.
 destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u|u] eqn:Low;destruct u.
 - change (@toZ (WordToZ 7) word mod 2=0) in Parity.
   exists (@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)),(inl tt).
   split;[apply literal_wnaf15_even;exact Low|].
   pose proof (literal_wnaf_shift128_value Bit.zero word) as Shift.
   change (@toZ (WordToZ 7) (@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word))=
    (0*2^128+@toZ (WordToZ 7) word)/2) in Shift.
   rewrite Shift;cbn [wnaf_literal_value];unfold secp_wnaf15_next;rewrite Parity.
   rewrite Z.mul_0_l,Z.add_0_l;split;[lia|reflexivity].
 - change (@toZ (WordToZ 7) word mod 2=1) in Parity.
   destruct (literal_wnaf15_odd_next word Low) as (next & digit & Step & Digit & Next).
   exists next,(inr digit);split;[exact Step|].
   cbn [wnaf_literal_value];split.
   + pose proof (wnaf_literal_odd_value_bounds (@toZ (WordToZ 7) word) Parity) as [DigitOdd _].
     rewrite <-Digit in DigitOdd.
     assert (Remainder:(@toZ (WordToZ 7) word-literal_wnaf_signed16 digit) mod 2=0).
     { rewrite Zminus_mod,Parity,DigitOdd;reflexivity. }
     pose proof (Z.div_mod (@toZ (WordToZ 7) word-literal_wnaf_signed16 digit) 2 ltac:(lia)) as Difference.
     rewrite Next;lia.
   + rewrite Next,Digit;unfold secp_wnaf15_next;rewrite Parity;reflexivity.
Qed.
Require Import C.jet_secp_wnaf_literal_zeros.
Definition secp_wnaf15_digit_fold (a:Z) (digit:Ty.tySem literal_wnaf_digit):=
 2*a+wnaf_literal_value digit.
Theorem secp_wnaf15_run_reconstruct count (word:Ty.tySem (Word 7)):
 exists (final:Ty.tySem (Word 7)) digits,
 literal_wnaf_run count (Bit.zero,word)=((Bit.zero,final),digits) /\
 @toZ (WordToZ 7) word=fold_left secp_wnaf15_digit_fold digits (@toZ (WordToZ 7) final) /\
 (-2^Z.of_nat count<=@toZ (WordToZ 7) word<=2^Z.of_nat count ->
  -1<=@toZ (WordToZ 7) final<=1).
Proof.
 revert word;induction count as [|count IH];intro word.
 - exists word,[];split;[reflexivity|];split;[reflexivity|exact (fun Range=>Range)].
 - destruct (secp_wnaf15_positive_step word) as (next & digit & Step & Balance & Next).
   destruct (IH next) as (final & digits & Run & Value & Bound).
   exists final,(digits++[digit]);split.
   + rewrite (literal_wnaf_run_step count _ _ _ Step),Run;reflexivity.
   + split.
     * rewrite fold_left_app;cbn [fold_left secp_wnaf15_digit_fold];rewrite <-Value;exact Balance.
     * intro Range;apply Bound;rewrite Next;apply secp_wnaf15_next_bound;exact Range.
Qed.
Lemma secp_wnaf15_next_small_zero q:-1<=q<=1 ->secp_wnaf15_next q=0.
Proof.
 intro Range;assert (Cases:q= -1 \/ q=0 \/ q=1) by lia.
 destruct Cases as [EqLeft | [EqZero | EqRight]];subst q;reflexivity.
Qed.
Theorem secp_wnaf15_run129_zero_payload (word:Ty.tySem (Word 7)):
 @toZ (WordToZ 7) (snd (fst (literal_wnaf_run 129 (Bit.zero,word))))=0.
Proof.
 destruct (secp_wnaf15_run_reconstruct 128 word) as (middle & digits & Run & Value & Bound).
 assert (Capacity:-2^Z.of_nat 128<=@toZ (WordToZ 7) word<=2^Z.of_nat 128).
 { pose proof (word_value_bounds 7 word) as Range;change (0<=@toZ (WordToZ 7) word<2^128) in Range.
   change (Z.of_nat 128) with 128;lia. }
 specialize (Bound Capacity).
 destruct (secp_wnaf15_positive_step middle) as (next & digit & Step & Balance & Next).
 change (@toZ (WordToZ 7) (snd (fst (literal_wnaf_run (128+1)%nat (Bit.zero,word))))=0).
 rewrite literal_wnaf_run_add,Run.
 cbn [literal_wnaf_run];rewrite Step;cbn [fst snd].
 rewrite Next;apply secp_wnaf15_next_small_zero;exact Bound.
Qed.
Theorem secp_wnaf15_digits_reconstruct (word:Ty.tySem (Word 7)):
 fold_left secp_wnaf15_digit_fold (literal_wnaf15_digits (Bit.zero,word)) 0=@toZ (WordToZ 7) word.
Proof.
 destruct (secp_wnaf15_run_reconstruct 129 word) as (final & digits & Run & Value & Bound).
 pose proof (secp_wnaf15_run129_zero_payload word) as Zero;rewrite Run in Zero;cbn [fst snd] in Zero.
 rewrite Zero in Value.
 assert (Digits:literal_wnaf15_digits (Bit.zero,word)=digits).
 { rewrite <-literal_wnaf15_digits_order,Run;reflexivity. }
 rewrite Digits;symmetry;exact Value.
Qed.
