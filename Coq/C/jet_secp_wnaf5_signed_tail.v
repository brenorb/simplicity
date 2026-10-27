(** Signed final partial windows. The magnitude bound is a property of the
    current scalar quotient, not a restriction to positive literal states. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_signed C.jet_secp_wnaf5_signed
 C.jet_secp_wnaf5_signed_windows C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next
 C.jet_secp_wnaf5_literal_window C.jet_secp_wnaf_digit.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem literal_wnaf5_last_signed n bit width carry sign b word :
 0<=bit -> 1<=width<=4 -> 0<=n/2^bit<2^width ->
 (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry -> (sign=1 \/ sign= -1) ->
 literal_wnaf_signed_value b word=sign*(n/2^bit+carry) ->
 exists b' final nib,
 literal_wnaf5_run (Z.to_nat width) (b,word)=
  ((b',final),repeat (inl tt) (Z.to_nat (width-1))++[inr nib]) /\
 literal_wnaf5_value nib=sign*wnaf_digit (wnaf_word n bit width carry) 5 /\
 literal_wnaf_signed_value b' final=0 /\ wnaf_carry (wnaf_word n bit width carry) 5=0.
Proof.
 intros HBit Width Top Carry Different Sign Value.
 set (magnitude:=n/2^bit+carry).
 assert (Word:wnaf_word n bit width carry=magnitude).
 { unfold wnaf_word,magnitude;rewrite Z.mod_small by exact Top;reflexivity. }
 destruct (wnaf_word_bounds n bit width carry HBit ltac:(lia) Carry Different) as [Bounds MOdd].
 rewrite Word in Bounds,MOdd.
 assert (Power:2^width<=16) by (change 16 with (2^4);apply Z.pow_le_mono_r;lia).
 assert (Small:0<magnitude<16) by lia.
 assert (CarryZero:wnaf_carry (wnaf_word n bit width carry) 5=0).
 { rewrite Word;unfold wnaf_carry;change (magnitude/16=0);apply Z.div_small;lia. }
 assert (CDigit:wnaf_digit (wnaf_word n bit width carry) 5=magnitude).
 { unfold wnaf_digit;rewrite CarryZero,Word,Z.mul_0_l,Z.sub_0_r;reflexivity. }
 assert (Odd:@Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one).
 { apply (literal_wnaf_signed_odd b word);rewrite Value;fold magnitude.
   apply wnaf5_signed_parity;assumption. }
 destruct (literal_wnaf5_odd_signed b word Odd) as (b' & next & nib & Step & Digit & Next).
 assert (DigitValue:literal_wnaf5_value nib=sign*magnitude).
 { refine (eq_trans Digit _);rewrite Value;fold magnitude.
   rewrite (wnaf5_signed_digit sign magnitude Sign MOdd),Z.mod_small by lia.
   unfold wnaf_digit,wnaf_carry;change (sign*(magnitude-magnitude/16*32)=sign*magnitude).
   rewrite Z.div_small by lia;ring. }
 assert (NextZero:literal_wnaf_signed_value b' next=0).
 { rewrite Next,DigitValue,Value;fold magnitude;rewrite Z.sub_diag;reflexivity. }
 destruct (literal_wnaf5_zero_signed (Z.to_nat (width-1)) b' next 0
  ltac:(rewrite NextZero,Z.mul_0_r;reflexivity)) as (final & Zeros & Last).
 assert (Count:Z.to_nat width=S (Z.to_nat (width-1))).
 { rewrite <-Z2Nat.inj_succ by lia;f_equal;lia. }
 exists b',final,nib;split.
 - rewrite Count;refine (eq_trans (literal_wnaf5_run_step (Z.to_nat (width-1))
    (b,word) (b',next) (inr nib) Step) _).
   exact (f_equal (fun p:Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf5_digit)=>
    let '(st,digits):=p in (st,digits++[inr nib])) Zeros).
 - split;[rewrite CDigit;exact DigitValue|];split;assumption.
Qed.

(** Covers every clamp selected by the 129-bit, window-5 C loop, including
    magnitude 2^128 when it has a signed literal representation. *)
Theorem literal_wnaf5_split_signed n bit carry sign b word :
 0<=n<2^129 -> 0<=bit<129 -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
 (sign=1 \/ sign= -1) -> literal_wnaf_signed_value b word=sign*(n/2^bit+carry) ->
 let width:=Z.min 5 (129-bit) in exists b' final nib,
 literal_wnaf5_run (Z.to_nat width) (b,word)=
  ((b',final),repeat (inl tt) (Z.to_nat (width-1))++[inr nib]) /\
 literal_wnaf5_value nib=sign*wnaf_digit (wnaf_word n bit width carry) 5 /\
 literal_wnaf_signed_value b' final=sign*(n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) 5).
Proof.
 intros N HBit Carry Different Sign Value;cbv zeta.
 destruct (Z_le_dec 5 (129-bit)) as [Full|Tail].
 - rewrite Z.min_l by lia;exact (literal_wnaf5_window_signed n bit carry sign b word
    ltac:(lia) Carry Different Sign Value).
 - rewrite Z.min_r by lia.
   pose proof (wnaf_top_quotient_bound n bit 130 ltac:(lia) N) as Top.
   replace (130-bit-1) with (129-bit) in Top by lia.
   destruct (literal_wnaf5_last_signed n bit (129-bit) carry sign b word
    ltac:(lia) ltac:(lia) Top Carry Different Sign Value)
    as (b' & final & nib & Run & Digit & Last & CarryZero).
   exists b',final,nib;split;[exact Run|];split;[exact Digit|].
   rewrite Last,CarryZero;replace (bit+(129-bit)) with 129 by lia.
   rewrite Z.div_small by exact N;ring.
Qed.
