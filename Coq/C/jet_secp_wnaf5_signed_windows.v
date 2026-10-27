(** Signed literal zero runs and complete five-bit C windows. Each result
    retains the exact literal digit order and the state at the window end. *)
From Coq Require Import ZArith List Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_signed C.jet_secp_wnaf5_signed
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next C.jet_secp_wnaf5_literal_window
 C.jet_secp_wnaf_digit C.jet_word_bit_spec C.jet_predicate_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_wnaf_shift128 literal_wnaf5_step.

Lemma literal_wnaf_signed_even b word : literal_wnaf_signed_value b word mod 2=0 ->
 @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.zero.
Proof.
 intro Even;rewrite literal_wnaf_signed_parity in Even.
 assert (Test:Z.testbit (@toZ (WordToZ 7) word) 0=Datatypes.false).
 { apply Z.testbit_false;[lia|];change ((@toZ (WordToZ 7) word)/1 mod 2=0).
   rewrite Z.div_1_r;exact Even. }
 pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as BitValue.
 change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
  Z.testbit (@toZ (WordToZ 7) word) 0) in BitValue.
 rewrite Test in BitValue;destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u|u];destruct u;
 [reflexivity|discriminate].
Qed.
Lemma literal_wnaf_signed_odd b word : literal_wnaf_signed_value b word mod 2=1 ->
 @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one.
Proof.
 intro Odd;rewrite literal_wnaf_signed_parity in Odd.
 assert (Test:Z.testbit (@toZ (WordToZ 7) word) 0=Datatypes.true).
 { apply Z.testbit_true;[lia|];change ((@toZ (WordToZ 7) word)/1 mod 2=1).
   rewrite Z.div_1_r;exact Odd. }
 pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as BitValue.
 change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
  Z.testbit (@toZ (WordToZ 7) word) 0) in BitValue.
 rewrite Test in BitValue;destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u|u];destruct u;
 [discriminate|reflexivity].
Qed.

Lemma literal_wnaf5_zero_signed count b word residual :
 literal_wnaf_signed_value b word=2^(Z.of_nat count)*residual ->
 exists final, literal_wnaf5_run count (b,word)=((b,final),repeat (inl tt) count) /\
 literal_wnaf_signed_value b final=residual.
Proof.
 revert word residual;induction count as [|count IH];intros word residual Value.
 - exists word;split;[reflexivity|].
   change (literal_wnaf_signed_value b word=1*residual) in Value;lia.
 - assert (Power:2^(Z.of_nat (S count))=2*2^(Z.of_nat count)).
   { rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia;reflexivity. }
   assert (Even:@Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.zero).
   { apply (literal_wnaf_signed_even b word);rewrite Value,Power.
     replace (2*2^(Z.of_nat count)*residual) with ((2^(Z.of_nat count)*residual)*2) by ring.
     apply Z.mod_mul;lia. }
   set (next:=@literal_wnaf_shift128 Alg.CoreFunSem (b,word)).
   assert (Next:literal_wnaf_signed_value b next=2^(Z.of_nat count)*residual).
   { unfold next;rewrite literal_wnaf_shift_signed,Value,Power.
     symmetry;apply Z.div_unique with (r:=0);[lia|ring]. }
   destruct (IH next residual Next) as (final & Run & Last).
   exists final;split;[|exact Last].
   refine (eq_trans (literal_wnaf5_run_step count (b,word) (b,next) (inl tt)
    (proj1 (literal_wnaf5_even_signed b word Even))) _).
   refine (eq_trans (f_equal (fun p:Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf5_digit)=>
    let '(st,digits):=p in (st,digits++[inl tt])) Run) _).
   f_equal;rewrite <-Nat.add_1_r,repeat_app;reflexivity.
Qed.

Lemma wnaf5_residual_odd n bit carry : (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
 (n/2^bit+carry) mod 2=1.
Proof.
 intros Carry Different;pose proof (Z.mod_pos_bound (n/2^bit) 2 ltac:(lia)) as Low.
 destruct Carry as [C|C];subst carry.
 - rewrite Z.add_0_r;lia.
 - assert (Zero:(n/2^bit) mod 2=0) by lia.
   rewrite Z.add_mod,Zero by lia;reflexivity.
Qed.
Lemma wnaf5_signed_parity sign magnitude : (sign=1 \/ sign= -1) -> magnitude mod 2=1 ->
 (sign*magnitude) mod 2=1.
Proof.
 intros Sign Odd;destruct Sign as [Sgn|Sgn];subst sign;[rewrite Z.mul_1_l;exact Odd|].
 replace (-1*magnitude) with (magnitude+(-magnitude)*2) by ring.
 rewrite Z.mod_add by lia;exact Odd.
Qed.
Lemma wnaf5_signed_digit sign magnitude : (sign=1 \/ sign= -1) -> magnitude mod 2=1 ->
 wnaf_digit ((sign*magnitude) mod 32) 5=sign*wnaf_digit (magnitude mod 32) 5.
Proof.
 intros Sign Odd;destruct Sign as [Sgn|Sgn];subst sign;[rewrite !Z.mul_1_l;reflexivity|].
 replace (-1*magnitude) with (-magnitude) by ring.
 rewrite literal_wnaf5_digit_negates by exact Odd;ring.
Qed.

Theorem literal_wnaf5_window_signed n bit carry sign b word :
 0<=bit -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry -> (sign=1 \/ sign= -1) ->
 literal_wnaf_signed_value b word=sign*(n/2^bit+carry) ->
 exists b' final nib,
 literal_wnaf5_run 5 (b,word)=((b',final),repeat (inl tt) 4++[inr nib]) /\
 literal_wnaf5_value nib=sign*wnaf_digit (wnaf_word n bit 5 carry) 5 /\
 literal_wnaf_signed_value b' final=sign*(n/2^(bit+5)+wnaf_carry (wnaf_word n bit 5 carry) 5).
Proof.
 intros HBit Carry Different Sign Value.
 pose proof (wnaf5_residual_odd n bit carry Carry Different) as MOdd.
 assert (Odd:@Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one).
 { apply (literal_wnaf_signed_odd b word);rewrite Value;apply wnaf5_signed_parity;assumption. }
 destruct (literal_wnaf5_odd_signed b word Odd) as (b' & next & nib & Step & Digit & Next).
 assert (DigitValue:literal_wnaf5_value nib=sign*wnaf_digit (wnaf_word n bit 5 carry) 5).
 { refine (eq_trans Digit _);rewrite Value,(wnaf5_signed_digit sign _ Sign MOdd).
   rewrite (wnaf5_nonzero_residual_word n bit carry HBit Carry Different);reflexivity. }
 set (residual:=n/2^(bit+5)+wnaf_carry (wnaf_word n bit 5 carry) 5).
 pose proof (wnaf_step_preserves_value n bit 5 5 carry HBit ltac:(lia) ltac:(lia) Carry Different) as Equation.
 assert (Power:literal_wnaf_signed_value b' next=2^(Z.of_nat 4)*(sign*residual)).
 { rewrite Next,DigitValue,Value.
   change ((sign*(n/2^bit+carry)-sign*wnaf_digit (wnaf_word n bit 5 carry) 5)/2=16*(sign*residual)).
   change (n/2^bit+carry=wnaf_digit (wnaf_word n bit 5 carry) 5+32*residual) in Equation.
   symmetry;apply Z.div_unique with (r:=0);[lia|rewrite Equation;ring]. }
 destruct (literal_wnaf5_zero_signed 4 b' next (sign*residual) Power) as (final & Zeros & Last).
 exists b',final,nib;split.
 - refine (eq_trans (literal_wnaf5_run_step 4 (b,word) (b',next) (inr nib) Step) _).
   exact (f_equal (fun p:Ty.tySem literal_wnaf_state * list (Ty.tySem literal_wnaf5_digit)=>
    let '(st,digits):=p in (st,digits++[inr nib])) Zeros).
 - split;assumption.
Qed.
