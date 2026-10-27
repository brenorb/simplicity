(** Signed window-5 transitions of the unchanged literal wNAF program.
    Negative split-lambda halves need these transitions before composing
    the original C loop; positive-state lemmas alone do not cover them. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_next
 C.jet_secp_wnaf_literal_signed C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next
 C.jet_secp_wnaf5_literal_window C.jet_secp_wnaf_digit C.jet_word_bit_spec C.jet_predicate_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_wnaf_shift128 literal_wnaf_sub128 literal_wnaf_extend4.

Lemma literal_wnaf_signed_range b w : -2^128<=literal_wnaf_signed_value b w<2^128.
Proof.
 pose proof (word_value_bounds 7 w) as Bound.
 change (0<=@toZ (WordToZ 7) w<2^128) in Bound.
 unfold literal_wnaf_signed_value;destruct b as [u|u];destruct u;
  [change (@toZ BitToZ (inl tt)) with 0|change (@toZ BitToZ (inr tt)) with 1];lia.
Qed.
Lemma literal_wnaf_signed_parity b w :
 literal_wnaf_signed_value b w mod 2=@toZ (WordToZ 7) w mod 2.
Proof.
 unfold literal_wnaf_signed_value.
 replace (@toZ (WordToZ 7) w-2^128* @toZ BitToZ b) with
  (@toZ (WordToZ 7) w+(- @toZ BitToZ b*2^127)*2) by ring.
 rewrite Z.mod_add by lia;reflexivity.
Qed.
Lemma literal_wnaf_shift_signed b w :
 literal_wnaf_signed_value b (@literal_wnaf_shift128 Alg.CoreFunSem (b,w))=
 literal_wnaf_signed_value b w/2.
Proof.
 unfold literal_wnaf_signed_value;rewrite literal_wnaf_shift128_value.
 change ((@toZ BitToZ b*2^128+@toZ (WordToZ 7) w)/2-2^128* @toZ BitToZ b=
  (@toZ (WordToZ 7) w-2^128* @toZ BitToZ b)/2).
 replace (@toZ BitToZ b*2^128+@toZ (WordToZ 7) w) with
  (@toZ (WordToZ 7) w+(@toZ BitToZ b*2^127)*2) by ring.
 replace (@toZ (WordToZ 7) w-2^128* @toZ BitToZ b) with
  (@toZ (WordToZ 7) w+(- @toZ BitToZ b*2^127)*2) by ring.
 rewrite !Z.div_add by lia;ring.
Qed.
Lemma literal_wnaf_low4_signed b w :
 @toZ (WordToZ 2) (literal_wnaf_low4 w)=literal_wnaf_signed_value b w mod 16.
Proof.
 rewrite literal_wnaf_low4_value;unfold literal_wnaf_signed_value.
 replace (@toZ (WordToZ 7) w-2^128* @toZ BitToZ b) with
  (@toZ (WordToZ 7) w+(- @toZ BitToZ b*2^124)*16) by ring.
 rewrite Z.mod_add by lia;reflexivity.
Qed.
Lemma literal_wnaf_signed4_range nib : -8<=literal_wnaf_signed4 nib<8.
Proof.
 pose proof (word_value_bounds 2 nib) as Range;change (0<=@toZ (WordToZ 2) nib<16) in Range.
 unfold literal_wnaf_signed4;rewrite literal_wnaf_top4.
 pose proof (Z.div_mod (@toZ (WordToZ 2) nib) 8 ltac:(lia)) as Div.
 pose proof (Z.mod_pos_bound (@toZ (WordToZ 2) nib) 8 ltac:(lia)) as Mod.
 assert (Cases:@toZ (WordToZ 2) nib/8=0 \/ @toZ (WordToZ 2) nib/8=1).
 { assert (0<=@toZ (WordToZ 2) nib/8<2) by
   (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia);lia. }
 destruct Cases;lia.
Qed.
Lemma literal_wnaf5_signed_digit_arith q : q mod 2=1 ->
 2*(((q/2) mod 16)-16*(((q/2) mod 16)/8))+1=wnaf_digit (q mod 32) 5.
Proof.
 intro Odd;unfold wnaf_digit,wnaf_carry;change (2^(5-1)) with 16;change (2^5) with 32.
 set (t:=(q/2) mod 16).
 assert (T:0<=t<16) by (apply Z.mod_pos_bound;lia).
 assert (R:q mod 32=2*t+1).
 { pose proof (Z.div_mod q 2 ltac:(lia)) as D2.
   pose proof (Z.div_mod (q/2) 16 ltac:(lia)) as D16.
   rewrite Z.div_div in D16 by lia;change (2*16) with 32 in D16.
   symmetry;apply Z.mod_unique with (q:=q/32);[lia|unfold t;lia]. }
 rewrite R.
 assert (C:(2*t+1)/16=t/8).
 { pose proof (Z.div_mod t 8 ltac:(lia)) as D8.
   assert (0<=t mod 8<8) by (apply Z.mod_pos_bound;lia).
   symmetry;apply Z.div_unique with (r:=2*(t mod 8)+1);lia. }
 rewrite C;ring.
Qed.
Lemma literal_wnaf_extend4_signed nib :
 literal_wnaf_signed_value (@Word.leftmost Bit 7 Alg.CoreFunSem
  (@literal_wnaf_extend4 Alg.CoreFunSem nib)) (@literal_wnaf_extend4 Alg.CoreFunSem nib)=
 literal_wnaf_signed4 nib.
Proof.
 unfold literal_wnaf_signed_value;rewrite literal_wnaf_extend4_value,literal_wnaf_extend4_top;ring.
Qed.
Lemma literal_wnaf5_body_signed_shape b x :
 @literal_wnaf5_body Alg.CoreFunSem (b,x)=
 (@literal_wnaf_sub128 Alg.CoreFunSem ((b,x),
  @literal_wnaf_extend4 Alg.CoreFunSem (literal_wnaf_low4 x)),inr (literal_wnaf_low4 x)).
Proof. reflexivity. Qed.

Theorem literal_wnaf5_odd_signed b word :
 @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one ->
 exists b' next nib,
 @literal_wnaf5_step Alg.CoreFunSem (b,word)=((b',next),inr nib) /\
 literal_wnaf5_value nib=wnaf_digit (literal_wnaf_signed_value b word mod 32) 5 /\
 literal_wnaf_signed_value b' next=(literal_wnaf_signed_value b word-literal_wnaf5_value nib)/2.
Proof.
 intro Odd;set (q:=literal_wnaf_signed_value b word).
 pose proof (literal_wnaf_signed_range b word) as Q;fold q in Q.
 assert (Parity:q mod 2=1).
 { unfold q;rewrite literal_wnaf_signed_parity.
   pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as BitValue.
   change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
    Z.testbit (@toZ (WordToZ 7) word) 0) in BitValue.
   rewrite Odd in BitValue;change (Datatypes.true=Z.testbit (@toZ (WordToZ 7) word) 0) in BitValue.
   symmetry in BitValue;apply Z.testbit_true in BitValue;[|lia].
   rewrite Z.div_1_r in BitValue;exact BitValue. }
 set (x:=@literal_wnaf_shift128 Alg.CoreFunSem (b,word)).
 set (nib:=literal_wnaf_low4 x).
 assert (X:literal_wnaf_signed_value b x=q/2) by (apply literal_wnaf_shift_signed).
 assert (N:@toZ (WordToZ 2) nib=(q/2) mod 16).
 { unfold nib;rewrite (literal_wnaf_low4_signed b x),X;reflexivity. }
 assert (Digit:literal_wnaf5_value nib=wnaf_digit (q mod 32) 5).
 { unfold literal_wnaf5_value,literal_wnaf_signed4;rewrite literal_wnaf_top4,N.
   apply literal_wnaf5_signed_digit_arith;exact Parity. }
 set (y:=@literal_wnaf_extend4 Alg.CoreFunSem nib).
 assert (Difference:literal_wnaf_signed_value b x-
   literal_wnaf_signed_value (@Word.leftmost Bit 7 Alg.CoreFunSem y) y=
   (q-literal_wnaf5_value nib)/2).
 { unfold y;rewrite literal_wnaf_extend4_signed,X;unfold literal_wnaf5_value.
   pose proof (Z.div_mod q 2 ltac:(lia)) as Divide;rewrite Parity in Divide.
   replace (q-(2*literal_wnaf_signed4 nib+1)) with
    ((q-1)+(-literal_wnaf_signed4 nib)*2) by ring.
   rewrite Z.div_add by lia.
   assert (Half:q/2=(q-1)/2) by (apply Z.div_unique with (r:=0);lia).
   rewrite Half;ring. }
 assert (Range:-2^128<=literal_wnaf_signed_value b x-
   literal_wnaf_signed_value (@Word.leftmost Bit 7 Alg.CoreFunSem y) y<2^128).
 { unfold y;rewrite literal_wnaf_extend4_signed,X.
   pose proof (literal_wnaf_signed4_range nib) as D.
   assert (Half:-2^127<=q/2<2^127) by
    (split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];lia).
   clear -Half D;lia. }
 destruct (literal_wnaf_sub128_signed b x y Range) as (b' & next & Sub & Value).
 exists b',next,nib;split.
 - assert (Step:@literal_wnaf5_step Alg.CoreFunSem (b,word)=@literal_wnaf5_body Alg.CoreFunSem (b,x)).
   { unfold literal_wnaf5_step;change
     ((match @Word.rightmost Bit 7 Alg.CoreFunSem word with
       | inl _=>((b,x),inl tt) | inr _=>@literal_wnaf5_body Alg.CoreFunSem (b,x) end)=
        @literal_wnaf5_body Alg.CoreFunSem (b,x));rewrite Odd;reflexivity. }
   refine (eq_trans Step (eq_trans (literal_wnaf5_body_signed_shape b x) _)).
   exact (f_equal (fun s=>(s,inr nib)) Sub).
 - split;[exact Digit|exact (eq_trans Value Difference)].
Qed.

Theorem literal_wnaf5_even_signed b word :
 @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.zero ->
 @literal_wnaf5_step Alg.CoreFunSem (b,word)=
  ((b,@literal_wnaf_shift128 Alg.CoreFunSem (b,word)),inl tt) /\
 literal_wnaf_signed_value b (@literal_wnaf_shift128 Alg.CoreFunSem (b,word))=
  literal_wnaf_signed_value b word/2.
Proof. intro Even;split;[apply literal_wnaf5_even;exact Even|apply literal_wnaf_shift_signed]. Qed.

(** C computes positive-magnitude digits and multiplies its stores by sign.
    This identity connects that negative branch to the literal signed digit. *)
Theorem literal_wnaf5_digit_negates q : q mod 2=1 ->
 wnaf_digit ((-q) mod 32) 5= -wnaf_digit (q mod 32) 5.
Proof.
 intro Odd;set (r:=q mod 32).
 assert (R:0<=r<32) by (apply Z.mod_pos_bound;lia).
 pose proof (Z.div_mod q 32 ltac:(lia)) as Divide;fold r in Divide.
 assert (Parity:r mod 2=1).
 { replace q with (r+(q/32*16)*2) in Odd by lia.
   rewrite Z.mod_add in Odd by lia;exact Odd. }
 assert (Nonzero:r<>0) by (intro E;rewrite E in Parity;discriminate).
 assert (NotMiddle:r<>16) by (intro E;rewrite E in Parity;discriminate).
 assert (Opp:(-q) mod 32=32-r).
 { symmetry;apply Z.mod_unique with (q:= -(q/32)-1);lia. }
 unfold wnaf_digit,wnaf_carry;change (2^(5-1)) with 16;change (2^5) with 32.
 fold r;rewrite Opp.
 destruct (Z_lt_ge_dec r 16) as [Small|Large].
 - assert (D:r/16=0) by (apply Z.div_small;lia).
   assert (E:(32-r)/16=1) by (symmetry;apply Z.div_unique with (r:=16-r);lia).
   rewrite D,E;ring.
 - assert (D:r/16=1) by (symmetry;apply Z.div_unique with (r:=r-16);lia).
   assert (E:(32-r)/16=0) by (apply Z.div_small;lia).
   rewrite D,E;ring.
Qed.
