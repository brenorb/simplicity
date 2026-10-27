(** Odd next-state bridge for the window-5 literal wNAF step: an odd state
    word q emits the low nibble n of q/2, whose odd digit 2n+1 (n signed) is
    the C digit [wnaf_digit (q mod 32) 5], and moves to (q - digit)/2. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_state C.jet_secp_wnaf_literal_next
  C.jet_secp_wnaf5_literal C.jet_extend_word_spec C.jet_predicate_spec C.jet_word_bit_spec
  C.jet_int64_bit_mask C.jet_secp_wnaf_digit.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_wnaf_signed4 (nib : Ty.tySem (Word 2)) :=
  @toZ (WordToZ 2) nib-16* @toZ BitToZ (@Word.leftmost Bit 2 Alg.CoreFunSem nib).
(** The odd digit encoded by a window-5 literal nibble. *)
Definition literal_wnaf5_value (nib : Ty.tySem (Word 2)) := 2*literal_wnaf_signed4 nib+1.

Definition literal_wnaf_low4 (word : Ty.tySem (Word 7)) : Ty.tySem (Word 2) :=
  snd (snd (snd (snd (snd word)))).

Lemma literal_wnaf_low4_value word :
  @toZ (WordToZ 2) (literal_wnaf_low4 word)=(@toZ (WordToZ 7) word) mod 16.
Proof.
  destruct word as [a [b [c [d [e f]]]]].
  pose proof (word_value_bounds 2 f) as Low.
  change (0<=@toZ (WordToZ 2) f<16) in Low.
  change (@toZ (WordToZ 2) f=
    (@toZ (WordToZ 6) a*18446744073709551616+
      (@toZ (WordToZ 5) b*4294967296+
        (@toZ (WordToZ 4) c*65536+
          (@toZ (WordToZ 3) d*256+(@toZ (WordToZ 2) e*16+@toZ (WordToZ 2) f))))) mod 16).
  apply Z.mod_unique with (q:=@toZ (WordToZ 6) a*1152921504606846976+
    @toZ (WordToZ 5) b*268435456+@toZ (WordToZ 4) c*4096+@toZ (WordToZ 3) d*16+
    @toZ (WordToZ 2) e);[lia|ring].
Qed.

Lemma literal_wnaf_top4 nib :
  @toZ BitToZ (@Word.leftmost Bit 2 Alg.CoreFunSem nib)=(@toZ (WordToZ 2) nib)/8.
Proof.
  pose proof (word_bit_spec_numeric 2 3 nib ltac:(cbn;lia)) as Top.
  change (Bit.toBool (@Word.leftmost Bit 2 Alg.CoreFunSem nib)=
    Z.testbit (@toZ (WordToZ 2) nib) 3) in Top.
  pose proof (word_value_bounds 2 nib) as Bounds.
  change (0<=@toZ (WordToZ 2) nib<2^4) in Bounds.
  rewrite (top_bit_threshold _ 3 ltac:(lia) Bounds) in Top.
  destruct (@toZ (WordToZ 2) nib <? 2^3) eqn:Small;
    destruct (@Word.leftmost Bit 2 Alg.CoreFunSem nib) as [u|u];destruct u;
    cbn in Top;try discriminate.
  - apply Z.ltb_lt in Small;change (0=@toZ (WordToZ 2) nib/8).
    symmetry;apply Z.div_small;change (2^3) with 8 in Small;lia.
  - apply Z.ltb_ge in Small;change (1=@toZ (WordToZ 2) nib/8).
    change (2^3) with 8 in Small;change (2^4) with 16 in Bounds.
    apply Z.div_unique with (r:=@toZ (WordToZ 2) nib-8);lia.
Qed.

Lemma literal_wnaf_pad4_value high (nib : Ty.tySem (Word 2)) :
  @toZ (WordToZ 7) (@left_pad_word_spec 2 5 high Alg.CoreFunSem nib)=
    @toZ (WordToZ 2) nib+(if high then 2^128-16 else 0).
Proof.
  destruct high.
  - change (18446744073709551615*18446744073709551616+
      (4294967295*4294967296+(65535*65536+(255*256+(15*16+@toZ (WordToZ 2) nib))))=
      @toZ (WordToZ 2) nib+(2^128-16)).
    ring.
  - change (0*18446744073709551616+(0*4294967296+(0*65536+(0*256+(0*16+@toZ (WordToZ 2) nib))))=
      @toZ (WordToZ 2) nib+0);ring.
Qed.

Lemma literal_wnaf_extend4_cases nib :
  @literal_wnaf_extend4 Alg.CoreFunSem nib=
    match @Word.leftmost Bit 2 Alg.CoreFunSem nib with
    | inl _ => @left_pad_word_spec 2 5 Datatypes.false Alg.CoreFunSem nib
    | inr _ => @left_pad_word_spec 2 5 Datatypes.true Alg.CoreFunSem nib
    end.
Proof. reflexivity. Qed.

Lemma literal_wnaf_extend4_value nib :
  @toZ (WordToZ 7) (@literal_wnaf_extend4 Alg.CoreFunSem nib)=
    literal_wnaf_signed4 nib+2^128* @toZ BitToZ (@Word.leftmost Bit 2 Alg.CoreFunSem nib).
Proof.
  pose proof (f_equal (@toZ (WordToZ 7)) (literal_wnaf_extend4_cases nib)) as Cases.
  destruct (@Word.leftmost Bit 2 Alg.CoreFunSem nib) as [u|u] eqn:Top;destruct u.
  - refine (eq_trans Cases (eq_trans (literal_wnaf_pad4_value Datatypes.false nib) _)).
    unfold literal_wnaf_signed4;rewrite Top.
    change (@toZ (WordToZ 2) nib+0=@toZ (WordToZ 2) nib-16*0+2^128*0);ring.
  - refine (eq_trans Cases (eq_trans (literal_wnaf_pad4_value Datatypes.true nib) _)).
    unfold literal_wnaf_signed4;rewrite Top.
    change (@toZ (WordToZ 2) nib+(2^128-16)=@toZ (WordToZ 2) nib-16*1+2^128*1);ring.
Qed.

Lemma literal_wnaf_extend4_top nib :
  @Word.leftmost Bit 7 Alg.CoreFunSem (@literal_wnaf_extend4 Alg.CoreFunSem nib)=
    @Word.leftmost Bit 2 Alg.CoreFunSem nib.
Proof.
  pose proof (f_equal (@Word.leftmost Bit 7 Alg.CoreFunSem) (literal_wnaf_extend4_cases nib)) as Cases.
  destruct (@Word.leftmost Bit 2 Alg.CoreFunSem nib) as [u|u];destruct u;exact Cases.
Qed.

(** The nibble of an odd word encodes exactly the C window-5 digit. *)
Lemma literal_wnaf5_digit_arith q : 0<=q -> q mod 2=1 ->
  2*(((q/2) mod 16)-16*(((q/2) mod 16)/8))+1=wnaf_digit (q mod 32) 5.
Proof.
  intros Q Odd;unfold wnaf_digit,wnaf_carry;change (2^(5-1)) with 16;change (2^5) with 32.
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

Lemma literal_wnaf5_body_shape x :
  @literal_wnaf5_body Alg.CoreFunSem (Bit.zero,x)=
    (@literal_wnaf_sub128 Alg.CoreFunSem
      ((Bit.zero,x),@literal_wnaf_extend4 Alg.CoreFunSem (literal_wnaf_low4 x)),
      inr (literal_wnaf_low4 x)).
Proof. reflexivity. Qed.

Theorem literal_wnaf5_odd_next word :
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one ->
  exists next nib,
    @literal_wnaf5_step Alg.CoreFunSem (Bit.zero,word)=((Bit.zero,next),inr nib) /\
    literal_wnaf5_value nib=wnaf_digit ((@toZ (WordToZ 7) word) mod 32) 5 /\
    @toZ (WordToZ 7) next=(@toZ (WordToZ 7) word-literal_wnaf5_value nib)/2.
Proof.
  intro Odd.
  set (q:=@toZ (WordToZ 7) word).
  pose proof (word_value_bounds 7 word) as Q.
  change (0<=q<2^128) in Q.
  pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as BitValue.
  change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=Z.testbit q 0) in BitValue.
  rewrite Odd in BitValue;change (Datatypes.true=Z.testbit q 0) in BitValue.
  symmetry in BitValue;apply Z.testbit_true in BitValue;[|lia].
  change (q/1 mod 2=1) in BitValue;rewrite Z.div_1_r in BitValue.
  set (x:=@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)).
  assert (X:@toZ (WordToZ 7) x=q/2).
  { unfold x;rewrite literal_wnaf_shift128_value;change ((0*2^128+q)/2=q/2);reflexivity. }
  set (nib:=literal_wnaf_low4 x).
  assert (N:@toZ (WordToZ 2) nib=(q/2) mod 16) by (unfold nib;rewrite literal_wnaf_low4_value,X;reflexivity).
  assert (Digit:literal_wnaf5_value nib=wnaf_digit (q mod 32) 5).
  { unfold literal_wnaf5_value,literal_wnaf_signed4;rewrite literal_wnaf_top4,N.
    apply literal_wnaf5_digit_arith;lia. }
  set (y:=@literal_wnaf_extend4 Alg.CoreFunSem nib).
  assert (Difference:@toZ (WordToZ 7) x-@toZ (WordToZ 7) y+
      2^128* @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem y)=(q-literal_wnaf5_value nib)/2).
  { unfold y;rewrite literal_wnaf_extend4_value,literal_wnaf_extend4_top,X.
    unfold literal_wnaf5_value.
    generalize (literal_wnaf_signed4 nib) (@toZ BitToZ (@Word.leftmost Bit 2 Alg.CoreFunSem nib));
      intros sv tv.
    assert (Half:q/2=(q-1)/2).
    { pose proof (Z.div_mod q 2 ltac:(lia));apply Z.div_unique with (r:=0);lia. }
    assert (Shift:(q-(2*sv+1))/2=(q-1)/2-sv).
    { replace (q-(2*sv+1)) with ((q-1)+(-sv)*2) by ring.
      rewrite Z.div_add by lia;ring. }
    rewrite Shift,Half;ring. }
  assert (Range:0<=(q-literal_wnaf5_value nib)/2<2^128).
  { rewrite Digit;unfold wnaf_digit,wnaf_carry;change (2^(5-1)) with 16;change (2^5) with 32.
    pose proof (Z.mod_pos_bound q 32 ltac:(lia)) as M.
    pose proof (Z.div_mod q 32 ltac:(lia)) as D.
    assert (Cr:0<=(q mod 32)/16<2) by (split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia).
    pose proof (Z.div_mod (q mod 32) 16 ltac:(lia)) as D16.
    pose proof (Z.mod_pos_bound (q mod 32) 16 ltac:(lia)) as M16.
    split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia]. }
  destruct (literal_wnaf_sub128_positive x y ltac:(rewrite Difference;exact Range)) as (next & Sub & Value).
  exists next,nib;split.
  - assert (Step:@literal_wnaf5_step Alg.CoreFunSem (Bit.zero,word)=
      @literal_wnaf5_body Alg.CoreFunSem (Bit.zero,x)).
    { unfold literal_wnaf5_step.
      change ((match @Word.rightmost Bit 7 Alg.CoreFunSem word with
        | inl _ => ((Bit.zero,x),inl tt)
        | inr _ => @literal_wnaf5_body Alg.CoreFunSem (Bit.zero,x)
        end)=@literal_wnaf5_body Alg.CoreFunSem (Bit.zero,x)).
      rewrite Odd;reflexivity. }
    refine (eq_trans Step (eq_trans (literal_wnaf5_body_shape x) _)).
    exact (f_equal (fun s=>(s,inr nib)) Sub).
  - split;[exact Digit|exact (eq_trans Value Difference)].
Qed.
