(** Odd next-state bridge for generate's positive split scalars. *)
From Coq Require Import ZArith Lia.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_state C.jet_secp_wnaf_literal_mask
  C.jet_extend_word_spec C.jet_predicate_spec C.jet_word_bit_spec C.jet_int64_bit_mask C.jet_secp_wnaf_digit.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma literal_wnaf_pad16_value high (word : Ty.tySem (Word 4)) :
  @toZ (WordToZ 7) (@left_pad_word_spec 4 3 high Alg.CoreFunSem word)=
    @toZ (WordToZ 4) word+(if high then 2^128-65536 else 0).
Proof.
  destruct high.
  - change (18446744073709551615*18446744073709551616+
      (4294967295*4294967296+(65535*65536+@toZ (WordToZ 4) word))=
      @toZ (WordToZ 4) word+(2^128-65536)).
    ring.
  - change (0*18446744073709551616+(0*4294967296+(0*65536+@toZ (WordToZ 4) word))=
      @toZ (WordToZ 4) word+0);ring.
Qed.

Lemma literal_wnaf_half_sub a b :
  a mod 2=b mod 2 -> a/2-b/2=(a-b)/2.
Proof.
  intro Parity.
  pose proof (Z.div_mod a 2 ltac:(lia)) as A.
  pose proof (Z.div_mod b 2 ltac:(lia)) as B.
  apply Z.div_unique with (r:=0);lia.
Qed.

Lemma literal_wnaf_extend16_cases word :
  @literal_wnaf_extend16 Alg.CoreFunSem word=
    match @Word.leftmost Bit 4 Alg.CoreFunSem word with
    | inl _ => @left_pad_word_spec 4 3 Datatypes.false Alg.CoreFunSem word
    | inr _ => @left_pad_word_spec 4 3 Datatypes.true Alg.CoreFunSem word
    end.
Proof. reflexivity. Qed.

Lemma literal_wnaf_extend16_value word :
  @toZ (WordToZ 7) (@literal_wnaf_extend16 Alg.CoreFunSem word)=
    literal_wnaf_signed16 word+2^128* @toZ BitToZ (@Word.leftmost Bit 4 Alg.CoreFunSem word).
Proof.
  pose proof (f_equal (@toZ (WordToZ 7)) (literal_wnaf_extend16_cases word)) as Cases.
  destruct (@Word.leftmost Bit 4 Alg.CoreFunSem word) as [u|u] eqn:Top;destruct u.
  - refine (eq_trans Cases (eq_trans (literal_wnaf_pad16_value Datatypes.false word) _)).
    unfold literal_wnaf_signed16;rewrite Top.
    change (@toZ (WordToZ 4) word+0=@toZ (WordToZ 4) word-65536*0+2^128*0);ring.
  - refine (eq_trans Cases (eq_trans (literal_wnaf_pad16_value Datatypes.true word) _)).
    unfold literal_wnaf_signed16;rewrite Top.
    change (@toZ (WordToZ 4) word+(2^128-65536)=@toZ (WordToZ 4) word-65536*1+2^128*1);ring.
Qed.

Lemma literal_wnaf_pad16_top high word :
  @Word.leftmost Bit 7 Alg.CoreFunSem (@left_pad_word_spec 4 3 high Alg.CoreFunSem word)=
    if high then Bit.one else Bit.zero.
Proof. destruct high;reflexivity. Qed.

Lemma literal_wnaf_extend16_top word :
  @Word.leftmost Bit 7 Alg.CoreFunSem (@literal_wnaf_extend16 Alg.CoreFunSem word)=
    @Word.leftmost Bit 4 Alg.CoreFunSem word.
Proof.
  pose proof (f_equal (@Word.leftmost Bit 7 Alg.CoreFunSem) (literal_wnaf_extend16_cases word)) as Cases.
  destruct (@Word.leftmost Bit 4 Alg.CoreFunSem word) as [u|u];destruct u;
    exact (eq_trans Cases (literal_wnaf_pad16_top _ word)).
Qed.

Lemma literal_wnaf_top128 word :
  @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem word)=
    (@toZ (WordToZ 7) word)/2^127.
Proof.
  pose proof (word_bit_spec_numeric 7 127 word ltac:(cbn;lia)) as Top.
  change (Bit.toBool (@Word.leftmost Bit 7 Alg.CoreFunSem word)=
    Z.testbit (@toZ (WordToZ 7) word) 127) in Top.
  pose proof (word_value_bounds 7 word) as Bounds.
  change (0<=@toZ (WordToZ 7) word<2^128) in Bounds.
  rewrite (top_bit_threshold _ 127 ltac:(lia) Bounds) in Top.
  destruct (@toZ (WordToZ 7) word <? 2^127) eqn:Small;
    destruct (@Word.leftmost Bit 7 Alg.CoreFunSem word) as [u|u];destruct u;
    cbn in Top;try discriminate.
  - apply Z.ltb_lt in Small;change (0=@toZ (WordToZ 7) word/2^127).
    symmetry;apply Z.div_small;lia.
  - apply Z.ltb_ge in Small;change (1=@toZ (WordToZ 7) word/2^127).
    apply Z.div_unique with (r:=@toZ (WordToZ 7) word-2^127);lia.
Qed.

Definition literal_wnaf_digit_half word :=
  let extended:=@literal_wnaf_extend16 Alg.CoreFunSem word in
  @literal_wnaf_shift128 Alg.CoreFunSem (@Word.leftmost Bit 7 Alg.CoreFunSem extended,extended).

Lemma literal_wnaf_digit_half_value word :
  @toZ (WordToZ 7) (literal_wnaf_digit_half word)=
    literal_wnaf_signed16 word/2+
      2^128* @toZ BitToZ (@Word.leftmost Bit 4 Alg.CoreFunSem word).
Proof.
  unfold literal_wnaf_digit_half;rewrite literal_wnaf_shift128_value,literal_wnaf_extend16_top,
    literal_wnaf_extend16_value.
  assert (Numerator : @toZ BitToZ (@Word.leftmost Bit 4 Alg.CoreFunSem word)*2^128+
    (literal_wnaf_signed16 word+2^128* @toZ BitToZ (@Word.leftmost Bit 4 Alg.CoreFunSem word))
    = (literal_wnaf_signed16 word+(2^128* @toZ BitToZ (@Word.leftmost Bit 4 Alg.CoreFunSem word))*2)) by ring.
  refine (eq_trans (f_equal (fun z=>z/2) Numerator) _).
  apply Z.div_add;lia.
Qed.

Lemma literal_wnaf_digit_half_top word :
  @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem (literal_wnaf_digit_half word))=
    @toZ BitToZ (@Word.leftmost Bit 4 Alg.CoreFunSem word).
Proof.
  pose proof (word_value_bounds 4 word) as Small.
  change (0<=@toZ (WordToZ 4) word<65536) in Small.
  pose proof (word_value_bounds 7 (@literal_wnaf_extend16 Alg.CoreFunSem word)) as Extended.
  change (0<=@toZ (WordToZ 7) (@literal_wnaf_extend16 Alg.CoreFunSem word)<2^128) in Extended.
  rewrite literal_wnaf_extend16_value in Extended.
  rewrite literal_wnaf_top128,literal_wnaf_digit_half_value.
  unfold literal_wnaf_signed16 in *.
  destruct (@Word.leftmost Bit 4 Alg.CoreFunSem word) as [u|u];destruct u.
  - change (0<=@toZ (WordToZ 4) word-65536*0+2^128*0<2^128) in Extended.
    change (((@toZ (WordToZ 4) word-65536*0)/2+2^128*0)/2^127=0).
    rewrite !Z.mul_0_r,Z.sub_0_r,Z.add_0_r.
    apply Z.div_small;split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;lia].
  - change (0<=@toZ (WordToZ 4) word-65536*1+2^128*1<2^128) in Extended.
    change (((@toZ (WordToZ 4) word-65536*1)/2+2^128*1)/2^127=1).
    assert (Half : -32768<=(@toZ (WordToZ 4) word-65536)/2<0).
    { split;[apply Z.div_le_lower_bound|apply Z.div_lt_upper_bound];lia. }
    rewrite !Z.mul_1_r.
    change (2^128) with (2*2^127).
    symmetry;apply Z.div_unique with (r:=(@toZ (WordToZ 4) word-65536)/2+2^127);lia.
Qed.

Lemma literal_wnaf_digit_half_signed word :
  @toZ (WordToZ 7) (literal_wnaf_digit_half word)-
    2^128* @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem (literal_wnaf_digit_half word))=
    literal_wnaf_signed16 word/2.
Proof. rewrite literal_wnaf_digit_half_value,literal_wnaf_digit_half_top;ring. Qed.

Lemma literal_wnaf_odd_bounds q : 0<=q<2^128 -> q mod 2=1 ->
  let d:=wnaf_digit (q mod 32768) 15 in
  d mod 2=1 /\ 0<=(q-d)/2<2^128.
Proof.
  intros Q Odd;cbv zeta.
  assert (Different : (q/2^0) mod 2<>0) by (change (q/1 mod 2<>0);rewrite Z.div_1_r;lia).
  destruct (wnaf_word_bounds q 0 15 0 ltac:(lia) ltac:(lia) ltac:(left;reflexivity) Different)
    as (Window & Wodd).
  unfold wnaf_word in Window,Wodd;change (2^0) with 1 in Window,Wodd.
  rewrite Z.div_1_r,Z.add_0_r in Window,Wodd.
  change (0<q mod 32768<32768) in Window.
  change ((q mod 32768) mod 2=1) in Wodd.
  destruct (wnaf_digit_bounds (q mod 32768) 15 ltac:(lia) Window Wodd)
    as (Carry & Bounds & Parity).
  change (-16384<wnaf_digit (q mod 32768) 15<16384) in Bounds.
  pose proof (wnaf_step_preserves_value q 0 15 15 0 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(left;reflexivity) Different) as Value.
  unfold wnaf_word in Value;change (2^0) with 1 in Value.
  rewrite Z.div_1_r,!Z.add_0_r in Value.
  change (q=wnaf_digit (q mod 32768) 15+32768*(q/32768+wnaf_carry (q mod 32768) 15)) in Value.
  pose proof (Z.div_pos q 32768 ltac:(lia) ltac:(lia)) as Quotient.
  assert (Nonnegative : 0<=q-wnaf_digit (q mod 32768) 15) by (destruct Carry;nia).
  split;[exact Parity|];split.
  - apply Z.div_pos;lia.
  - apply Z.div_lt_upper_bound;lia.
Qed.

Lemma literal_wnaf15_body_shape word :
  @literal_wnaf15_body Alg.CoreFunSem (Bit.zero,word)=
    (@literal_wnaf_sub128 Alg.CoreFunSem
      ((Bit.zero,@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)),
        literal_wnaf_digit_half (@literal_wnaf_mask15 Alg.CoreFunSem (literal_wnaf_low16 word))),
      inr (@literal_wnaf_mask15 Alg.CoreFunSem (literal_wnaf_low16 word))).
Proof. reflexivity. Qed.

Theorem literal_wnaf15_odd_next word :
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one ->
  exists next digit,
    @literal_wnaf15_step Alg.CoreFunSem (Bit.zero,word)=((Bit.zero,next),inr digit) /\
    literal_wnaf_signed16 digit=wnaf_digit ((@toZ (WordToZ 7) word) mod 32768) 15 /\
    @toZ (WordToZ 7) next=(@toZ (WordToZ 7) word-literal_wnaf_signed16 digit)/2.
Proof.
  intro Odd.
  pose (digit:=@literal_wnaf_mask15 Alg.CoreFunSem (literal_wnaf_low16 word)).
  assert (DigitValue : literal_wnaf_signed16 digit=wnaf_digit ((@toZ (WordToZ 7) word) mod 32768) 15).
  { refine (eq_trans (literal_wnaf_mask15_signed (literal_wnaf_low16 word)) _).
    refine (f_equal (fun z=>wnaf_digit z 15) _).
    refine (eq_trans (f_equal (fun z=>z mod 32768) (literal_wnaf_low16_value word)) _).
    symmetry;apply Znumtheory.Zmod_div_mod;[lia|lia|exists 2;reflexivity]. }
  pose proof (word_value_bounds 7 word) as Q.
  change (0<=@toZ (WordToZ 7) word<2^128) in Q.
  pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as BitValue.
  change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
    Z.testbit (@toZ (WordToZ 7) word) 0) in BitValue.
  rewrite Odd in BitValue;change (Datatypes.true=Z.testbit (@toZ (WordToZ 7) word) 0) in BitValue.
  symmetry in BitValue;apply Z.testbit_true in BitValue;[|lia].
  change ((@toZ (WordToZ 7) word)/1 mod 2=1) in BitValue.
  rewrite Z.div_1_r in BitValue.
  destruct (literal_wnaf_odd_bounds (@toZ (WordToZ 7) word) Q BitValue) as (DigitOdd & Range).
  rewrite <-DigitValue in DigitOdd,Range.
  pose (x:=@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)).
  pose (y:=literal_wnaf_digit_half digit).
  assert (X : @toZ (WordToZ 7) x=(@toZ (WordToZ 7) word)/2).
  { unfold x;rewrite literal_wnaf_shift128_value;change ((0*2^128+@toZ (WordToZ 7) word)/2=
      (@toZ (WordToZ 7) word)/2);reflexivity. }
  assert (Y : @toZ (WordToZ 7) y-2^128* @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem y)=
    literal_wnaf_signed16 digit/2) by (apply literal_wnaf_digit_half_signed).
  assert (Difference : @toZ (WordToZ 7) x-@toZ (WordToZ 7) y+
      2^128* @toZ BitToZ (@Word.leftmost Bit 7 Alg.CoreFunSem y)=
    (@toZ (WordToZ 7) word-literal_wnaf_signed16 digit)/2).
  { pose proof (literal_wnaf_half_sub (@toZ (WordToZ 7) word) (literal_wnaf_signed16 digit) ltac:(lia)) as Half.
    rewrite X.
    lia. }
  destruct (literal_wnaf_sub128_positive x y ltac:(rewrite Difference;exact Range)) as (next & Sub & Value).
  exists next,digit;split.
  - assert (Step : @literal_wnaf15_step Alg.CoreFunSem (Bit.zero,word)=
      @literal_wnaf15_body Alg.CoreFunSem (Bit.zero,word)).
    { unfold literal_wnaf15_step.
      change ((match @Word.rightmost Bit 7 Alg.CoreFunSem word with
        | inl _ => ((Bit.zero,@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)),inl tt)
        | inr _ => @literal_wnaf15_body Alg.CoreFunSem (Bit.zero,word)
        end)=@literal_wnaf15_body Alg.CoreFunSem (Bit.zero,word)).
      rewrite Odd;reflexivity. }
    refine (eq_trans Step (eq_trans (literal_wnaf15_body_shape word) _)).
    exact (f_equal (fun s=>(s,inr digit)) Sub).
  - split;[exact DigitValue|exact (eq_trans Value Difference)].
Qed.
