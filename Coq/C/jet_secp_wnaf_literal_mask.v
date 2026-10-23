(** Signed literal digit versus the original C digit arithmetic and store.
    The execution endpoint covers a full 15-bit window with positive C sign,
    as needed for generate's 128-bit split scalars. It is not a whole wNAF
    function or public jet theorem; truncated windows and literal next-state
    correspondence are separate remaining obligations. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers AST Maps Memory Values Events Clight ClightBigstep.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_digit C.jet_word_repr C.jet_predicate_spec.
Require Import C.jet_word_bit_spec C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_linkage C.jets_secp.
Import Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_wnaf_signed16 (word : Ty.tySem (Word 4)) :=
  @toZ (WordToZ 4) word-65536* @toZ BitToZ (@Word.leftmost Bit 4 Alg.CoreFunSem word).

Lemma wnaf_mask_arithmetic hi sign tail :
  (hi=0 \/ hi=1) -> (sign=0 \/ sign=1) -> 0<=tail<16384 ->
  wnaf_digit ((32768*hi+16384*sign+tail) mod 32768) 15=tail-16384*sign.
Proof.
  intros Hi Sign Tail.
  assert (M : (32768*hi+16384*sign+tail) mod 32768=16384*sign+tail).
  { symmetry;apply Z.mod_unique with (q:=hi);destruct Sign;subst;lia. }
  rewrite M;unfold wnaf_digit,wnaf_carry.
  change (16384*sign+tail-(16384*sign+tail)/16384*32768=tail-16384*sign).
  assert (Q : (16384*sign+tail)/16384=sign).
  { symmetry;apply Z.div_unique with (r:=tail);lia. }
  rewrite Q;ring.
Qed.

Definition literal_wnaf_low16 (word : Ty.tySem (Word 7)) : Ty.tySem (Word 4) := snd (snd (snd word)).

Lemma literal_wnaf_low16_value word :
  @toZ (WordToZ 4) (literal_wnaf_low16 word)=(@toZ (WordToZ 7) word) mod 65536.
Proof.
  destruct word as [hi64 [hi32 [hi16 lo16]]].
  pose proof (word_value_bounds 4 lo16) as Low.
  change (0<=@toZ (WordToZ 4) lo16<65536) in Low.
  change (@toZ (WordToZ 4) lo16=
    (@toZ (WordToZ 6) hi64*18446744073709551616+
      (@toZ (WordToZ 5) hi32*4294967296+
        (@toZ (WordToZ 4) hi16*65536+@toZ (WordToZ 4) lo16))) mod 65536).
  apply Z.mod_unique with (q:=@toZ (WordToZ 6) hi64*281474976710656+
    @toZ (WordToZ 5) hi32*65536+@toZ (WordToZ 4) hi16);[lia|ring].
Qed.

Theorem literal_wnaf15_odd_digit sign word :
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one ->
  snd (@literal_wnaf15_step Alg.CoreFunSem (sign,word))=
    inr (@literal_wnaf_mask15 Alg.CoreFunSem (literal_wnaf_low16 word)).
Proof.
  intro Odd.
  assert (Step : @literal_wnaf15_step Alg.CoreFunSem (sign,word)=
    @literal_wnaf15_body Alg.CoreFunSem (sign,word)).
  { unfold literal_wnaf15_step.
    change ((match @Word.rightmost Bit 7 Alg.CoreFunSem word with
      | inl _ => ((sign,@literal_wnaf_shift128 Alg.CoreFunSem (sign,word)),inl tt)
      | inr _ => @literal_wnaf15_body Alg.CoreFunSem (sign,word)
      end)=@literal_wnaf15_body Alg.CoreFunSem (sign,word)).
    rewrite Odd;reflexivity. }
  refine (eq_trans (f_equal (@snd (Ty.tySem literal_wnaf_state) (Ty.tySem literal_wnaf_digit)) Step) _).
  reflexivity.
Qed.

Theorem literal_wnaf_mask15_signed word :
  literal_wnaf_signed16 (@literal_wnaf_mask15 Alg.CoreFunSem word)=
    wnaf_digit ((@toZ (WordToZ 4) word) mod 32768) 15.
Proof.
  destruct word as [[[[hi sign] a] b] c].
  set (tail := @toZ (WordToZ 1) a*4096+@toZ (WordToZ 2) b*256+@toZ (WordToZ 3) c).
  assert (Tail : 0<=tail<16384).
  { pose proof (word_value_bounds 1 a);pose proof (word_value_bounds 2 b);
    pose proof (word_value_bounds 3 c).
    change (0<=@toZ (WordToZ 1) a<4) in H.
    change (0<=@toZ (WordToZ 2) b<16) in H0.
    change (0<=@toZ (WordToZ 3) c<256) in H1.
    unfold tail;lia. }
  assert (Input : @toZ (WordToZ 4) ((((hi,sign),a),b),c)=
    32768* @toZ BitToZ hi+16384* @toZ BitToZ sign+tail).
  { change ((((@toZ BitToZ hi*2+@toZ BitToZ sign)*4+@toZ (WordToZ 1) a)*16+
      @toZ (WordToZ 2) b)*256+@toZ (WordToZ 3) c=
      32768* @toZ BitToZ hi+16384* @toZ BitToZ sign+tail).
    unfold tail;ring. }
  assert (Mask : literal_wnaf_signed16 (@literal_wnaf_mask15 Alg.CoreFunSem ((((hi,sign),a),b),c))=
    tail-16384* @toZ BitToZ sign).
  { change ((((@toZ BitToZ sign*2+@toZ BitToZ sign)*4+@toZ (WordToZ 1) a)*16+
      @toZ (WordToZ 2) b)*256+@toZ (WordToZ 3) c-65536* @toZ BitToZ sign=
      tail-16384* @toZ BitToZ sign).
    unfold tail;ring. }
  refine (eq_trans Mask (eq_trans _ (eq_sym (f_equal (fun n=>wnaf_digit (n mod 32768) 15) Input)))).
  symmetry;apply wnaf_mask_arithmetic;[destruct hi as [u|u];destruct u;auto|
    destruct sign as [u|u];destruct u;auto|exact Tail].
Qed.

Theorem literal_wnaf15_odd_digit_numeric sign word :
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one ->
  exists digit : Ty.tySem (Word 4),
    snd (@literal_wnaf15_step Alg.CoreFunSem (sign,word))=inr digit /\
    literal_wnaf_signed16 digit=wnaf_digit ((@toZ (WordToZ 7) word) mod 32768) 15.
Proof.
  intro Odd;exists (@literal_wnaf_mask15 Alg.CoreFunSem (literal_wnaf_low16 word)).
  split;[apply literal_wnaf15_odd_digit;exact Odd|].
  refine (eq_trans (literal_wnaf_mask15_signed (literal_wnaf_low16 word)) _).
  refine (f_equal (fun n=>wnaf_digit n 15) _).
  refine (eq_trans (f_equal (fun n=>n mod 32768) (literal_wnaf_low16_value word)) _).
  symmetry;apply Znumtheory.Zmod_div_mod;[lia|lia|exists 2;reflexivity].
Qed.

Lemma wnaf_nonzero_residual_word n bit carry :
  0<=bit -> (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  (n/2^bit+carry) mod 32768=wnaf_word n bit 15 carry.
Proof.
  intros HBit Carry Different.
  pose proof (wnaf_word_bounds n bit 15 carry HBit ltac:(lia) Carry Different) as Bounds.
  destruct Bounds as [Bounds Odd].
  change (0<wnaf_word n bit 15 carry<32768) in Bounds.
  rewrite <-Z.add_mod_idemp_l by lia.
  change ((wnaf_word n bit 15 carry) mod 32768=wnaf_word n bit 15 carry).
  apply Z.mod_small;lia.
Qed.

Lemma wnaf_nonzero_literal_odd n bit carry (word : Ty.tySem (Word 7)) :
  (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  @Word.rightmost Bit 7 Alg.CoreFunSem word=Bit.one.
Proof.
  intros Carry Different HWord.
  pose proof (Z.div_mod (n/2^bit) 2 ltac:(lia)) as Split.
  pose proof (Z.mod_pos_bound (n/2^bit) 2 ltac:(lia)) as Low.
  assert (Odd : Z.testbit (@toZ (WordToZ 7) word) 0=Datatypes.true).
  { destruct Carry as [C | C];subst carry.
    - replace (@toZ (WordToZ 7) word) with (2*(n/2^bit/2)+1) by lia.
      apply Z.testbit_odd_0.
    - replace (@toZ (WordToZ 7) word) with (2*(n/2^bit/2)+1) by lia.
      apply Z.testbit_odd_0. }
  pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as HB.
  change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
    Z.testbit (@toZ (WordToZ 7) word) 0) in HB.
  rewrite Odd in HB;destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u|u];
    destruct u;[discriminate|reflexivity].
Qed.

Theorem exec_wnaf_literal_digit15 le m n bit carry b base bs (word : Ty.tySem (Word 7)) :
  0<=n<2^256 -> 0<=bit<256 -> bit+15<=256 ->
  (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  @toZ (WordToZ 7) word=n/2^bit+carry ->
  le!_now=Some (Vint (Int.repr 15)) -> le!_carry=Some (Vint (Int.repr carry)) ->
  le!_w=Some (Vint (Int.repr 15)) -> le!_wnaf=Some (Vptr b (Ptrofs.repr base)) ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_sign=Some (Vint Int.one) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  0<=base -> base+4*bit<=Ptrofs.max_unsigned ->
  Mem.valid_access m Mint32 b (base+4*bit) Writable ->
  exists mf digit,
    snd (@literal_wnaf15_step Alg.CoreFunSem (Bit.zero,word))=inr digit /\
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_window_digit E0
      (wnaf_digit_final (PTree.set _t'3 (Vint (Int.repr ((n/2^bit) mod 2^15))) le)
        (wnaf_word n bit 15 carry) 15) mf Out_normal /\
    Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (literal_wnaf_signed16 digit)))=Some mf /\
    Mem.load Mint32 mf b (base+4*bit)=Some (Vint (Int.repr (literal_wnaf_signed16 digit))).
Proof.
  intros N HBit End Carry Different HWord HNow HC HW HP HB HS Storage Base Max Writable.
  destruct (literal_wnaf15_odd_digit_numeric Bit.zero word
    (wnaf_nonzero_literal_odd n bit carry word Carry Different HWord)) as (digit & Lit & Value).
  assert (Digit : literal_wnaf_signed16 digit=wnaf_digit (wnaf_word n bit 15 carry) 15).
  { refine (eq_trans Value (f_equal (fun k=>wnaf_digit k 15) _)).
    refine (eq_trans (f_equal (fun k=>k mod 32768) HWord) _).
    apply wnaf_nonzero_residual_word;lia || assumption. }
  destruct (exec_wnaf_window_digit le m n bit 15 15 carry b base 1 bs N HBit ltac:(lia) ltac:(lia)
    End Carry Different ltac:(left;reflexivity) HNow HC HW HP HB HS Storage Base Max Writable)
    as (mf & Exec & Store & Load & Rest).
  exists mf,digit;split;[exact Lit|];split;[exact Exec|].
  rewrite Z.mul_1_l in Store,Load.
  rewrite Digit;split;assumption.
Qed.
