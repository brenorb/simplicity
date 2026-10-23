(** Reachable raw digit constructors and their exact C integer interpretation. *)
From Coq Require Import ZArith Lia List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
From compcert Require Import Integers.
Require Import C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_literal_mask
  C.jet_secp_wnaf_literal_next C.jet_secp_wnaf_literal_zeros C.jet_secp_wnaf_digit
  C.jet_predicate_spec C.jet_word_bit_spec C.jet_subtract_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wnaf_literal_valid (digit : Ty.tySem literal_wnaf_digit) : Prop :=
  match digit with
  | inl _=>True
  | inr word=>literal_wnaf_signed16 word mod 2=1 /\ -16384<literal_wnaf_signed16 word<16384
  end.

Lemma wnaf_literal_odd_value_bounds q : q mod 2=1 ->
  wnaf_digit (q mod 32768) 15 mod 2=1 /\ -16384<wnaf_digit (q mod 32768) 15<16384.
Proof.
  intro Odd.
  assert (Different : (q/2^0) mod 2<>0).
  { change (q/1 mod 2<>0);rewrite Z.div_1_r;lia. }
  destruct (wnaf_word_bounds q 0 15 0 ltac:(lia) ltac:(lia) ltac:(left;reflexivity) Different)
    as (Window & Low).
  unfold wnaf_word in Window,Low;change (2^0) with 1 in Window,Low.
  rewrite Z.div_1_r,Z.add_0_r in Window,Low.
  change (0<q mod 32768<32768) in Window;change ((q mod 32768) mod 2=1) in Low.
  destruct (wnaf_digit_bounds (q mod 32768) 15 ltac:(lia) Window Low) as (_ & Bounds & Parity).
  split;[exact Parity|exact Bounds].
Qed.

Lemma literal_wnaf15_valid_step (word : Ty.tySem (Word 7)) :
  exists (next : Ty.tySem (Word 7)) digit,
    @literal_wnaf15_step Alg.CoreFunSem (Bit.zero,word)=((Bit.zero,next),digit) /\ wnaf_literal_valid digit.
Proof.
  destruct (@Word.rightmost Bit 7 Alg.CoreFunSem word) as [u|u] eqn:Low;destruct u.
  - exists (@literal_wnaf_shift128 Alg.CoreFunSem (Bit.zero,word)),(inl tt).
    split;[apply literal_wnaf15_even;exact Low|constructor].
  - destruct (literal_wnaf15_odd_next word Low) as (next & digit & Step & Digit & Value).
    exists next,(inr digit);split;[exact Step|].
    pose proof (word_bit_spec_numeric 7 0 word ltac:(cbn;lia)) as Parity.
    change (Bit.toBool (@Word.rightmost Bit 7 Alg.CoreFunSem word)=
      Z.testbit (@toZ (WordToZ 7) word) 0) in Parity.
    rewrite Low in Parity;change (Datatypes.true=Z.testbit (@toZ (WordToZ 7) word) 0) in Parity.
    symmetry in Parity;apply Z.testbit_true in Parity;[|lia].
    change ((@toZ (WordToZ 7) word)/1 mod 2=1) in Parity;rewrite Z.div_1_r in Parity.
    change (literal_wnaf_signed16 digit mod 2=1 /\ -16384<literal_wnaf_signed16 digit<16384).
    rewrite Digit;apply wnaf_literal_odd_value_bounds;exact Parity.
Qed.

Lemma literal_wnaf_run_values count (word : Ty.tySem (Word 7)) :
  Forall wnaf_literal_valid (snd (literal_wnaf_run count (Bit.zero,word))).
Proof.
  revert word;induction count as [|count IH];intro word;[constructor|].
  destruct (literal_wnaf15_valid_step word) as (next & digit & Step & Valid).
  rewrite (literal_wnaf_run_step count (Bit.zero,word) (Bit.zero,next) digit Step).
  pose proof (IH next) as Good.
  destruct (literal_wnaf_run count (Bit.zero,next)) as [final digits] eqn:Run.
  change (Forall wnaf_literal_valid (digits++[digit])).
  apply Forall_app;split.
  - exact Good.
  - constructor;[exact Valid|constructor].
Qed.

Theorem literal_wnaf15_values word : Forall wnaf_literal_valid (literal_wnaf15_digits (Bit.zero,word)).
Proof. rewrite <-literal_wnaf15_digits_order;apply literal_wnaf_run_values. Qed.

Lemma literal_wnaf_signed16_injective (a b : Ty.tySem (Word 4)) :
  literal_wnaf_signed16 a=literal_wnaf_signed16 b -> a=b.
Proof.
  intro Same.
  assert (Pair : (@Word.leftmost Bit 4 Alg.CoreFunSem a,a)=(@Word.leftmost Bit 4 Alg.CoreFunSem b,b)).
  { apply (borrow_word_balance_injective 4).
    change (literal_wnaf_signed16 a=literal_wnaf_signed16 b);exact Same. }
  exact (f_equal (@snd (Ty.tySem Bit) (Ty.tySem (Word 4))) Pair).
Qed.

Theorem wnaf_literal_zero_iff digit :
  wnaf_literal_valid digit -> (wnaf_literal_value digit=0 <-> digit=inl tt).
Proof.
  destruct digit as [u|word];[destruct u;intro Valid;split;intro;reflexivity|].
  intros [Odd Bounds];split.
  - intro Zero;change (literal_wnaf_signed16 word=0) in Zero;rewrite Zero in Odd;discriminate.
  - intro Impossible;discriminate.
Qed.

Theorem wnaf_literal_value_injective a b :
  wnaf_literal_valid a -> wnaf_literal_valid b -> wnaf_literal_value a=wnaf_literal_value b -> a=b.
Proof.
  intros A B Same;destruct a as [u|a];destruct b as [v|b].
  - destruct u,v;reflexivity.
  - assert (Zero : wnaf_literal_value (inr b)=0) by (symmetry;exact Same).
    apply (proj1 (wnaf_literal_zero_iff (inr b) B)) in Zero;discriminate.
  - assert (Zero : wnaf_literal_value (inr a)=0) by exact Same.
    apply (proj1 (wnaf_literal_zero_iff (inr a) A)) in Zero;discriminate.
  - f_equal;apply literal_wnaf_signed16_injective;exact Same.
Qed.

Lemma wnaf_literal_int_signed digit : wnaf_literal_valid digit ->
  Int.signed (Int.repr (wnaf_literal_value digit))=wnaf_literal_value digit.
Proof.
  intro Valid;apply Int.signed_repr.
  change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647.
  destruct digit as [u|word];[change (-2147483648<=0<=2147483647);lia|].
  destruct Valid as [Odd Bounds];exact (ltac:(change (-2147483648<=literal_wnaf_signed16 word<=2147483647);lia)).
Qed.

Theorem wnaf_literal_int_zero_iff digit : wnaf_literal_valid digit ->
  (Int.repr (wnaf_literal_value digit)=Int.zero <-> digit=inl tt).
Proof.
  intro Valid;split.
  - intro Zero;apply (proj1 (wnaf_literal_zero_iff digit Valid)).
    pose proof (f_equal Int.signed Zero) as Value.
    rewrite (wnaf_literal_int_signed digit Valid) in Value;exact Value.
  - intro None;rewrite None;reflexivity.
Qed.

Theorem wnaf_literal_int_injective a b : wnaf_literal_valid a -> wnaf_literal_valid b ->
  Int.repr (wnaf_literal_value a)=Int.repr (wnaf_literal_value b) -> a=b.
Proof.
  intros A B Same;apply wnaf_literal_value_injective;try assumption.
  pose proof (f_equal Int.signed Same) as Value.
  rewrite (wnaf_literal_int_signed a A),(wnaf_literal_int_signed b B) in Value;exact Value.
Qed.
