(** Integer/value bridge for the actual fe_half machine outputs on loose limbs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp
  C.jet_secp_field_half C.jet_secp_square_columns C.jet_secp_u128_word_shift
  C.jet_secp_multiply_secondvalues_arithmetic C.jet_secp_multiply_normalize_bridge
  C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition half_parity (w : nat -> int64) := Int64.unsigned (w 0%nat) mod 2.
Definition half_prime_digit i :=
  if Nat.eqb i 0 then 4503595332402223
  else if Nat.eqb i 4 then 281474976710655 else 4503599627370495.

Lemma half_lowbit_unsigned x : Int64.unsigned (Int64.and x Int64.one)=Int64.unsigned x mod 2.
Proof.
  replace Int64.one with (Int64.sub (Int64.repr 2) Int64.one) at 1 by reflexivity.
  exact (mask_pow2_unsigned x (Int64.repr 2) (Int64.repr 1) ltac:(change (0<2);lia) eq_refl).
Qed.
Lemma half_lowbit_word x : Int64.and x Int64.one=Int64.repr (Int64.unsigned x mod 2).
Proof.
  rewrite <- (Int64.repr_unsigned (Int64.and x Int64.one)) at 1.
  rewrite half_lowbit_unsigned;reflexivity.
Qed.
Lemma half_parity_range w : half_parity w=0 \/ half_parity w=1.
Proof. unfold half_parity;pose proof (Z.mod_pos_bound (Int64.unsigned (w 0%nat)) 2 ltac:(lia));lia. Qed.
Lemma half_mask_word w : half_mask w=Int64.repr (half_parity w*4503599627370495).
Proof.
  unfold half_mask;rewrite half_lowbit_word;fold (half_parity w).
  destruct (half_parity_range w) as [H|H];rewrite H;reflexivity.
Qed.
Lemma half_addend_unsigned w i :
  Int64.unsigned
    (if Nat.eqb i 0 then Int64.and (Int64.repr 4503595332402223) (half_mask w)
     else if Nat.eqb i 4 then Int64.shru (half_mask w) (Int64.repr 4) else half_mask w)=
  half_parity w*half_prime_digit i.
Proof.
  rewrite half_mask_word;unfold half_prime_digit.
  destruct (half_parity_range w) as [H|H];rewrite H;
    destruct (Nat.eqb i 0), (Nat.eqb i 4);reflexivity.
Qed.

Lemma half_adjust_unsigned w : square_input_bounds w ->
  forall i, (i<5)%nat -> Int64.unsigned (half_adjust_words w i)=
    Int64.unsigned (w i)+half_parity w*half_prime_digit i.
Proof.
  intros HB i HI;unfold half_adjust_words,Int64.add;rewrite half_addend_unsigned.
  apply Int64.unsigned_repr.
  pose proof (HB i HI);pose proof (Int64.unsigned_range_2 (w i)).
  destruct (half_parity_range w) as [HP|HP];rewrite HP;unfold half_prime_digit;
    destruct (Nat.eqb i 0), (Nat.eqb i 4);change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma half_adjust_bound w : square_input_bounds w ->
  forall i, (i<5)%nat -> 0<=Int64.unsigned (half_adjust_words w i)<
    if Nat.eqb i 4 then 4785074604081152 else 76561193665298432.
Proof.
  intros HB i HI;split;[apply Int64.unsigned_range_2|].
  rewrite half_adjust_unsigned by assumption;pose proof (HB i HI) as HBnd.
  destruct i as [|[|[|[|[|i]]]]]; try lia;
    cbn in HBnd |- *; unfold half_prime_digit; cbn;
    destruct (half_parity_range w) as [HP|HP]; rewrite HP; lia.
Qed.

Lemma half_carry_unsigned a :
  Int64.unsigned (Int64.shl (Int64.and a Int64.one) (Int64.repr 51))=
    (Int64.unsigned a mod 2)*2251799813685248.
Proof.
  rewrite Int64.shl_mul_two_p.
  change (two_p (Int64.unsigned (Int64.repr 51))) with 2251799813685248.
  unfold Int64.mul;rewrite half_lowbit_unsigned.
  change (Int64.unsigned (Int64.repr 2251799813685248)) with 2251799813685248.
  apply Int64.unsigned_repr;pose proof (Z.mod_pos_bound (Int64.unsigned a) 2 ltac:(lia)).
  change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma half_output_unsigned w : square_input_bounds w ->
  forall i, (i<5)%nat -> Int64.unsigned (half_words w i)=
    if Nat.eqb i 4 then Int64.unsigned (half_adjust_words w i)/2
    else Int64.unsigned (half_adjust_words w i)/2+
      (Int64.unsigned (half_adjust_words w (S i)) mod 2)*2251799813685248.
Proof.
  intros HB i HI;unfold half_words;destruct (Nat.eqb i 4) eqn:HE.
  - rewrite uns_shru by lia;reflexivity.
  - unfold Int64.add;rewrite (uns_shru _ 1 ltac:(lia)),half_carry_unsigned.
    change (2^1) with 2.
    apply Int64.unsigned_repr.
    pose proof (half_adjust_bound w HB i HI) as HA.
    rewrite HE in HA.
    pose proof (Z.mod_pos_bound (Int64.unsigned (half_adjust_words w (S i))) 2 ltac:(lia)) as HC.
    pose proof (Z.div_pos (Int64.unsigned (half_adjust_words w i)) 2 ltac:(lia) ltac:(lia)).
    assert (HD : Int64.unsigned (half_adjust_words w i)/2<38280596832649216)
      by (apply Z.div_lt_upper_bound;lia).
    change Int64.max_unsigned with 18446744073709551615;lia.
Qed.

Lemma half_output_reusable w : square_input_bounds w -> square_input_bounds (half_words w).
Proof.
  intros HB i HI;rewrite half_output_unsigned by assumption.
  pose proof (half_adjust_bound w HB i HI) as HA.
  pose proof (Z.mod_pos_bound (Int64.unsigned (half_adjust_words w (S i))) 2 ltac:(lia)) as HC.
  destruct (Nat.eqb i 4) eqn:HE.
  - apply Z.div_lt_upper_bound;lia.
  - assert (HD : Int64.unsigned (half_adjust_words w i)/2<38280596832649216)
      by (apply Z.div_lt_upper_bound;lia);lia.
Qed.

Lemma half_adjust_radix w : square_input_bounds w ->
  radix_value (half_adjust_words w)=radix_value w+half_parity w*feP.
Proof.
  intro HB;rewrite !radix_value_matches_normalizer.
  rewrite !half_adjust_unsigned by (assumption || lia).
  unfold half_prime_digit;cbn [Nat.eqb].
  unfold fe_val,feP,feR;ring.
Qed.

Lemma half_adjust_even w : square_input_bounds w ->
  Int64.unsigned (half_adjust_words w 0%nat) mod 2=0.
Proof.
  intro HB;rewrite half_adjust_unsigned by (assumption || lia).
  change (half_prime_digit 0) with 4503595332402223.
  rewrite Z.add_mod, Z.mul_mod by lia.
  change (4503595332402223 mod 2) with 1.
  fold (half_parity w).
  destruct (half_parity_range w) as [HP|HP];rewrite HP;reflexivity.
Qed.

Lemma half_radix_telescope t0 t1 t2 t3 t4 : t0 mod 2=0 ->
  2*fe_val (t0/2+(t1 mod 2)*2251799813685248)
    (t1/2+(t2 mod 2)*2251799813685248)
    (t2/2+(t3 mod 2)*2251799813685248)
    (t3/2+(t4 mod 2)*2251799813685248) (t4/2)=
  fe_val t0 t1 t2 t3 t4.
Proof.
  intro HE.
  pose proof (Z.div_mod t0 2 ltac:(lia)).
  pose proof (Z.div_mod t1 2 ltac:(lia)).
  pose proof (Z.div_mod t2 2 ltac:(lia)).
  pose proof (Z.div_mod t3 2 ltac:(lia)).
  pose proof (Z.div_mod t4 2 ltac:(lia)).
  unfold fe_val;cbn [Z.pow Pos.iter];lia.
Qed.

Theorem half_value_identity w : square_input_bounds w ->
  2*radix_value (half_words w)=radix_value w+half_parity w*feP.
Proof.
  intro HB;rewrite <-half_adjust_radix by exact HB.
  rewrite !radix_value_matches_normalizer.
  rewrite !half_output_unsigned by (assumption || lia).
  cbn [Nat.eqb].
  apply half_radix_telescope;apply half_adjust_even;exact HB.
Qed.

Theorem eval_field_half_numeric w m b :
  square_input_bounds w -> fe_at m b 0 (words5 w) ->
  Mem.range_perm m b 0 40 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_half)
    [Vptr b Ptrofs.zero] E0 mf Vundef /\
  fe_at mf b 0 (words5 (half_words w)) /\
  Mem.range_perm mf b 0 40 Cur Freeable /\
  square_input_bounds (half_words w) /\
  2*radix_value (half_words w)=radix_value w+half_parity w*feP /\
  lframe (fun bx _ => bx<>b) m mf.
Proof.
  intros HB HI HF.
  destruct (eval_field_half_from_storage w m b HI HF) as (mf & HC & HO & HP & HL).
  exists mf;split;[exact HC|];split;[exact HO|];split;[exact HP|];
    split;[apply half_output_reusable;exact HB|];
    split;[apply half_value_identity;exact HB|exact HL].
Qed.
