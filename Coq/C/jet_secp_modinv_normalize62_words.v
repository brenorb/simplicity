(** Signed-value bridges for the actual normalize_62 word operations.
    Overflow bounds are internal helper obligations, not restrictions added
    to a public jet contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import C.jet_secp_modinv_normalize62_exec.
Local Open Scope Z_scope.
Set Default Timeout 10.

(** Bridges for the actual helper's bitwise conditional operations. *)
Lemma norm62_add_word_cases w modulus i :
 norm62_add_words w modulus i =
 if Int64.lt (w 4%nat) Int64.zero then Int64.add (w i) (modulus i) else w i.
Proof.
 unfold norm62_add_words.
 change (Int64.repr 63) with (Int64.repr (Int64.zwordsize-1)).
 rewrite Int64.shr_lt_zero.
 destruct (Int64.lt (w 4%nat) Int64.zero).
 - rewrite Int64.and_mone;reflexivity.
 - rewrite Int64.and_zero,Int64.add_zero;reflexivity.
Qed.

Lemma norm62_signed_add a b :
 Int64.min_signed <= Int64.signed a + Int64.signed b <= Int64.max_signed ->
 Int64.signed (Int64.add a b) = Int64.signed a + Int64.signed b.
Proof. intro Bound;rewrite Int64.add_signed;apply Int64.signed_repr;exact Bound. Qed.

Lemma norm62_signed_neg a :
 Int64.min_signed <= -Int64.signed a <= Int64.max_signed ->
 Int64.signed (Int64.neg a) = -Int64.signed a.
Proof.
 intro Bound. rewrite <- (Int64.repr_signed a) at 1.
 rewrite Int64.neg_repr. apply Int64.signed_repr;exact Bound.
Qed.

Lemma norm62_signed_shr a k : 0<=k<64 ->
 Int64.signed (Int64.shr a (Int64.repr k)) = Int64.signed a / 2^k.
Proof.
 intro K. rewrite Int64.shr_div_two_p.
 rewrite Int64.unsigned_repr by (change (0<=k<=18446744073709551615);lia).
 rewrite two_p_equiv. apply Int64.signed_repr.
 pose proof (Int64.signed_range a) as Range.
 assert (Power : 1<=2^k) by (pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia));lia).
 change Int64.min_signed with (-9223372036854775808) in *.
 change Int64.max_signed with 9223372036854775807 in *.
 split.
 - apply Z.div_le_lower_bound;[lia|nia].
 - apply Z.div_le_upper_bound;[lia|nia].
Qed.

Lemma norm62_unsigned_signed_mod a :
 Int64.unsigned a mod 2^62 = Int64.signed a mod 2^62.
Proof.
 unfold Int64.signed;destruct (zlt (Int64.unsigned a) Int64.half_modulus);[reflexivity|].
 change Int64.modulus with (4*2^62).
 replace (Int64.unsigned a - 4*2^62) with (Int64.unsigned a + (-4)*2^62) by ring.
 rewrite Z_mod_plus_full;reflexivity.
Qed.

Lemma norm62_mask_unsigned a :
 Int64.unsigned (Int64.and a (Int64.repr (2^62-1))) = Int64.signed a mod 2^62.
Proof.
 rewrite <- norm62_unsigned_signed_mod.
 rewrite <- two_p_equiv.
 rewrite <- Int64.zero_ext_and by lia.
 apply Int64.zero_ext_mod;change (0<=62<64);lia.
Qed.

Lemma norm62_mask_signed a :
 Int64.signed (Int64.and a (Int64.repr (2^62-1))) = Int64.signed a mod 2^62.
Proof.
 rewrite Int64.signed_eq_unsigned;[apply norm62_mask_unsigned|].
 rewrite norm62_mask_unsigned.
 pose proof (Z.mod_pos_bound (Int64.signed a) (2^62) ltac:(lia)).
 change Int64.max_signed with 9223372036854775807;lia.
Qed.

Lemma norm62_neg_word_cases w sign i :
 norm62_neg_words w sign i = if Int64.lt sign Int64.zero then Int64.neg (w i) else w i.
Proof.
 unfold norm62_neg_words.
 change (Int64.repr 63) with (Int64.repr (Int64.zwordsize-1)).
 rewrite Int64.shr_lt_zero. destruct (Int64.lt sign Int64.zero).
 - change (Int64.sub (Int64.not (w i)) Int64.mone = Int64.neg (w i)).
   rewrite Int64.sub_add_not, Int64.not_mone, Int64.add_zero.
   symmetry;apply Int64.neg_not.
 - rewrite Int64.xor_zero,Int64.sub_zero_l;reflexivity.
Qed.

Fixpoint norm62_value_z (n : nat) (w : nat -> Z) : Z :=
 match n with
 | O => w 0%nat
 | S n => w 0%nat + 2^62 * norm62_value_z n (fun i => w (S i))
 end.

Fixpoint norm62_carry_z (n : nat) (w : nat -> Z) (carry : Z) : nat -> Z :=
 match n with
 | O => fun _ => w 0%nat + carry
 | S n => fun i => match i with
   | O => (w 0%nat + carry) mod 2^62
   | S i => norm62_carry_z n (fun j => w (S j)) ((w 0%nat + carry)/2^62) i
   end
 end.

Lemma norm62_carry_z_value n : forall w carry,
 norm62_value_z n (norm62_carry_z n w carry) = norm62_value_z n w + carry.
Proof.
 induction n as [|n IH];intros w carry.
 - reflexivity.
 - cbn [norm62_value_z norm62_carry_z].
   rewrite IH.
   pose proof (Z.div_mod (w 0%nat + carry) (2^62) ltac:(lia)). nia.
Qed.

Lemma norm62_carry_z_low n : forall w carry i, (i<n)%nat ->
 0 <= norm62_carry_z n w carry i < 2^62.
Proof.
 induction n as [|n IH];intros w carry i I;[lia|].
 destruct i as [|i].
 - cbn [norm62_carry_z];apply Z.mod_pos_bound;lia.
 - cbn [norm62_carry_z];apply IH;lia.
Qed.

Lemma norm62_shr62_bounds a :
 -2 <= Int64.signed (Int64.shr a (Int64.repr 62)) <= 1.
Proof.
 rewrite norm62_signed_shr by lia.
 pose proof (Int64.signed_range a) as Range.
 change Int64.min_signed with (-9223372036854775808) in Range.
 change Int64.max_signed with 9223372036854775807 in Range.
 split.
 - apply Z.div_le_lower_bound;[lia|nia].
 - assert (Upper : Int64.signed a / 2^62 < 2).
   { apply Z.div_lt_upper_bound;[lia|nia]. }
   lia.
Qed.

Lemma norm62_signed_add_shr62 a b :
 Int64.min_signed+2 <= Int64.signed a <= Int64.max_signed-1 ->
 Int64.signed (Int64.add a (Int64.shr b (Int64.repr 62))) =
 Int64.signed a + Int64.signed b / 2^62.
Proof.
 intro Bound. rewrite norm62_signed_add.
 - rewrite norm62_signed_shr by lia;reflexivity.
 - pose proof (norm62_shr62_bounds b);lia.
Qed.

Lemma norm62_carry_words_signed w :
 (forall j, (j<5)%nat -> Int64.min_signed+2 <= Int64.signed (w j) <= Int64.max_signed-1) ->
 forall i, (i<5)%nat ->
 Int64.signed (norm62_carry_words w i) =
 norm62_carry_z 4 (fun j => Int64.signed (w j)) 0 i.
Proof.
 intros Bound i I.
 destruct i as [|[|[|[|[|i]]]]];[| | | | |lia];
   cbn [norm62_carry_words norm62_carry_z List.nth];
   repeat rewrite norm62_mask_signed;
   repeat rewrite norm62_signed_add_shr62 by (apply Bound;lia);
   repeat rewrite Z.add_0_r;reflexivity.
Qed.

Lemma norm62_value_ext n w v :
 (forall i, (i<=n)%nat -> w i=v i) -> norm62_value_z n w=norm62_value_z n v.
Proof.
 induction n as [|n IH] in w,v|-*;intro E;cbn [norm62_value_z].
 - apply E;lia.
 - rewrite E by lia. f_equal. f_equal. apply IH;intros;apply E;lia.
Qed.

Lemma norm62_carry_words_value w :
 (forall j, (j<5)%nat -> Int64.min_signed+2 <= Int64.signed (w j) <= Int64.max_signed-1) ->
 norm62_value_z 4 (fun i=>Int64.signed (norm62_carry_words w i)) =
 norm62_value_z 4 (fun i=>Int64.signed (w i)).
Proof.
 intro Bound.
 transitivity (norm62_value_z 4 (norm62_carry_z 4 (fun i=>Int64.signed (w i)) 0)).
 - apply norm62_value_ext;intros;apply norm62_carry_words_signed;[exact Bound|lia].
 - rewrite norm62_carry_z_value;lia.
Qed.

Lemma norm62_carry_words_low w :
 (forall j, (j<5)%nat -> Int64.min_signed+2 <= Int64.signed (w j) <= Int64.max_signed-1) ->
 forall i, (i<4)%nat -> 0<=Int64.signed (norm62_carry_words w i)<2^62.
Proof.
 intros Bound i I. rewrite norm62_carry_words_signed by (exact Bound||lia).
 apply norm62_carry_z_low;exact I.
Qed.
