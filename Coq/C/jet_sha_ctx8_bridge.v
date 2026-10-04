(** Bridges between the canonical Ctx8 value, its byte-list model and the C
    context fields: buffers and states exist for every byte list / register
    list, and the C counter arithmetic is the model's compression count. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks C.jet_wide C.jet_wide_spec.
Require Import C.jet_read_sha256_counter C.jet_read_sha256_overflow C.jet_sha256_counter_representation.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Lemma buffer_values_list depth (buf : Ty.tySem (buffer_type (Word 3) depth)) :
  byte_chunks_values (buffer_byte_chunks depth buf) = buffer_list (Word 3) depth buf.
Proof.
  induction depth.
  - destruct buf as [[]|x]; reflexivity.
  - destruct buf as [sv b0]. cbn [buffer_byte_chunks byte_chunks_values buffer_list fst snd].
    rewrite IHdepth. destruct sv as [[]|v]; reflexivity.
Qed.

Lemma buffer_exists X depth (l : list (Ty.tySem X)) :
  (length l < Nat.pow 2 (S depth))%nat ->
  exists buf : Ty.tySem (buffer_type X depth), buffer_list X depth buf = l.
Proof.
  induction l as [|x l IH] using rev_ind; intros HL.
  - exists (buffer_empty_value X depth). apply buffer_list_empty.
  - rewrite app_length in HL. cbn [length] in HL.
    destruct (IH ltac:(lia)) as [b0 Hb0].
    pose proof (buffer_snoc_value X depth b0 x) as HS.
    destruct (@buffer_snoc_spec X depth Alg.CoreFunSem (b0, x)) as [v|b'].
    + exfalso. pose proof (vector_values_length X (S depth) v) as HV.
      rewrite HS, app_length, Hb0 in HV. cbn [length] in HV. lia.
    + exists b'. rewrite HS, Hb0. reflexivity.
Qed.

Lemma word32_of_int (x : int) : word32_array_value (@fromZ (WordToZ 5) (Int.unsigned x)) = x.
Proof.
  unfold word32_array_value. rewrite (@to_fromZ (WordToZ 5)).
  change (two_power_nat (bitSize (WordToZ 5))) with Int.modulus.
  rewrite Z.mod_small by apply Int.unsigned_range. apply Int.repr_unsigned.
Qed.

Lemma state_exists (regs : list int) : length regs = 8%nat ->
  exists h : Ty.tySem (Word 8), state_regs h = regs.
Proof.
  intros HL.
  destruct regs as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 rest]]]]]]]]]; try discriminate.
  set (w := fun x => @fromZ (WordToZ 5) (Int.unsigned x)).
  exists (((w r0, w r1), (w r2, w r3)), ((w r4, w r5), (w r6, w r7))).
  unfold state_regs. cbn [word32_chunks app map fst snd]. unfold w. rewrite !word32_of_int. reflexivity.
Qed.

Lemma absorb_length bs : forall (l : list (Ty.tySem (Word 3))) regs, (length l < 64)%nat ->
  Z.of_nat (length (fst (absorb l regs bs))) = (Z.of_nat (length l) + Z.of_nat (length bs)) mod 64 /\
  (length (fst (absorb l regs bs)) < 64)%nat.
Proof.
  induction bs as [|x bs IH]; intros l regs HL.
  - unfold absorb. cbn [fold_left fst length]. rewrite Z.add_0_r, Z.mod_small by lia. split; [reflexivity|exact HL].
  - destruct (Nat.eq_dec (length l) 63) as [E|E].
    + rewrite absorb_cons_full by exact E.
      destruct (IH [] (SHA256.hash_block regs (be_words (map word8_array_value (l ++ [x]))))
        ltac:(cbn; lia)) as [H1 H2].
      split; [|exact H2]. rewrite H1. cbn [length]. rewrite E.
      replace (Z.of_nat 63 + Z.of_nat (S (length bs))) with (Z.of_nat 0 + Z.of_nat (length bs) + 1 * 64) by lia.
      rewrite Z.mod_add by lia. reflexivity.
    + rewrite absorb_cons_small by lia.
      destruct (IH (l ++ [x]) regs ltac:(rewrite app_length; cbn [length]; lia)) as [H1 H2].
      split; [|exact H2]. rewrite H1, app_length. cbn [length]. f_equal. lia.
Qed.

(** ** Counter arithmetic *)
Section Counter.
Variables (r : int64) (len n : Z).
Hypothesis Hr : Int64.unsigned r < 36028797018963968.
Hypothesis Hlen : 0 <= len < 64.
Hypothesis Hn : 0 <= n <= 4096.

Let c := sha256_read_counter r (Int64.repr len).

Lemma add_counter_c : Int64.unsigned c = 64 * Int64.unsigned r + len.
Proof.
  unfold c. rewrite sha256_counter_unsigned; rewrite ?Int64.unsigned_repr;
    try (change Int64.max_unsigned with 18446744073709551615); lia.
Qed.

Lemma add_counter_sum :
  Int64.unsigned (Int64.add c (Int64.repr n)) = 64 * Int64.unsigned r + len + n.
Proof.
  pose proof (Int64.unsigned_range r) as HR.
  unfold Int64.add. rewrite add_counter_c.
  rewrite (Int64.unsigned_repr n) by (change Int64.max_unsigned with 18446744073709551615; lia).
  apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma add_counter_overflow :
  uc_overflow false c (Int64.repr n) =
    negb (Int64.unsigned r + (len + n) / 64 <? ctx8_limit).
Proof.
  pose proof (Int64.unsigned_range r) as HR.
  unfold uc_overflow. cbn [orb]. rewrite cmpu_le_bool.
  assert (HS : Int64.unsigned (Int64.sub sha_max_counter c) = 2305843009213693952 - Int64.unsigned c).
  { rewrite long_sub_unsigned; change (Int64.unsigned sha_max_counter) with 2305843009213693952;
      rewrite ?add_counter_c; lia. }
  rewrite HS, add_counter_c.
  rewrite (Int64.unsigned_repr n) by (change Int64.max_unsigned with 18446744073709551615; lia).
  unfold ctx8_limit.
  assert (HD : (len + n) = 64 * ((len + n) / 64) + (len + n) mod 64) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound (len + n) 64 ltac:(lia)) as HM.
  destruct (Z.ltb_spec (Int64.unsigned r + (len + n) / 64) 36028797018963968) as [H|H]; cbn [negb].
  - apply Z.leb_gt. lia.
  - apply Z.leb_le. lia.
Qed.

Lemma add_counter_modu :
  Int64.modu (Int64.add c (Int64.repr n)) (Int64.repr 64) = Int64.repr ((len + n) mod 64).
Proof.
  unfold Int64.modu. rewrite add_counter_sum. change (Int64.unsigned (Int64.repr 64)) with 64.
  f_equal. replace (64 * Int64.unsigned r + len + n) with (len + n + Int64.unsigned r * 64) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma add_counter_count :
  Int64.unsigned r + (len + n) / 64 < ctx8_limit ->
  decode_wide W64 (Int64.zero_ext 64 (Int64.shru (Int64.add c (Int64.repr n)) (Int64.repr 6))) =
    @fromZ (WordToZ 6) (Int64.unsigned r + (len + n) / 64).
Proof.
  intros HT. pose proof (Int64.unsigned_range r) as HR.
  assert (HD : 0 <= (len + n) / 64) by (apply Z.div_pos; lia).
  unfold decode_wide. f_equal.
  rewrite Int64.zero_ext_above by (change Int64.zwordsize with 64; lia).
  rewrite Int64.shru_div_two_p, sha256_counter_shift_constant, add_counter_sum.
  replace (64 * Int64.unsigned r + len + n) with (Int64.unsigned r * 64 + (len + n)) by lia.
  rewrite Z.div_add_l by lia.
  apply Int64.unsigned_repr. unfold ctx8_limit in HT.
  change Int64.max_unsigned with 18446744073709551615. lia.
Qed.
End Counter.
