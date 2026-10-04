(** Bridge between the ctx8Finalize option semantics and the C
    [sha256_finalize]: both absorb the SHA-256 padding of the context. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks C.jet_predicate_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_uchars_prep.
Require Import C.jet_sha_uchars_exec C.jet_sha_be64_exec C.jet_sha_finalize_exec C.jet_sha_finalize_spec.
Require Import C.jet_sha_ctx8_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

(** ** Big-endian bytes of a 64-bit word *)
Lemma c255_and (y : int64) : Int64.and c255 y = Int64.zero_ext 8 y.
Proof.
  rewrite Int64.and_commut. symmetry. change c255 with (Int64.repr (two_p 8 - 1)).
  apply Int64.zero_ext_and. lia.
Qed.

Lemma zero_ext8_repr (v : Z) : 0 <= v < 256 -> Int.zero_ext 8 (Int.repr v) = Int.repr v.
Proof.
  intros Hv. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 (Int.repr v))).
  rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  change (two_p 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma c_be64_shift_value (x : int64) (k : Z) : 0 <= k < 64 ->
  c_be64_shift x k = Int.repr ((Int64.unsigned x / 2 ^ k) mod 256).
Proof.
  intros Hk. unfold c_be64_shift. rewrite c255_and.
  pose proof (Int64.unsigned_range x) as HX.
  assert (HS : Int64.unsigned (Int64.shru' x (Int.repr k)) = Int64.unsigned x / 2 ^ k).
  { unfold Int64.shru'.
    rewrite (Int.unsigned_repr k) by (change Int.max_unsigned with 4294967295; lia).
    rewrite Z.shiftr_div_pow2 by lia. apply Int64.unsigned_repr.
    assert (0 < 2 ^ k) by (apply Z.pow_pos_nonneg; lia).
    assert (Int64.unsigned x / 2 ^ k <= Int64.unsigned x) by (apply Z.div_le_upper_bound; nia).
    assert (0 <= Int64.unsigned x / 2 ^ k) by (apply Z.div_pos; lia).
    unfold Int64.max_unsigned. lia. }
  unfold Int64.loword. rewrite Int64.zero_ext_mod by (change Int64.zwordsize with 64; lia).
  rewrite HS. change (two_p 8) with 256.
  apply zero_ext8_repr. apply Z.mod_pos_bound. lia.
Qed.

Lemma c_be64_low_value (x : int64) : c_be64_low x = Int.repr (Int64.unsigned x mod 256).
Proof.
  unfold c_be64_low. rewrite c255_and. unfold Int64.loword.
  rewrite Int64.zero_ext_mod by (change Int64.zwordsize with 64; lia).
  change (two_p 8) with 256. apply zero_ext8_repr. apply Z.mod_pos_bound. lia.
Qed.

Lemma toZ_word64_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : Ty.tySem (Word 3)) :
  @toZ (WordToZ 6) (((b0, b1), (b2, b3)), ((b4, b5), (b6, b7))) =
    ((@toZ (WordToZ 3) b0 * 256 + @toZ (WordToZ 3) b1) * 65536 +
     (@toZ (WordToZ 3) b2 * 256 + @toZ (WordToZ 3) b3)) * 4294967296 +
    ((@toZ (WordToZ 3) b4 * 256 + @toZ (WordToZ 3) b5) * 65536 +
     (@toZ (WordToZ 3) b6 * 256 + @toZ (WordToZ 3) b7)).
Proof. reflexivity. Qed.

Lemma be64_bytes_word (W : Ty.tySem (Word 6)) :
  c_be64_bytes (Int64.repr (@toZ (WordToZ 6) W)) = map word8_array_value (vector_values (Word 3) 3 W).
Proof.
  pose proof (word64_range W) as HW.
  assert (HU : Int64.unsigned (Int64.repr (@toZ (WordToZ 6) W)) = @toZ (WordToZ 6) W)
    by (apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia).
  destruct W as [[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]].
  change (vector_values (Word 3) 3 (b0, b1, (b2, b3), (b4, b5, (b6, b7)))) with [b0; b1; b2; b3; b4; b5; b6; b7].
  unfold c_be64_bytes. rewrite !c_be64_shift_value by lia. rewrite c_be64_low_value. rewrite HU.
  rewrite toZ_word64_bytes.
  pose proof (word_value_bounds 3 b0) as B0. pose proof (word_value_bounds 3 b1) as B1.
  pose proof (word_value_bounds 3 b2) as B2. pose proof (word_value_bounds 3 b3) as B3.
  pose proof (word_value_bounds 3 b4) as B4. pose proof (word_value_bounds 3 b5) as B5.
  pose proof (word_value_bounds 3 b6) as B6. pose proof (word_value_bounds 3 b7) as B7.
  change (word_modulus 3) with 256 in *.
  set (z0 := @toZ (WordToZ 3) b0) in *. set (z1 := @toZ (WordToZ 3) b1) in *.
  set (z2 := @toZ (WordToZ 3) b2) in *. set (z3 := @toZ (WordToZ 3) b3) in *.
  set (z4 := @toZ (WordToZ 3) b4) in *. set (z5 := @toZ (WordToZ 3) b5) in *.
  set (z6 := @toZ (WordToZ 3) b6) in *. set (z7 := @toZ (WordToZ 3) b7) in *.
  set (N := ((z0 * 256 + z1) * 65536 + (z2 * 256 + z3)) * 4294967296 + ((z4 * 256 + z5) * 65536 + (z6 * 256 + z7))).
  cbn [map]. unfold word8_array_value. fold z0 z1 z2 z3 z4 z5 z6 z7.
  assert (E0 : (N / 2 ^ 56) mod 256 = z0).
  { assert (HQ : N / 2 ^ 56 = z0).
    { symmetry. apply (Z.div_unique N (2 ^ 56) (z0) (z1 * 281474976710656 + z2 * 1099511627776 + z3 * 4294967296 + z4 * 16777216 + z5 * 65536 + z6 * 256 + z7 * 1)); [left; change (2 ^ 56) with 72057594037927936; lia|].
      change (2 ^ 56) with 72057594037927936. unfold N. lia. }
    rewrite HQ. symmetry. apply (Z.mod_unique _ _ (0)); [left; lia|lia]. }
  assert (E1 : (N / 2 ^ 48) mod 256 = z1).
  { assert (HQ : N / 2 ^ 48 = (z0 * 256 + z1)).
    { symmetry. apply (Z.div_unique N (2 ^ 48) ((z0 * 256 + z1)) (z2 * 1099511627776 + z3 * 4294967296 + z4 * 16777216 + z5 * 65536 + z6 * 256 + z7 * 1)); [left; change (2 ^ 48) with 281474976710656; lia|].
      change (2 ^ 48) with 281474976710656. unfold N. lia. }
    rewrite HQ. symmetry. apply (Z.mod_unique _ _ (z0)); [left; lia|lia]. }
  assert (E2 : (N / 2 ^ 40) mod 256 = z2).
  { assert (HQ : N / 2 ^ 40 = ((z0 * 256 + z1) * 256 + z2)).
    { symmetry. apply (Z.div_unique N (2 ^ 40) (((z0 * 256 + z1) * 256 + z2)) (z3 * 4294967296 + z4 * 16777216 + z5 * 65536 + z6 * 256 + z7 * 1)); [left; change (2 ^ 40) with 1099511627776; lia|].
      change (2 ^ 40) with 1099511627776. unfold N. lia. }
    rewrite HQ. symmetry. apply (Z.mod_unique _ _ ((z0 * 256 + z1))); [left; lia|lia]. }
  assert (E3 : (N / 2 ^ 32) mod 256 = z3).
  { assert (HQ : N / 2 ^ 32 = (((z0 * 256 + z1) * 256 + z2) * 256 + z3)).
    { symmetry. apply (Z.div_unique N (2 ^ 32) ((((z0 * 256 + z1) * 256 + z2) * 256 + z3)) (z4 * 16777216 + z5 * 65536 + z6 * 256 + z7 * 1)); [left; change (2 ^ 32) with 4294967296; lia|].
      change (2 ^ 32) with 4294967296. unfold N. lia. }
    rewrite HQ. symmetry. apply (Z.mod_unique _ _ (((z0 * 256 + z1) * 256 + z2))); [left; lia|lia]. }
  assert (E4 : (N / 2 ^ 24) mod 256 = z4).
  { assert (HQ : N / 2 ^ 24 = ((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4)).
    { symmetry. apply (Z.div_unique N (2 ^ 24) (((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4)) (z5 * 65536 + z6 * 256 + z7 * 1)); [left; change (2 ^ 24) with 16777216; lia|].
      change (2 ^ 24) with 16777216. unfold N. lia. }
    rewrite HQ. symmetry. apply (Z.mod_unique _ _ ((((z0 * 256 + z1) * 256 + z2) * 256 + z3))); [left; lia|lia]. }
  assert (E5 : (N / 2 ^ 16) mod 256 = z5).
  { assert (HQ : N / 2 ^ 16 = (((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4) * 256 + z5)).
    { symmetry. apply (Z.div_unique N (2 ^ 16) ((((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4) * 256 + z5)) (z6 * 256 + z7 * 1)); [left; change (2 ^ 16) with 65536; lia|].
      change (2 ^ 16) with 65536. unfold N. lia. }
    rewrite HQ. symmetry. apply (Z.mod_unique _ _ (((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4))); [left; lia|lia]. }
  assert (E6 : (N / 2 ^ 8) mod 256 = z6).
  { assert (HQ : N / 2 ^ 8 = ((((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4) * 256 + z5) * 256 + z6)).
    { symmetry. apply (Z.div_unique N (2 ^ 8) (((((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4) * 256 + z5) * 256 + z6)) (z7 * 1)); [left; change (2 ^ 8) with 256; lia|].
      change (2 ^ 8) with 256. unfold N. lia. }
    rewrite HQ. symmetry. apply (Z.mod_unique _ _ ((((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4) * 256 + z5))); [left; lia|lia]. }
  assert (E7 : N mod 256 = z7).
  { symmetry. apply (Z.mod_unique _ _ (((((((z0 * 256 + z1) * 256 + z2) * 256 + z3) * 256 + z4) * 256 + z5) * 256 + z6))); [left; lia|unfold N; lia]. }
  rewrite E0, E1, E2, E3, E4, E5, E6, E7. reflexivity.
Qed.

(** ** Padding: the two procedures agree *)
Lemma firstn_repeat {A} (x : A) : forall n m, firstn n (repeat x m) = repeat x (Nat.min n m).
Proof.
  induction n; intros m; [reflexivity|]. destruct m; [reflexivity|].
  cbn [repeat firstn Nat.min]. rewrite IHn. reflexivity.
Qed.

Lemma pad_bytes_shape c :
  pad_bytes c = Int.repr 128 :: repeat Int.zero (Z.to_nat ((119 - Int64.unsigned c mod 64) mod 64)).
Proof.
  pose proof (pad_count_unsigned c) as HP.
  pose proof (Z.mod_pos_bound (119 - Int64.unsigned c mod 64) 64 ltac:(lia)) as HM.
  unfold pad_bytes, pad_source. rewrite HP.
  replace (Z.to_nat (1 + (119 - Int64.unsigned c mod 64) mod 64)) with
    (S (Z.to_nat ((119 - Int64.unsigned c mod 64) mod 64))) by lia.
  cbn [firstn]. rewrite firstn_repeat. f_equal. f_equal. lia.
Qed.

Lemma pad_equiv (l regs LB : list int) (c : int64) :
  Z.of_nat (length l) = Int64.unsigned c mod 64 -> length LB = 8%nat ->
  let st := absorb_i l regs (Int.repr 128 :: repeat Int.zero 7) in
  SHA256.hash_block (snd st)
    (be_words (firstn 56 (fst st ++ repeat Int.zero (64 - length (fst st))) ++ LB)) =
  snd (absorb_i l regs (pad_bytes c ++ LB)).
Proof.
  intros HL HLB.
  pose proof (Z.mod_pos_bound (Int64.unsigned c) 64 ltac:(lia)) as HM.
  rewrite pad_bytes_shape, <- HL.
  set (L := length l) in *.
  destruct (le_lt_dec L 55) as [Hs|Hs].
  - (* the padding fits in the current block *)
    assert (HP : Z.to_nat ((119 - Z.of_nat L) mod 64) = (55 - L)%nat).
    { replace (119 - Z.of_nat L) with (55 - Z.of_nat L + 1 * 64) by lia.
      rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia. }
    rewrite HP. cbv zeta.
    rewrite (absorb_i_small (Int.repr 128 :: repeat Int.zero 7) l regs)
      by (cbn [length]; rewrite repeat_length; fold L; lia).
    cbn [fst snd].
    assert (HF : firstn 56 ((l ++ Int.repr 128 :: repeat Int.zero 7) ++
        repeat Int.zero (64 - length (l ++ Int.repr 128 :: repeat Int.zero 7))) =
      l ++ Int.repr 128 :: repeat Int.zero (55 - L)).
    { rewrite app_length. cbn [length]. rewrite repeat_length. fold L.
      rewrite <- app_assoc. rewrite firstn_app. rewrite firstn_all2 by (fold L; lia). fold L.
      f_equal. cbn [app]. replace (56 - L)%nat with (S (55 - L)) by lia. cbn [firstn]. f_equal.
      rewrite <- repeat_app, firstn_repeat. f_equal. lia. }
    rewrite HF.
    rewrite (absorb_i_fill l regs ((Int.repr 128 :: repeat Int.zero (55 - L)) ++ LB)).
    + cbn [snd]. rewrite <- app_assoc. reflexivity.
    + rewrite app_length. cbn [length]. rewrite repeat_length, HLB. fold L. lia.
    + discriminate.
  - (* the padding completes the current block and starts another *)
    assert (HL64 : (L < 64)%nat) by lia.
    assert (HP : Z.to_nat ((119 - Z.of_nat L) mod 64) = (119 - L)%nat).
    { rewrite Z.mod_small by lia. lia. }
    rewrite HP. cbv zeta.
    set (b1 := Int.repr 128 :: repeat Int.zero (63 - L)).
    set (H1 := SHA256.hash_block regs (be_words (l ++ b1))).
    assert (Hb1 : (length l + length b1 = 64)%nat).
    { unfold b1. cbn [length]. rewrite repeat_length. fold L. lia. }
    assert (Hb1n : b1 <> []) by discriminate.
    assert (E8 : Int.repr 128 :: repeat Int.zero 7 = b1 ++ repeat Int.zero (L - 56)).
    { unfold b1. cbn [app]. f_equal. rewrite <- repeat_app. f_equal. lia. }
    assert (EP : (Int.repr 128 :: repeat Int.zero (119 - L)) ++ LB = b1 ++ (repeat Int.zero 56 ++ LB)).
    { unfold b1. cbn [app]. f_equal. rewrite app_assoc, <- repeat_app. f_equal. f_equal. lia. }
    rewrite E8, EP.
    rewrite (absorb_i_app l regs b1 (repeat Int.zero (L - 56))),
      (absorb_i_app l regs b1 (repeat Int.zero 56 ++ LB)), (absorb_i_fill l regs b1 Hb1 Hb1n).
    cbn [fst snd]. fold H1.
    rewrite (absorb_i_small (repeat Int.zero (L - 56)) [] H1) by (rewrite repeat_length; cbn [length]; lia).
    cbn [fst snd app]. rewrite repeat_length.
    rewrite <- repeat_app, firstn_repeat.
    replace (Nat.min 56 (L - 56 + (64 - (L - 56)))) with 56%nat by lia.
    rewrite (absorb_i_fill [] H1 (repeat Int.zero 56 ++ LB)).
    + reflexivity.
    + rewrite app_length, repeat_length, HLB. reflexivity.
    + destruct LB; [discriminate|]. intro HN. apply (f_equal (@length int)) in HN.
      rewrite app_length, repeat_length in HN. cbn in HN. lia.
Qed.

(** ** The final block *)
Lemma finalize_block_bytes (P : Ty.tySem (Word 9)) (H : Ty.tySem (Word 8)) (LEN : Ty.tySem (Word 6)) :
  fst (@ctx8_finalize_block_spec Alg.CoreFunSem ((P, H), LEN)) = H /\
  vector_values (Word 3) 6 (snd (@ctx8_finalize_block_spec Alg.CoreFunSem ((P, H), LEN))) =
    firstn 56 (vector_values (Word 3) 6 P) ++ vector_values (Word 3) 3 LEN.
Proof.
  destruct P as [P0 [P1a [P1ba P1bb]]]. split; [reflexivity|].
  change (@ctx8_finalize_block_spec Alg.CoreFunSem (P0, (P1a, (P1ba, P1bb)), H, LEN)) with
    (H, (P0, (P1a, (P1ba, LEN)))).
  cbn [snd].
  change (vector_values (Word 3) 6 (P0, (P1a, (P1ba, LEN)))) with
    (vector_values (Word 3) 5 P0 ++ (vector_values (Word 3) 4 P1a ++
      (vector_values (Word 3) 3 P1ba ++ vector_values (Word 3) 3 LEN))).
  change (vector_values (Word 3) 6 (P0, (P1a, (P1ba, P1bb)))) with
    (vector_values (Word 3) 5 P0 ++ (vector_values (Word 3) 4 P1a ++
      (vector_values (Word 3) 3 P1ba ++ vector_values (Word 3) 3 P1bb))).
  pose proof (vector_values_length (Word 3) 5 P0) as L0.
  pose proof (vector_values_length (Word 3) 4 P1a) as L1.
  pose proof (vector_values_length (Word 3) 3 P1ba) as L2.
  change (Nat.pow 2 5) with 32%nat in L0. change (Nat.pow 2 4) with 16%nat in L1.
  change (Nat.pow 2 3) with 8%nat in L2.
  rewrite !app_assoc.
  rewrite firstn_app.
  rewrite firstn_all2 by (rewrite !app_length; lia).
  rewrite !app_length, L0, L1, L2. cbn [Nat.sub firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma pad8_bytes_ints : map word8_array_value pad8_bytes = Int.repr 128 :: repeat Int.zero 7.
Proof. reflexivity. Qed.

Lemma zero8_int : word8_array_value zero8 = Int.zero.
Proof. reflexivity. Qed.

(** ** The closed form of ctx8Finalize *)
Theorem ctx8_finalize_closed (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6))
    (h : Ty.tySem (Word 8)) :
  let l0 := buffer_list (Word 3) 5 buf in
  let c := Int64.repr (64 * @toZ (WordToZ 6) count + Z.of_nat (length l0)) in
  (@toZ (WordToZ 6) count < ctx8_limit ->
     exists hf, @ctx8_finalize_spec optalg (buf, (count, h)) = Some hf /\
       state_regs hf = snd (absorb_i (map word8_array_value l0) (state_regs h) (sha_pad c))) /\
  (ctx8_limit <= @toZ (WordToZ 6) count -> @ctx8_finalize_spec optalg (buf, (count, h)) = None).
Proof.
  intros l0 c. rewrite ctx8_finalize_option. split.
  2:{ intros HG. apply Z.ltb_ge in HG. rewrite HG. reflexivity. }
  intros HC. pose proof HC as HC'0. pose proof HC as HC'. apply Z.ltb_lt in HC'. rewrite HC'. unfold ctx8_limit in HC.
  pose proof (word64_range count) as HR.
  pose proof (buffer_list_length (Word 3) 5 buf) as HL. change (Nat.pow 2 6) with 64%nat in HL. fold l0 in HL.
  (* the eight padding bytes always fit the counter (it was cleared) *)
  assert (Hne : pad8_bytes <> []) by discriminate.
  destruct (ctx8_add_list_closed pad8_bytes buf zero64 h Hne) as [HCa _].
  fold l0 in HCa. change (@toZ (WordToZ 6) zero64) with 0 in HCa. change (length pad8_bytes) with 8%nat in HCa.
  assert (HT : 0 + (Z.of_nat (length l0) + Z.of_nat 8) / 64 < ctx8_limit).
  { assert ((Z.of_nat (length l0) + Z.of_nat 8) / 64 < 2) by (apply Z.div_lt_upper_bound; lia).
    unfold ctx8_limit. lia. }
  destruct (HCa HT) as (buf2 & h2 & HAdd & HB2 & HR2).
  rewrite HAdd. cbn [fst snd].
  eexists. split; [reflexivity|].
  set (P := @buffer_pad_spec 5 Alg.CoreFunSem buf2).
  set (LEN := @ctx8_bitlen_spec Alg.CoreFunSem (buf, (count, h))).
  destruct (finalize_block_bytes P h2 LEN) as [HF1 HF2].
  set (BLK := snd (@ctx8_finalize_block_spec Alg.CoreFunSem (P, h2, LEN))) in *.
  assert (HE : @ctx8_finalize_block_spec Alg.CoreFunSem (P, h2, LEN) = (h2, BLK)).
  { rewrite <- HF1. unfold BLK. apply surjective_pairing. }
  transitivity (state_regs (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (h2, BLK)));
    [apply f_equal, f_equal; exact HE|].
  assert (HF2' : vector_values (Word 3) 6 BLK =
    firstn 56 (vector_values (Word 3) 6 P) ++ vector_values (Word 3) 3 LEN) by exact HF2.
  rewrite hashBlock_regs, HF2', HR2.
  unfold P. rewrite buffer_pad_value, HB2.
  rewrite map_app, <- firstn_map, map_app, map_repeat, zero8_int.
  pose proof (absorb_i_map l0 (state_regs h) pad8_bytes) as HM. rewrite pad8_bytes_ints in HM.
  set (A := absorb l0 (state_regs h) pad8_bytes) in *.
  assert (HA1 : map word8_array_value (fst A) =
    fst (absorb_i (map word8_array_value l0) (state_regs h) (Int.repr 128 :: repeat Int.zero 7)))
    by (rewrite HM; reflexivity).
  assert (HA2 : snd A = snd (absorb_i (map word8_array_value l0) (state_regs h) (Int.repr 128 :: repeat Int.zero 7)))
    by (rewrite HM; reflexivity).
  assert (HA3 : length (fst A) =
    length (fst (absorb_i (map word8_array_value l0) (state_regs h) (Int.repr 128 :: repeat Int.zero 7))))
    by (rewrite <- HA1, map_length; reflexivity).
  rewrite HA1, HA2, HA3.
  assert (HcU : Int64.unsigned c = 64 * @toZ (WordToZ 6) count + Z.of_nat (length l0)).
  { unfold c. apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. lia. }
  assert (HLB : map word8_array_value (vector_values (Word 3) 3 LEN) =
    c_be64_bytes (Int64.mul c (Int64.repr 8))).
  { rewrite <- be64_bytes_word. f_equal. unfold LEN.
    rewrite ctx8_bitlen_value by exact HC'0. fold l0.
    unfold Int64.mul. rewrite HcU. reflexivity. }
  rewrite HLB. unfold sha_pad.
  apply (pad_equiv (map word8_array_value l0) (state_regs h) (c_be64_bytes (Int64.mul c (Int64.repr 8))) c).
  - rewrite map_length, HcU. fold l0.
    replace (64 * @toZ (WordToZ 6) count + Z.of_nat (length l0)) with
      (Z.of_nat (length l0) + @toZ (WordToZ 6) count * 64) by lia.
    rewrite Z.mod_add by lia. symmetry. apply Z.mod_small. lia.
  - reflexivity.
Qed.
