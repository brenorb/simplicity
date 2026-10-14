(** The bytes [memcmp] sees when it is called on arrays of 32-bit words
    (SHA-256 midstates: [sumFees], [lookup_fee], the Merkle-root checks of
    exec.c): a stored word is read back as its four little-endian bytes, so
    the byte comparison of two word arrays is [Eq] exactly when the arrays
    are equal.  (The order [memcmp] induces on unequal arrays is the
    little-endian byte order, not the numeric order of the words.) *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Values Memory Memdata.
Require Import C.jet_memcmp_model.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition word_digit (x j : Z) : Z := (x / 256 ^ j) mod 256.

Definition word_bytes (w : int) : list int :=
  [Int.repr (word_digit (Int.unsigned w) 0); Int.repr (word_digit (Int.unsigned w) 1);
   Int.repr (word_digit (Int.unsigned w) 2); Int.repr (word_digit (Int.unsigned w) 3)].

Definition words_bytes (ws : list int) : list int := flat_map word_bytes ws.

Lemma word_digit_range x j : 0 <= word_digit x j < 256.
Proof. unfold word_digit. apply Z.mod_pos_bound. lia. Qed.

Lemma word_digits_decomp x : 0 <= x < 4294967296 ->
  x = word_digit x 0 + 256 * word_digit x 1 + 65536 * word_digit x 2 + 16777216 * word_digit x 3.
Proof.
  intros Hx. unfold word_digit.
  change (256 ^ 0) with 1. change (256 ^ 1) with 256. change (256 ^ 2) with 65536. change (256 ^ 3) with 16777216.
  rewrite Z.div_1_r.
  pose proof (Z.div_mod x 256 ltac:(lia)) as H0.
  pose proof (Z.div_mod (x / 256) 256 ltac:(lia)) as H1.
  pose proof (Z.div_mod (x / 256 / 256) 256 ltac:(lia)) as H2.
  pose proof (Z.mod_pos_bound x 256 ltac:(lia)) as B0.
  pose proof (Z.mod_pos_bound (x / 256) 256 ltac:(lia)) as B1.
  pose proof (Z.mod_pos_bound (x / 256 / 256) 256 ltac:(lia)) as B2.
  assert (E2 : x / 65536 = x / 256 / 256) by (rewrite Z.div_div by lia; reflexivity).
  assert (E3 : x / 16777216 = x / 256 / 256 / 256) by (rewrite !Z.div_div by lia; reflexivity).
  rewrite E2, E3.
  assert (H3 : 0 <= x / 256 / 256 / 256 < 256).
  { split; [repeat apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; [lia|]. apply Z.div_lt_upper_bound; [lia|].
    apply Z.div_lt_upper_bound; lia. }
  rewrite (Z.mod_small (x / 256 / 256 / 256) 256) by exact H3.
  lia.
Qed.

Lemma word_digits_unique x b0 b1 b2 b3 :
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  x = b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 ->
  word_digit x 0 = b0 /\ word_digit x 1 = b1 /\ word_digit x 2 = b2 /\ word_digit x 3 = b3.
Proof.
  intros H0 H1 H2 H3 Hx.
  assert (Hr : 0 <= x < 4294967296) by lia.
  pose proof (word_digits_decomp x Hr) as HD.
  pose proof (word_digit_range x 0). pose proof (word_digit_range x 1).
  pose proof (word_digit_range x 2). pose proof (word_digit_range x 3).
  lia.
Qed.

Lemma word_bytes_inj w1 w2 : word_bytes w1 = word_bytes w2 -> w1 = w2.
Proof.
  intros H.
  pose proof (f_equal (fun l => nth 0 l Int.zero) H) as E0.
  pose proof (f_equal (fun l => nth 1 l Int.zero) H) as E1.
  pose proof (f_equal (fun l => nth 2 l Int.zero) H) as E2.
  pose proof (f_equal (fun l => nth 3 l Int.zero) H) as E3.
  cbn [word_bytes nth] in E0, E1, E2, E3.
  assert (HE : forall a b, 0 <= a < 256 -> 0 <= b < 256 -> Int.repr a = Int.repr b -> a = b).
  { intros a b Ha Hb E. apply (f_equal Int.unsigned) in E.
    rewrite !Int.unsigned_repr in E by (change Int.max_unsigned with 4294967295; lia). exact E. }
  apply HE in E0; [|apply word_digit_range|apply word_digit_range].
  apply HE in E1; [|apply word_digit_range|apply word_digit_range].
  apply HE in E2; [|apply word_digit_range|apply word_digit_range].
  apply HE in E3; [|apply word_digit_range|apply word_digit_range].
  pose proof (Int.unsigned_range w1) as R1. pose proof (Int.unsigned_range w2) as R2.
  change Int.modulus with 4294967296 in R1, R2.
  pose proof (word_digits_decomp _ R1) as D1. pose proof (word_digits_decomp _ R2) as D2.
  rewrite <- (Int.repr_unsigned w1), <- (Int.repr_unsigned w2). f_equal. lia.
Qed.

Lemma words_bytes_length ws : length (words_bytes ws) = (4 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [words_bytes flat_map length app word_bytes] in *. fold (words_bytes ws). lia. Qed.

Lemma words_bytes_inj : forall ws1 ws2, length ws1 = length ws2 ->
  words_bytes ws1 = words_bytes ws2 -> ws1 = ws2.
Proof.
  induction ws1 as [|w1 ws1 IH]; intros [|w2 ws2] HL HE; try discriminate; [reflexivity|].
  cbn [words_bytes flat_map] in HE. fold (words_bytes ws1) in HE. fold (words_bytes ws2) in HE.
  assert (HW : word_bytes w1 = word_bytes w2 /\ words_bytes ws1 = words_bytes ws2).
  { split.
    - exact (f_equal (firstn 4) HE).
    - exact (f_equal (skipn 4) HE). }
  destruct HW as [HW HT]. f_equal; [apply word_bytes_inj; exact HW|].
  apply IH; [injection HL; auto|exact HT].
Qed.

(** The byte comparison of two word arrays is [Eq] exactly for equal arrays. *)
Theorem words_bytes_cmp_eq ws1 ws2 : length ws1 = length ws2 ->
  (bytes_cmp (words_bytes ws1) (words_bytes ws2) = Eq <-> ws1 = ws2).
Proof.
  intros HL. split.
  - intros HC. apply words_bytes_inj; [exact HL|].
    apply bytes_cmp_eq; [rewrite !words_bytes_length; lia|exact HC].
  - intros ->. apply bytes_cmp_refl.
Qed.

(** A stored word is read back as its four bytes. *)
Lemma loadbytes_one m b ofs n bytes i :
  Mem.loadbytes m b ofs n = Some bytes -> 0 <= i < n ->
  Mem.loadbytes m b (ofs + i) 1 = Some [nth (Z.to_nat i) bytes Undef].
Proof.
  intros HL Hi.
  replace n with (i + (n - i)) in HL by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ HL ltac:(lia) ltac:(lia)) as (b1 & b2 & L1 & L2 & E).
  replace (n - i) with (1 + (n - i - 1)) in L2 by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ L2 ltac:(lia) ltac:(lia)) as (c1 & c2 & M1 & M2 & E2).
  pose proof (Mem.loadbytes_length _ _ _ _ _ L1) as Len1.
  pose proof (Mem.loadbytes_length _ _ _ _ _ M1) as Len2. change (Z.to_nat 1) with 1%nat in Len2.
  destruct c1 as [|x [|y c1]]; try discriminate Len2.
  rewrite M1. f_equal. f_equal. subst bytes b2.
  rewrite app_nth2 by lia. rewrite Len1, Nat.sub_diag. reflexivity.
Qed.

Lemma load_word_bytes m b o w :
  Mem.load Mint32 m b o = Some (Vint w) ->
  forall j, (j < 4)%nat ->
    Mem.load Mint8unsigned m b (o + Z.of_nat j) = Some (Vint (nth j (word_bytes w) Int.zero)).
Proof.
  intros HL j Hj.
  destruct (Mem.load_loadbytes _ _ _ _ _ HL) as (bytes & HLB & HV).
  change (size_chunk Mint32) with 4 in HLB.
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLB) as HLen. change (Z.to_nat 4) with 4%nat in HLen.
  unfold decode_val in HV.
  destruct (proj_bytes bytes) as [bl|] eqn:HP; [|discriminate HV].
  pose proof (inj_proj_bytes _ _ HP) as HB. subst bytes.
  rewrite length_inj_bytes in HLen.
  destruct bl as [|b0 [|b1 [|b2 [|b3 [|b4 bl]]]]]; try discriminate HLen.
  injection HV as HV.
  assert (HD : decode_int [b0; b1; b2; b3] =
    Byte.unsigned b0 + 256 * Byte.unsigned b1 + 65536 * Byte.unsigned b2 + 16777216 * Byte.unsigned b3).
  { unfold decode_int, rev_if_be. change Archi.big_endian with false. cbn [int_of_bytes]. lia. }
  pose proof (Byte.unsigned_range b0) as R0. pose proof (Byte.unsigned_range b1) as R1.
  pose proof (Byte.unsigned_range b2) as R2. pose proof (Byte.unsigned_range b3) as R3.
  change Byte.modulus with 256 in R0, R1, R2, R3.
  assert (HU : Int.unsigned w =
    Byte.unsigned b0 + 256 * Byte.unsigned b1 + 65536 * Byte.unsigned b2 + 16777216 * Byte.unsigned b3).
  { rewrite HV, HD. apply Int.unsigned_repr. change Int.max_unsigned with 4294967295. lia. }
  destruct (word_digits_unique _ _ _ _ _ R0 R1 R2 R3 HU) as (D0 & D1 & D2 & D3).
  pose proof (loadbytes_one m b o 4 _ (Z.of_nat j) HLB ltac:(lia)) as HOne.
  rewrite Nat2Z.id in HOne.
  pose proof (Mem.loadbytes_load Mint8unsigned m b (o + Z.of_nat j) _ HOne (Z.divide_1_l _)) as HLd.
  rewrite HLd. unfold word_bytes. rewrite D0, D1, D2, D3.
  assert (HDec : forall x : byte, decode_val Mint8unsigned [Byte x] = Vint (Int.repr (Byte.unsigned x))).
  { intros x. unfold decode_val. cbn [proj_bytes]. unfold decode_int, rev_if_be.
    change Archi.big_endian with false. cbn [int_of_bytes]. rewrite Z.add_0_r.
    f_equal.
    pose proof (Byte.unsigned_range x) as Rx. change Byte.modulus with 256 in Rx.
    apply Int.same_bits_eq. intros i Hi. rewrite Int.bits_zero_ext by lia.
    destruct (zlt i 8) as [Hlt|Hge]; [reflexivity|].
    rewrite Int.testbit_repr by exact Hi. symmetry.
    apply (Zbits.Ztestbit_above 8); [change (two_power_nat 8) with 256; lia|cbn; lia]. }
  destruct j as [|[|[|[|j]]]]; cbn [nth inj_bytes map]; try lia; apply f_equal; apply HDec.
Qed.

(** A readable word array is a readable byte range holding its bytes. *)
Lemma nth_words_bytes : forall ws q r, (q < length ws)%nat -> (r < 4)%nat ->
  nth (4 * q + r) (words_bytes ws) Int.zero = nth r (word_bytes (nth q ws Int.zero)) Int.zero.
Proof.
  induction ws as [|w ws IH]; intros q r Hq Hr; [cbn in Hq; lia|].
  cbn [words_bytes flat_map]. fold (words_bytes ws).
  destruct q as [|q].
  - rewrite app_nth1 by (cbn; lia). reflexivity.
  - rewrite app_nth2 by (cbn; lia). cbn [length word_bytes nth].
    replace (4 * S q + r - 4)%nat with (4 * q + r)%nat by lia.
    apply IH; [cbn in Hq; lia|exact Hr].
Qed.

Theorem words_bytes_at m b o (ws : list int) :
  (forall i x, nth_error ws i = Some x -> Mem.load Mint32 m b (o + 4 * Z.of_nat i) = Some (Vint x)) ->
  bytes_at m b o (words_bytes ws).
Proof.
  intros HW i Hi. rewrite words_bytes_length in Hi.
  set (q := (i / 4)%nat). set (r := (i mod 4)%nat).
  assert (Hqr : i = (4 * q + r)%nat) by (unfold q, r; apply Nat.div_mod; lia).
  assert (Hr : (r < 4)%nat) by (unfold r; apply Nat.mod_upper_bound; lia).
  assert (Hq : (q < length ws)%nat) by lia.
  rewrite Hqr at 2. rewrite nth_words_bytes by assumption.
  replace (o + Z.of_nat i) with (o + 4 * Z.of_nat q + Z.of_nat r) by lia.
  apply load_word_bytes; [|exact Hr].
  apply HW. apply nth_error_nth'. exact Hq.
Qed.
