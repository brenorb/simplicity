(** Closed byte-list form of the ctx8Add option semantics.
    Adding the bytes [bs] to a context whose buffer holds the bytes [l]
    appends them, compresses every completed 64-byte block (as sixteen
    big-endian words) and counts it; the result exists exactly when the final
    compression count is below 2^55.  This is the form the C functions
    [sha256_uchars] / [simplicity_write_sha256_context] are compared with. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks C.jet_toZ C.jet_predicate_spec.
Require Import C.jet_sha_ctx8_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

(** ** Big-endian words of a byte list *)
Definition be32 (b0 b1 b2 b3 : int) : int :=
  Int.repr (Int.unsigned b0 * 16777216 + Int.unsigned b1 * 65536 + Int.unsigned b2 * 256 + Int.unsigned b3).

Fixpoint be_words (bs : list int) : list int :=
  match bs with
  | b0 :: b1 :: b2 :: b3 :: rest => be32 b0 b1 b2 b3 :: be_words rest
  | _ => []
  end.

Definition word_bytes (w : Ty.tySem (Word 5)) : list (Ty.tySem (Word 3)) :=
  vector_values (Word 3) 2 w.

Lemma word8_array_value_unsigned (x : Ty.tySem (Word 3)) :
  Int.unsigned (word8_array_value x) = @toZ (WordToZ 3) x.
Proof.
  pose proof (word_value_bounds 3 x) as HR. change (word_modulus 3) with 256 in HR.
  unfold word8_array_value. apply Int.unsigned_repr.
  change Int.max_unsigned with 4294967295. lia.
Qed.

Lemma word32_from_bytes (w : Ty.tySem (Word 5)) :
  be_words (map word8_array_value (word_bytes w)) = [word32_array_value w].
Proof.
  destruct w as [[b0 b1] [b2 b3]].
  change (word_bytes (b0, b1, (b2, b3))) with [b0; b1; b2; b3].
  cbn [map be_words]. unfold be32, word32_array_value.
  rewrite !word8_array_value_unsigned.
  pose proof (@toZ_Pair (PairToZ (WordToZ 3) (WordToZ 3)) (PairToZ (WordToZ 3) (WordToZ 3))
    (b0, b1) (b2, b3)) as E1.
  pose proof (@toZ_Pair (WordToZ 3) (WordToZ 3) b0 b1) as E2.
  pose proof (@toZ_Pair (WordToZ 3) (WordToZ 3) b2 b3) as E3.
  match type of E1 with _ = ?A * ?P + ?B =>
    assert (EA : A = @toZ (WordToZ 3) b0 * 256 + @toZ (WordToZ 3) b1) by exact E2;
    assert (EB : B = @toZ (WordToZ 3) b2 * 256 + @toZ (WordToZ 3) b3) by exact E3;
    assert (EP : P = 65536) by reflexivity;
    rewrite EA, EB, EP in E1
  end.
  do 2 f_equal. etransitivity; [|symmetry; exact E1]. lia.
Qed.

Lemma be_words_flat (ws : list (Ty.tySem (Word 5))) :
  be_words (map word8_array_value (flat_map word_bytes ws)) = map word32_array_value ws.
Proof.
  induction ws as [|w ws IH]; [reflexivity|].
  cbn [flat_map map]. rewrite map_app.
  pose proof (word32_from_bytes w) as HW.
  destruct w as [[b0 b1] [b2 b3]].
  change (word_bytes (b0, b1, (b2, b3))) with [b0; b1; b2; b3] in HW |- *.
  cbn [map app be_words] in HW |- *.
  apply (f_equal (fun l => hd Int.zero l)) in HW. cbn [hd] in HW. rewrite HW, IH. reflexivity.
Qed.

Lemma block_bytes_chunks (blk : Ty.tySem (Word 9)) :
  flat_map word_bytes (word32_chunks 4 blk) = vector_values (Word 3) 6 blk.
Proof. reflexivity. Qed.

Lemma block_be_words (blk : Ty.tySem (Word 9)) :
  be_words (map word8_array_value (vector_values (Word 3) 6 blk)) =
    map word32_array_value (word32_chunks 4 blk).
Proof. rewrite <- block_bytes_chunks. apply be_words_flat. Qed.

Lemma hash256_reg_chunks (h : Ty.tySem Word256) :
  hash256_reg (to_hash256 h) = map word32_array_value (word32_chunks 3 h).
Proof. destruct h as [[[h0 h1] [h2 h3]] [[h4 h5] [h6 h7]]]. reflexivity. Qed.

Lemma repr_Block_chunks (b : Ty.tySem Word512) :
  Simplicity.SHA256.repr_Block b = map word32_array_value (word32_chunks 4 b).
Proof.
  destruct b as [b0 b1]. unfold Simplicity.SHA256.repr_Block. rewrite !hash256_reg_chunks.
  change (word32_chunks 4 (b0, b1)) with (word32_chunks 3 b0 ++ word32_chunks 3 b1).
  rewrite map_app. reflexivity.
Qed.

Definition state_regs (h : Ty.tySem (Word 8)) : list int := map word32_array_value (word32_chunks 3 h).

Lemma hashBlock_regs (h : Ty.tySem (Word 8)) (blk : Ty.tySem (Word 9)) :
  state_regs (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (h, blk)) =
    SHA256.hash_block (state_regs h) (be_words (map word8_array_value (vector_values (Word 3) 6 blk))).
Proof.
  unfold state_regs. rewrite block_be_words, <- !hash256_reg_chunks, <- repr_Block_chunks.
  exact (Simplicity.SHA256.hashBlock_correct h blk).
Qed.

(** ** Buffer sizes *)
Lemma buffer_list_length X depth (b : Ty.tySem (buffer_type X depth)) :
  (length (buffer_list X depth b) < Nat.pow 2 (S depth))%nat.
Proof.
  induction depth.
  - destruct b as [[]|y]; cbn; lia.
  - destruct b as [sv b0]. cbn [buffer_list fst snd]. rewrite app_length.
    specialize (IHdepth b0).
    assert (HS : (length (match sv with inl _ => [] | inr v => vector_values X (S depth) v end)
        <= Nat.pow 2 (S depth))%nat).
    { destruct sv as [u|v]; [cbn [length]; lia|rewrite vector_values_length; lia]. }
    change (Nat.pow 2 (S (S depth))) with (2 * Nat.pow 2 (S depth))%nat. lia.
Qed.

(** ** The byte-list model *)
Definition absorb_step (st : list (Ty.tySem (Word 3)) * list int) (x : Ty.tySem (Word 3)) :
    list (Ty.tySem (Word 3)) * list int :=
  let l' := fst st ++ [x] in
  if Nat.eqb (length l') 64
  then ([], SHA256.hash_block (snd st) (be_words (map word8_array_value l')))
  else (l', snd st).

Definition absorb (l : list (Ty.tySem (Word 3))) (regs : list int) (bs : list (Ty.tySem (Word 3))) :=
  fold_left absorb_step bs (l, regs).

Lemma ctx8_add1_closed (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6))
    (h : Ty.tySem (Word 8)) (x : Ty.tySem (Word 3)) :
  let l := buffer_list (Word 3) 5 buf in
  ((length l < 63)%nat /\ exists buf', buffer_list (Word 3) 5 buf' = l ++ [x] /\
     ctx8_add1_model (buf, (count, h)) x =
       if @toZ (WordToZ 6) count <? ctx8_limit then Some (buf', (count, h)) else None) \/
  ((length l = 63)%nat /\ exists h',
     state_regs h' = SHA256.hash_block (state_regs h) (be_words (map word8_array_value (l ++ [x]))) /\
     ctx8_add1_model (buf, (count, h)) x =
       if @toZ (WordToZ 6) count + 1 <? ctx8_limit
       then Some (buffer_empty_value (Word 3) 5, (@fromZ (WordToZ 6) (@toZ (WordToZ 6) count + 1), h'))
       else None).
Proof.
  intros l. unfold ctx8_add1_model.
  pose proof (buffer_snoc_value (Word 3) 5 buf x) as HS. fold l in HS.
  pose proof (buffer_list_length (Word 3) 5 buf) as HL. fold l in HL.
  change (Nat.pow 2 6) with 64%nat in HL.
  match goal with |- context[@buffer_snoc_spec ?X ?d ?alg ?p] =>
    change (@buffer_snoc_spec (Word 3) 5 Alg.CoreFunSem (buf, x)) with (@buffer_snoc_spec X d alg p) in HS;
    destruct (@buffer_snoc_spec X d alg p) as [blk|buf']
  end.
  - right. pose proof (vector_values_length (Word 3) 6 blk) as HV. rewrite HS, app_length in HV.
    change (Nat.pow 2 6) with 64%nat in HV. cbn [length] in HV.
    split; [lia|]. exists (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (h, blk)).
    split; [|reflexivity]. rewrite hashBlock_regs, HS. reflexivity.
  - left. pose proof (buffer_list_length (Word 3) 5 buf') as HL'. rewrite HS, app_length in HL'.
    change (Nat.pow 2 6) with 64%nat in HL'. cbn [length] in HL'.
    split; [lia|]. exists buf'. split; [exact HS|reflexivity].
Qed.

Lemma absorb_cons_small l regs x bs : (length l < 63)%nat ->
  absorb l regs (x :: bs) = absorb (l ++ [x]) regs bs.
Proof.
  intros HL. unfold absorb. cbn [fold_left]. unfold absorb_step at 2. cbn [fst snd].
  assert (HE : Nat.eqb (length (l ++ [x])) 64 = false)
    by (apply Nat.eqb_neq; rewrite app_length; cbn [length]; lia).
  rewrite HE. reflexivity.
Qed.

Lemma absorb_cons_full l regs x bs : length l = 63%nat ->
  absorb l regs (x :: bs) =
    absorb [] (SHA256.hash_block regs (be_words (map word8_array_value (l ++ [x])))) bs.
Proof.
  intros HL. unfold absorb. cbn [fold_left]. unfold absorb_step at 2. cbn [fst snd].
  assert (HE : Nat.eqb (length (l ++ [x])) 64 = true)
    by (apply Nat.eqb_eq; rewrite app_length; cbn [length]; lia).
  rewrite HE. reflexivity.
Qed.

Lemma div64_small n : 0 <= n < 64 -> n / 64 = 0.
Proof. apply Z.div_small. Qed.
Lemma div64_step n : (64 + n) / 64 = 1 + n / 64.
Proof. replace (64 + n) with (n + 1 * 64) by lia. rewrite Z.div_add by lia. lia. Qed.
Lemma div64_nonneg n : 0 <= n -> 0 <= n / 64.
Proof. intros H. apply Z.div_pos; lia. Qed.

Theorem ctx8_add_list_closed (bs : list (Ty.tySem (Word 3))) :
  forall (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6)) (h : Ty.tySem (Word 8)),
  bs <> [] ->
  let l := buffer_list (Word 3) 5 buf in
  let total := @toZ (WordToZ 6) count + (Z.of_nat (length l) + Z.of_nat (length bs)) / 64 in
  (total < ctx8_limit -> exists buf' h',
     ctx8_add_list (buf, (count, h)) bs = Some (buf', (@fromZ (WordToZ 6) total, h')) /\
     buffer_list (Word 3) 5 buf' = fst (absorb l (state_regs h) bs) /\
     state_regs h' = snd (absorb l (state_regs h) bs)) /\
  (ctx8_limit <= total -> ctx8_add_list (buf, (count, h)) bs = None).
Proof.
  induction bs as [|x bs IH]; intros buf count h Hne l total; [contradiction|].
  pose proof (word64_range count) as HCnt.
  cbn [ctx8_add_list].
  destruct (ctx8_add1_closed buf count h x) as [[HL (buf1 & HB1 & HM)]|[HL (h1 & HR1 & HM)]];
    fold l in HL, HM; try fold l in HB1; try fold l in HR1; rewrite HM; clear HM.
  - rewrite (absorb_cons_small l (state_regs h) x bs HL).
    destruct bs as [|y bs'].
    + assert (HT : total = @toZ (WordToZ 6) count).
      { unfold total. cbn [length]. rewrite div64_small by lia. lia. }
      rewrite HT. split.
      * intros Hlt. apply Z.ltb_lt in Hlt. rewrite Hlt. exists buf1, h.
        cbn [ctx8_add_list]. rewrite (@from_toZ (WordToZ 6) count).
        split; [reflexivity|]. split; [exact HB1|reflexivity].
      * intros Hge. apply Z.ltb_ge in Hge. rewrite Hge. reflexivity.
    + destruct (IH buf1 count h ltac:(discriminate)) as [IHa IHb].
      rewrite HB1 in IHa, IHb.
      assert (HT : @toZ (WordToZ 6) count +
          (Z.of_nat (length (l ++ [x])) + Z.of_nat (length (y :: bs'))) / 64 = total).
      { unfold total. rewrite app_length. cbn [length]. f_equal. f_equal. lia. }
      rewrite HT in IHa, IHb.
      assert (HD : 0 <= (Z.of_nat (length l) + Z.of_nat (length (x :: y :: bs'))) / 64)
        by (apply div64_nonneg; lia).
      fold total in HD |- *.
      split.
      * intros Hlt. assert (HC : (@toZ (WordToZ 6) count <? ctx8_limit) = true)
          by (apply Z.ltb_lt; unfold total in Hlt; lia).
        rewrite HC. exact (IHa Hlt).
      * intros Hge. destruct (@toZ (WordToZ 6) count <? ctx8_limit); [exact (IHb Hge)|reflexivity].
  - rewrite (absorb_cons_full l (state_regs h) x bs HL), <- HR1.
    assert (HT : total = @toZ (WordToZ 6) count + 1 + Z.of_nat (length bs) / 64).
    { unfold total. cbn [length]. rewrite HL.
      replace (Z.of_nat 63 + Z.of_nat (S (length bs))) with (64 + Z.of_nat (length bs)) by lia.
      rewrite div64_step. lia. }
    assert (HD : 0 <= Z.of_nat (length bs) / 64) by (apply div64_nonneg; lia).
    destruct (Z.ltb_spec (@toZ (WordToZ 6) count + 1) ctx8_limit) as [HC|HC].
    2:{ split; [intros Hlt; exfalso; lia|reflexivity]. }
    assert (HC1 : @toZ (WordToZ 6) (@fromZ (WordToZ 6) (@toZ (WordToZ 6) count + 1)) =
        @toZ (WordToZ 6) count + 1).
    { rewrite (@to_fromZ (WordToZ 6)), word64_pow. apply Z.mod_small.
      unfold ctx8_limit in HC. lia. }
    destruct bs as [|y bs'].
    + cbn [length] in HT. change (Z.of_nat 0 / 64) with 0 in HT.
      split; [|intros Hge; exfalso; lia].
      intros _. exists (buffer_empty_value (Word 3) 5), h1. cbn [ctx8_add_list].
      replace total with (@toZ (WordToZ 6) count + 1) by lia.
      split; [reflexivity|]. split; [apply buffer_list_empty|reflexivity].
    + destruct (IH (buffer_empty_value (Word 3) 5)
        (@fromZ (WordToZ 6) (@toZ (WordToZ 6) count + 1)) h1 ltac:(discriminate)) as [IHa IHb].
      rewrite buffer_list_empty, HC1 in IHa, IHb. cbn [length] in IHa, IHb.
      change (Z.of_nat 0) with 0 in IHa, IHb.
      replace (0 + Z.of_nat (S (length bs'))) with (Z.of_nat (length (y :: bs'))) in IHa, IHb
        by (cbn [length]; lia).
      rewrite <- HT in IHa, IHb. split; [exact IHa|exact IHb].
Qed.
