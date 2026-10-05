(** Literal port of Programs.Sha256.mkLibAssert.ctx8Finalize and of its
    local helpers (pad01 .. pad063, buffer63Size), with value lemmas for the
    pieces: the zero-padded buffer, its size, and the bit-length word. *)
From Coq Require Import ZArith List Lia PeanoNat.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Util.Option.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_assertion_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_count_assertion C.jet_core_pad_spec C.jet_sha_ctx8_spec C.jet_sha_ctx8_model.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

(** pad01 = copair (zero word16) (iden &&& (unit >>> zero word8))
    pad(2n+1) = oh &&& drop pad(n) >>> match (ih &&& take (zero word(8(n+1)))) iden
    ([zero w] is [fill false w]; over byte leaves that is [fill (zero word8)]). *)
Fixpoint buffer_pad_spec (d : nat) {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (buffer_type (Word 3) d) (Vector (Word 3) (S d)) :=
  match d with
  | O => AC.copair (@Word.zero 4 term) (AC.pair AC.iden (AC.comp AC.unit (@Word.zero 3 term)))
  | S d' =>
      AC.comp (AC.pair (AC.take AC.iden) (AC.drop (buffer_pad_spec d')))
        (AC.case
          (AC.pair (AC.drop AC.iden) (AC.take (@fill Ty.Unit (Word 3) (S d') term (@Word.zero 3 term))))
          AC.iden)
  end.

Lemma buffer_pad_spec_parametric d : Alg.Core.Parametric (@buffer_pad_spec d).
Proof.
  intros alg1 alg2 R. induction d; cbn [buffer_pad_spec].
  - apply Alg.copair_Parametric; [apply Word.zero_Parametric|].
    apply Alg.pair_Parametric; [apply Alg.iden_Parametric|].
    apply Alg.comp_Parametric; [apply Alg.unit_Parametric|apply Word.zero_Parametric].
  - apply Alg.comp_Parametric.
    + apply Alg.pair_Parametric; [apply Alg.take_Parametric, Alg.iden_Parametric|].
      apply Alg.drop_Parametric. exact IHd.
    + apply Alg.case_Parametric; [|apply Alg.iden_Parametric].
      apply Alg.pair_Parametric; [apply Alg.drop_Parametric, Alg.iden_Parametric|].
      apply Alg.take_Parametric. apply Word.fill_Parametric. apply Word.zero_Parametric.
Qed.

Definition zero8 : Ty.tySem (Word 3) := @Word.zero 3 Alg.CoreFunSem tt.

Lemma vector_values_fill_zero n (u : unit) :
  vector_values (Word 3) n (@fill Ty.Unit (Word 3) n Alg.CoreFunSem (@Word.zero 3 Alg.CoreFunSem) u) =
    repeat zero8 (Nat.pow 2 n).
Proof.
  destruct u. induction n; [reflexivity|].
  change (vector_values (Word 3) (S n) (@fill Ty.Unit (Word 3) (S n) Alg.CoreFunSem (@Word.zero 3 Alg.CoreFunSem) tt))
    with (vector_values (Word 3) n (@fill Ty.Unit (Word 3) n Alg.CoreFunSem (@Word.zero 3 Alg.CoreFunSem) tt) ++
          vector_values (Word 3) n (@fill Ty.Unit (Word 3) n Alg.CoreFunSem (@Word.zero 3 Alg.CoreFunSem) tt)).
  rewrite IHn, <- repeat_app. f_equal. cbn [Nat.pow]. lia.
Qed.

Lemma buffer_pad_value d (b : Ty.tySem (buffer_type (Word 3) d)) :
  vector_values (Word 3) (S d) (@buffer_pad_spec d Alg.CoreFunSem b) =
    buffer_list (Word 3) d b ++ repeat zero8 (Nat.pow 2 (S d) - length (buffer_list (Word 3) d b)).
Proof.
  induction d.
  - destruct b as [[]|y]; reflexivity.
  - destruct b as [sv b0]. specialize (IHd b0).
    pose proof (buffer_list_length (Word 3) d b0) as HL.
    set (rec := @buffer_pad_spec d Alg.CoreFunSem b0) in *.
    destruct sv as [u|v].
    + change (@buffer_pad_spec (S d) Alg.CoreFunSem (inl u, b0)) with
        (rec, @fill Ty.Unit (Word 3) (S d) Alg.CoreFunSem (@Word.zero 3 Alg.CoreFunSem) u).
      change (vector_values (Word 3) (S (S d))
          (rec, @fill Ty.Unit (Word 3) (S d) Alg.CoreFunSem (@Word.zero 3 Alg.CoreFunSem) u)) with
        (vector_values (Word 3) (S d) rec ++
         vector_values (Word 3) (S d) (@fill Ty.Unit (Word 3) (S d) Alg.CoreFunSem (@Word.zero 3 Alg.CoreFunSem) u)).
      rewrite IHd, vector_values_fill_zero. cbn [buffer_list fst snd app].
      rewrite <- app_assoc, <- repeat_app. f_equal. f_equal.
      change (Nat.pow 2 (S (S d))) with (2 * Nat.pow 2 (S d))%nat. lia.
    + change (@buffer_pad_spec (S d) Alg.CoreFunSem (inr v, b0)) with (v, rec).
      change (vector_values (Word 3) (S (S d)) (v, rec)) with
        (vector_values (Word 3) (S d) v ++ vector_values (Word 3) (S d) rec).
      rewrite IHd. cbn [buffer_list fst snd]. rewrite <- app_assoc. f_equal. f_equal. f_equal.
      rewrite app_length, vector_values_length.
      change (Nat.pow 2 (S (S d))) with (2 * Nat.pow 2 (S d))%nat. lia.
Qed.

(** buffer63Size *)
Definition flag_spec {X : Ty.Ty} {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Sum Ty.Unit X) Bit :=
  AC.copair Bit.false Bit.true.

Definition buffer63_size_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (buffer_type (Word 3) 5) (Word 3) :=
  AC.pair
    (AC.pair (AC.pair Bit.false Bit.false)
             (AC.pair (AC.take flag_spec) (AC.drop (AC.take flag_spec))))
    (AC.drop (AC.drop
      (AC.pair (AC.pair (AC.take flag_spec) (AC.drop (AC.take flag_spec)))
               (AC.drop (AC.drop (AC.pair (AC.take flag_spec) (AC.drop flag_spec))))))).

Lemma flag_spec_parametric X : Alg.Core.Parametric (@flag_spec X).
Proof.
  intros alg1 alg2 R. unfold flag_spec.
  apply Alg.copair_Parametric; [apply Bit.false_Parametric|apply Bit.true_Parametric].
Qed.

Lemma buffer63_size_spec_parametric : Alg.Core.Parametric (@buffer63_size_spec).
Proof.
  intros alg1 alg2 R. unfold buffer63_size_spec.
  repeat first [apply flag_spec_parametric | apply Bit.false_Parametric
    | apply Alg.pair_Parametric | apply Alg.take_Parametric | apply Alg.drop_Parametric].
Qed.

Lemma buffer63_size_value (b : Ty.tySem (buffer_type (Word 3) 5)) :
  @toZ (WordToZ 3) (@buffer63_size_spec Alg.CoreFunSem b) =
    Z.of_nat (length (buffer_list (Word 3) 5 b)).
Proof.
  destruct b as [s5 [s4 [s3 [s2 [s1 s0]]]]].
  cbn [buffer_list fst snd]. rewrite !app_length.
  destruct s5 as [[]|v5], s4 as [[]|v4], s3 as [[]|v3], s2 as [[]|v2], s1 as [[]|v1], s0 as [[]|v0];
    rewrite ?vector_values_length; reflexivity.
Qed.

(** ** The bit length
    (take buffer63Size >>> left_pad_low word8 vector8)
      &&& drop (take (shift_const_by false word64 6)) >>> add64 >>> shift_const_by false word64 3 *)
Definition ctx8_bitlen_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term sha256_ctx8_type (Word 6) :=
  AC.comp
    (AC.pair (AC.comp (AC.take buffer63_size_spec) (@left_pad_low_spec term 3 3))
             (AC.drop (AC.take (@Word.shift_const 6 term 6))))
    (AC.comp (AC.comp (@Word.adder 6 term) (AC.drop AC.iden)) (@Word.shift_const 6 term 3)).

Lemma left_pad_low_8_64_value (x : Ty.tySem (Word 3)) :
  @toZ (WordToZ 6) (@left_pad_low_spec Alg.CoreFunSem 3 3 x) = @toZ (WordToZ 3) x.
Proof.
  change (@left_pad_low_spec Alg.CoreFunSem 3 3 x) with
    (((zero8, zero8), (zero8, zero8)), ((zero8, zero8), (zero8, x))).
  destruct x as [[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]]. reflexivity.
Qed.

Lemma shift64_left_value (k : Z) (x : Ty.tySem (Word 6)) : 0 < k < 64 ->
  @toZ (WordToZ 6) (@Word.shift_const 6 Alg.CoreFunSem k x) = (@toZ (WordToZ 6) x * 2 ^ k) mod 2 ^ 64.
Proof.
  intros Hk.
  pose proof (word64_range (@Word.shift_const 6 Alg.CoreFunSem k x)) as HR.
  pose proof (Z.mod_pos_bound (@toZ (WordToZ 6) x * 2 ^ k) (2 ^ 64) ltac:(lia)) as HM.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_dec i 64) as [Hs|Hs].
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mul_pow2_bits by lia.
    replace k with (- (- k)) at 1 by lia.
    rewrite (@Word.shift_const_correct 6 (- k) x i) by (change (two_power_nat 6) with 64; lia).
    reflexivity.
  - rewrite Z.mod_pow2_bits_high by lia.
    destruct (Z.eq_dec (@toZ (WordToZ 6) (@Word.shift_const 6 Alg.CoreFunSem k x)) 0) as [->|Hz];
      [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|].
    assert (Z.log2 (@toZ (WordToZ 6) (@Word.shift_const 6 Alg.CoreFunSem k x)) < 64)
      by (apply Z.log2_lt_pow2; [lia|change (2 ^ 64) with 18446744073709551616; lia]).
    lia.
Qed.

Lemma add64_value (a b : Ty.tySem (Word 6)) :
  @toZ (WordToZ 6) (snd (@Word.adder 6 Alg.CoreFunSem (a, b))) =
    (@toZ (WordToZ 6) a + @toZ (WordToZ 6) b) mod 2 ^ 64.
Proof.
  pose proof (Word.adder_correct 6 a b) as HA.
  destruct (@Word.adder 6 Alg.CoreFunSem (a, b)) as [c s]. cbn [snd].
  rewrite (@toZ_Pair BitToZ (WordToZ 6)), word64_pow in HA.
  pose proof (word64_range s) as HS.
  change (2 ^ 64) with 18446744073709551616.
  apply (Z.mod_unique _ _ (@toZ BitToZ c)); [left; lia|lia].
Qed.

Lemma ctx8_bitlen_value (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6))
    (h : Ty.tySem (Word 8)) :
  @toZ (WordToZ 6) count < ctx8_limit ->
  @toZ (WordToZ 6) (@ctx8_bitlen_spec Alg.CoreFunSem (buf, (count, h))) =
    (64 * @toZ (WordToZ 6) count + Z.of_nat (length (buffer_list (Word 3) 5 buf))) * 8.
Proof.
  intros HC. unfold ctx8_limit in HC.
  pose proof (word64_range count) as HR.
  pose proof (buffer_list_length (Word 3) 5 buf) as HL. change (Nat.pow 2 6) with 64%nat in HL.
  change (@ctx8_bitlen_spec Alg.CoreFunSem (buf, (count, h))) with
    (@Word.shift_const 6 Alg.CoreFunSem 3
      (snd (@Word.adder 6 Alg.CoreFunSem
        (@left_pad_low_spec Alg.CoreFunSem 3 3 (@buffer63_size_spec Alg.CoreFunSem buf),
         @Word.shift_const 6 Alg.CoreFunSem 6 count)))).
  rewrite shift64_left_value by lia. rewrite add64_value.
  rewrite left_pad_low_8_64_value, buffer63_size_value, shift64_left_value by lia.
  change (2 ^ 6) with 64. change (2 ^ 3) with 8. change (2 ^ 64) with 18446744073709551616.
  rewrite (Z.mod_small (@toZ (WordToZ 6) count * 64)) by lia.
  rewrite (Z.mod_small (Z.of_nat (length (buffer_list (Word 3) 5 buf)) + @toZ (WordToZ 6) count * 64)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

(** ** ctx8Finalize *)
Definition pad_word64 : Ty.tySem (Word 6) := @fromZ (WordToZ 6) 9223372036854775808.

(** oh &&& ((verifyNumCompression >>> zero word64) &&& iih) *)
Definition ctx8_clear_count_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term sha256_ctx8_type sha256_ctx8_type :=
  @AC.pair _ _ _ (Alg.Assertion.toCore term) (AC.take AC.iden)
    (@AC.pair _ _ _ (Alg.Assertion.toCore term)
      (@AC.comp _ _ _ (Alg.Assertion.toCore term) (@sha256_count_assertion_spec term)
        (@Word.zero 6 (Alg.Assertion.toCore term)))
      (AC.drop (AC.drop AC.iden))).

(** (.. &&& (unit >>> scribe (toWord64 (2^63))) >>> ctx8Add8 >>> (take pad063 &&& iih)) *)
Definition ctx8_finalize_pad_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term sha256_ctx8_type (Ty.Prod (Word 9) (Word 8)) :=
  @AC.comp _ _ _ (Alg.Assertion.toCore term)
    (@AC.pair _ _ (Word 6) (Alg.Assertion.toCore term) (@ctx8_clear_count_spec term)
      (AC.comp AC.unit (Alg.scribe pad_word64)))
    (@AC.comp _ _ _ (Alg.Assertion.toCore term) (@ctx8_addn_spec 3 term)
      (AC.pair (AC.take (@buffer_pad_spec 5 (Alg.Assertion.toCore term))) (AC.drop (AC.drop AC.iden)))).

(** oih &&& (oooh &&& (take oioh &&& (take (take iioh) &&& ih))) *)
Definition ctx8_finalize_block_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term (Ty.Prod (Ty.Prod (Word 9) (Word 8)) (Word 6)) (Ty.Prod (Word 8) (Word 9)) :=
  AC.pair (AC.take (AC.drop AC.iden))
    (AC.pair (AC.take (AC.take (AC.take AC.iden)))
      (AC.pair (AC.take (AC.take (AC.drop (AC.take AC.iden))))
        (AC.pair (AC.take (AC.take (AC.drop (AC.drop (AC.take AC.iden))))) (AC.drop AC.iden)))).

Definition ctx8_finalize_spec {term : Alg.Assertion.Algebra} :
    @Alg.Assertion.domain term sha256_ctx8_type (Word 8) :=
  @AC.comp _ _ _ (Alg.Assertion.toCore term)
    (@AC.pair _ _ _ (Alg.Assertion.toCore term) (@ctx8_finalize_pad_spec term)
      (@ctx8_bitlen_spec (Alg.Assertion.toCore term)))
    (AC.comp (@ctx8_finalize_block_spec (Alg.Assertion.toCore term)) Simplicity.SHA256.hashBlock).

Lemma ctx8_bitlen_spec_parametric : Alg.Core.Parametric (@ctx8_bitlen_spec).
Proof.
  intros alg1 alg2 R. unfold ctx8_bitlen_spec.
  apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.comp_Parametric; [apply Alg.take_Parametric, buffer63_size_spec_parametric|].
      unfold left_pad_low_spec, low_word.
      assert (HP : forall k, Alg.Core.Parametric.rel R
        (left_pad_pad (AC.comp AC.unit (fill (n := 3) (@Bit.false Ty.Unit alg1))) k)
        (left_pad_pad (AC.comp AC.unit (fill (n := 3) (@Bit.false Ty.Unit alg2))) k)).
      { induction k; cbn [left_pad_pad]; [apply Alg.iden_Parametric|].
        apply Alg.pair_Parametric; [|exact IHk].
        apply Word.fill_Parametric. apply Alg.comp_Parametric; [apply Alg.unit_Parametric|].
        apply Word.fill_Parametric. apply Bit.false_Parametric. }
      apply HP.
    + apply Alg.drop_Parametric, Alg.take_Parametric, Word.shift_const_Parametric.
  - apply Alg.comp_Parametric; [|apply Word.shift_const_Parametric].
    apply Alg.comp_Parametric; [apply Word.adder_Parametric|apply Alg.drop_Parametric, Alg.iden_Parametric].
Qed.

Lemma ctx8_finalize_block_spec_parametric : Alg.Core.Parametric (@ctx8_finalize_block_spec).
Proof.
  intros alg1 alg2 R. unfold ctx8_finalize_block_spec.
  repeat first [apply Alg.pair_Parametric | apply Alg.take_Parametric | apply Alg.drop_Parametric
    | apply Alg.iden_Parametric].
Qed.

Definition zero64 : Ty.tySem (Word 6) := @Word.zero 6 Alg.CoreFunSem tt.

Definition pad8_bytes : list (Ty.tySem (Word 3)) := vector_values (Word 3) 3 pad_word64.

Lemma ctx8_finalize_option (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6))
    (h : Ty.tySem (Word 8)) :
  @ctx8_finalize_spec optalg (buf, (count, h)) =
    if @toZ (WordToZ 6) count <? ctx8_limit
    then match ctx8_add_list (buf, (zero64, h)) pad8_bytes with
         | Some c2 =>
             Some (@Simplicity.SHA256.hashBlock Alg.CoreFunSem
               (@ctx8_finalize_block_spec Alg.CoreFunSem
                  ((@buffer_pad_spec 5 Alg.CoreFunSem (fst c2), snd (snd c2)),
                   @ctx8_bitlen_spec Alg.CoreFunSem (buf, (count, h)))))
         | None => None
         end
    else None.
Proof.
  assert (HZ : forall u, @Word.zero 6 (Alg.Assertion.toCore optalg) u = Some (@Word.zero 6 Alg.CoreFunSem u))
    by (intro u; exact (opt_core (fun alg => @Word.zero 6 alg) (fun a1 a2 R => @Word.zero_Parametric 6 a1 a2 R) u)).
  assert (HS : forall u, @Alg.scribe Ty.Unit (Word 6) pad_word64 (Alg.Assertion.toCore optalg) u = Some pad_word64).
  { intro u. rewrite (opt_core (fun alg => @Alg.scribe Ty.Unit (Word 6) pad_word64 alg)
      (fun a1 a2 R => @Alg.scribe_Parametric a1 a2 R Ty.Unit (Word 6) pad_word64) u).
    rewrite Alg.scribe_correct. reflexivity. }
  assert (HP : forall b, @buffer_pad_spec 5 (Alg.Assertion.toCore optalg) b = Some (@buffer_pad_spec 5 Alg.CoreFunSem b))
    by (intro b; exact (opt_core (@buffer_pad_spec 5) (buffer_pad_spec_parametric 5) b)).
  assert (HL : forall c, @ctx8_bitlen_spec (Alg.Assertion.toCore optalg) c = Some (@ctx8_bitlen_spec Alg.CoreFunSem c))
    by (intro c; exact (opt_core (@ctx8_bitlen_spec) ctx8_bitlen_spec_parametric c)).
  assert (HB : forall c, @ctx8_finalize_block_spec (Alg.Assertion.toCore optalg) c =
      Some (@ctx8_finalize_block_spec Alg.CoreFunSem c))
    by (intro c; exact (opt_core (@ctx8_finalize_block_spec) ctx8_finalize_block_spec_parametric c)).
  assert (HH : forall c, @Simplicity.SHA256.hashBlock (Alg.Assertion.toCore optalg) c =
      Some (@Simplicity.SHA256.hashBlock Alg.CoreFunSem c))
    by (intro c; exact (opt_core (@Simplicity.SHA256.hashBlock)
          (fun a1 a2 R => @Simplicity.SHA256.hashBlock_Parametric a1 a2 R) c)).
  unfold ctx8_finalize_spec, ctx8_finalize_pad_spec, ctx8_clear_count_spec.
  repeat progress (cbv beta iota; cbn [fst snd];
    rewrite ?opt_unit, ?opt_pair, ?opt_comp, ?opt_take, ?opt_drop, ?opt_iden,
      ?sha256_count_assertion_option, ?HS, ?HL).
  unfold ctx8_limit.
  destruct (@toZ (WordToZ 6) count <? 36028797018963968); [|reflexivity].
  cbv beta iota. rewrite HZ. cbv beta iota. rewrite opt_comp, ctx8_addn_option.
  fold pad8_bytes. fold zero64.
  match goal with |- context[ctx8_add_list ?a ?b] => set (r := ctx8_add_list a b) end.
  repeat match goal with |- context[ctx8_add_list ?a ?b] => change (ctx8_add_list a b) with r end.
  clearbody r. destruct r as [c2|]; [|reflexivity].
  repeat progress (cbv beta iota; cbn [fst snd];
    rewrite ?opt_pair, ?opt_comp, ?opt_take, ?opt_drop, ?opt_iden, ?HP, ?HB, ?HH).
  reflexivity.
Qed.

Lemma ctx8_clear_count_spec_parametric : Alg.Assertion.Parametric (@ctx8_clear_count_spec).
Proof.
  intros alg1 alg2 R. pose proof (sha256_count_assertion_parametric alg1 alg2 R) as HCount.
  destruct R as [R [HC HA]]. unfold ctx8_clear_count_spec.
  set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.pair_Parametric RC); [apply (Alg.take_Parametric RC), Alg.iden_Parametric|].
  apply (Alg.pair_Parametric RC).
  - apply (Alg.comp_Parametric RC); [exact HCount|apply (Word.zero_Parametric RC)].
  - apply (Alg.drop_Parametric RC), (Alg.drop_Parametric RC), Alg.iden_Parametric.
Qed.

Lemma ctx8_finalize_spec_parametric : Alg.Assertion.Parametric (@ctx8_finalize_spec).
Proof.
  intros alg1 alg2 R. pose proof (ctx8_clear_count_spec_parametric alg1 alg2 R) as HClear.
  pose proof (ctx8_addn_spec_parametric 3 alg1 alg2 R) as HAdd.
  destruct R as [R [HC HA]]. unfold ctx8_finalize_spec, ctx8_finalize_pad_spec.
  set (RC := Alg.Core.Parametric.Pack HC).
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [|apply (ctx8_bitlen_spec_parametric _ _ RC)].
    apply (Alg.comp_Parametric RC).
    + apply (Alg.pair_Parametric RC); [exact HClear|].
      apply (Alg.comp_Parametric RC); [apply Alg.unit_Parametric|apply (Alg.scribe_Parametric RC)].
    + apply (Alg.comp_Parametric RC); [exact HAdd|].
      apply (Alg.pair_Parametric RC).
      * apply (Alg.take_Parametric RC). apply (buffer_pad_spec_parametric 5 _ _ RC).
      * apply (Alg.drop_Parametric RC), (Alg.drop_Parametric RC), Alg.iden_Parametric.
  - apply (Alg.comp_Parametric RC); [apply (ctx8_finalize_block_spec_parametric _ _ RC)|].
    apply (Simplicity.SHA256.hashBlock_Parametric RC).
Qed.
