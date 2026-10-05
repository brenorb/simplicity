(** Literal ports of the SigHash helpers
      hashWord256s w array = iden &&& (unit >>> ctx8Init) >>> hashLoop vector32 w array >>> ctx8Finalize
    (and the 64- and 32-bit variants, which differ only in the vector), and
    their value: the SHA-256 of the concatenated array elements. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec C.jet_sha256_iv_init.
Require Import C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_forWhile_spec C.jet_forWhile_seq.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_uchars_prep.
Require Import C.jet_sha_finalize_exec C.jet_sha_finalize_spec C.jet_sha_finalize_bridge C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim C.jet_sha_hash_loop.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

(** [ctx8_hash_closed] without the non-emptiness premise. *)
Theorem ctx8_hash_closed_gen (bs : list (Ty.tySem (Word 3)))
    (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6)) (h : Ty.tySem (Word 8)) :
  let l := buffer_list (Word 3) 5 buf in
  @toZ (WordToZ 6) count + (Z.of_nat (length l) + Z.of_nat (length bs)) / 64 < ctx8_limit ->
  exists cf, ctx8_add_list (buf, (count, h)) bs = Some cf /\
    @ctx8_finalize_spec optalg cf =
      Some (from_hash256 (mk_hash256 (sha_stream l (state_regs h) (@toZ (WordToZ 6) count) bs))).
Proof.
  intros l HT. destruct bs as [|b bs].
  - exists (buf, (count, h)). split; [reflexivity|].
    pose proof (buffer_list_length (Word 3) 5 buf) as HL. change (Nat.pow 2 6) with 64%nat in HL. fold l in HL.
    assert (HD : (Z.of_nat (length l) + Z.of_nat (@length (Ty.tySem (Word 3)) [])) / 64 = 0)
      by (apply Z.div_small; cbn [length]; lia).
    rewrite HD, Z.add_0_r in HT.
    destruct (ctx8_finalize_closed buf count h) as [HF _].
    destruct (HF HT) as (hf & HFin & HRegs).
    refine (eq_trans HFin _). f_equal. symmetry. apply mk_hash256_word.
    rewrite HRegs. unfold sha_stream. rewrite HD, Z.add_0_r. reflexivity.
  - pose proof (ctx8_hash_closed (b :: bs) buf count h ltac:(discriminate) HT) as HC.
    destruct (ctx8_add_list (buf, (count, h)) (b :: bs)) as [cf|]; [|discriminate].
    exists cf. split; [reflexivity|exact HC].
Qed.

Lemma fx_unit {A : Ty} (a : Ty.tySem A) e : @AC.unit A fullcore a e = Some tt.
Proof. reflexivity. Qed.

Definition hash_words_spec (k w : nat) {term : Alg.Assertion.Algebra} {C : Ty}
    (array : @Alg.Assertion.domain term (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k))) :
    @Alg.Assertion.domain term C Word256 :=
  let core := Alg.Assertion.toCore term in
  @AC.comp _ _ _ core
    (@AC.pair _ _ _ core (@AC.iden _ core)
      (@AC.comp _ _ _ core (@AC.unit _ core) (@sha256_ctx8_init_spec core)))
    (@AC.comp _ _ _ core (@hash_loop_spec k w term C array) (@ctx8_finalize_spec term)).

Lemma hash_words_spec_parametric k w {C : Ty} {alg1 alg2 : Alg.Assertion.Algebra}
    (R : Alg.Assertion.Parametric.Rel alg1 alg2) a1 a2 :
  Alg.Assertion.Parametric.rel R a1 a2 ->
  Alg.Assertion.Parametric.rel R (@hash_words_spec k w alg1 C a1) (@hash_words_spec k w alg2 C a2).
Proof.
  intros HA. pose proof (hash_loop_spec_parametric k w R a1 a2 HA) as HL.
  pose proof (ctx8_finalize_spec_parametric _ _ R) as HF.
  destruct R as [R [HC HAm]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold hash_words_spec. cbv zeta.
  apply (Alg.comp_Parametric RC); [|apply (Alg.comp_Parametric RC); [exact HL|exact HF]].
  apply (Alg.pair_Parametric RC); [apply Alg.iden_Parametric|].
  apply (Alg.comp_Parametric RC); [apply Alg.unit_Parametric|].
  apply (sha256_ctx8_init_spec_parametric _ _ RC).
Qed.

Definition hash_words_of (k : nat) (items : list (Ty.tySem (Vector (Word 3) k))) : hash256 :=
  mk_hash256 (sha_stream [] sha256_iv_words 0 (loop_bytes k items)).

Lemma iv_spec_regs : state_regs (@sha256_iv_spec Alg.CoreFunSem tt) = sha256_iv_words.
Proof. vm_compute. reflexivity. Qed.

Lemma loop_bytes_length k (l : list (Ty.tySem (Vector (Word 3) k))) :
  length (loop_bytes k l) = (Nat.pow 2 k * length l)%nat.
Proof.
  induction l as [|x l IH]; [cbn; lia|].
  change (loop_bytes k (x :: l)) with (vector_values (Word 3) k x ++ loop_bytes k l).
  rewrite app_length, vector_values_length, IH. cbn [length]. lia.
Qed.

Theorem hash_words_sem (k w : nat) (C : Ty)
    (array : @Alg.Assertion.domain fullassert (Ty.Prod C (Word w)) (Ty.Sum Ty.Unit (Vector (Word 3) k)))
    (c : Ty.tySem C) (e : ext_environment) (xs : list (Ty.tySem (Vector (Word 3) k))) :
  (forall i, array (c, i) e =
    Some (match nth_error xs (Z.to_nat (wz w i)) with Some x => inr x | None => inl tt end)) ->
  Z.of_nat (Nat.pow 2 k) * wsize w / 64 < ctx8_limit ->
  @hash_words_spec k w fullassert C array c e =
    Some (from_hash256 (hash_words_of k (firstn (Z.to_nat (wsize w)) xs))).
Proof.
  intros Harr HB. pose proof (wsize_pos w) as HW.
  set (items := firstn (Z.to_nat (wsize w)) xs).
  set (c0 := (buffer_empty_value (Word 3) 5,
    (@Word.zero 6 Alg.CoreFunSem tt, @sha256_iv_spec Alg.CoreFunSem tt)) : Ty.tySem sha256_ctx8_type).
  assert (HT : @toZ (WordToZ 6) (@Word.zero 6 Alg.CoreFunSem tt) +
    (Z.of_nat (length (buffer_list (Word 3) 5 (buffer_empty_value (Word 3) 5))) +
     Z.of_nat (length (loop_bytes k items))) / 64 < ctx8_limit).
  { rewrite buffer_list_empty, loop_bytes_length.
    change (@toZ (WordToZ 6) (@Word.zero 6 Alg.CoreFunSem tt)) with 0. cbn [length].
    assert (HL : (length items <= Z.to_nat (wsize w))%nat) by (unfold items; apply firstn_le_length).
    eapply Z.le_lt_trans; [|exact HB]. rewrite Z.add_0_l, Z.add_0_l.
    apply Z.div_le_mono; [lia|]. rewrite Nat2Z.inj_mul. apply Z.mul_le_mono_nonneg_l; lia. }
  destruct (ctx8_hash_closed_gen (loop_bytes k items) (buffer_empty_value (Word 3) 5)
    (@Word.zero 6 Alg.CoreFunSem tt) (@sha256_iv_spec Alg.CoreFunSem tt) HT) as (cf & Hcf & HFin).
  rewrite buffer_list_empty, iv_spec_regs in HFin.
  change (@toZ (WordToZ 6) (@Word.zero 6 Alg.CoreFunSem tt)) with 0 in HFin.
  unfold hash_words_spec. cbv zeta.
  rewrite fx_comp, fx_pair, fx_iden, fx_comp, fx_unit.
  rewrite (fx_core (fun alg => @sha256_ctx8_init_spec alg) sha256_ctx8_init_spec_parametric),
    sha256_ctx8_init_spec_value.
  rewrite fx_comp.
  match goal with |- match ?X with _ => _ end = _ =>
    assert (HX : X = Some cf) by exact (hash_loop_sem k w C array c c0 e xs Harr cf Hcf);
    rewrite HX end.
  rewrite (fx_assert (fun alg => @ctx8_finalize_spec alg) ctx8_finalize_spec_parametric).
  exact HFin.
Qed.
