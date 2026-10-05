(** Closed form of "absorb a byte list, then finalize" for the Simplicity
    SHA-256 context programs: the resulting hash is the padded stream
    [sha_stream] of the byte-list model.  No C execution here. *)
From Coq Require Import ZArith List Lia PeanoNat Eqdep_dec.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Simplicity.Alg.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_uchars_prep.
Require Import C.jet_sha_finalize_exec C.jet_sha_finalize_spec C.jet_sha_finalize_bridge.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

(** The registers after absorbing [bs] into a context holding the pending
    bytes [l], the state [regs] and the compression count [c], then padding. *)
Definition sha_stream (l : list (Ty.tySem (Word 3))) (regs : list int) (c : Z)
    (bs : list (Ty.tySem (Word 3))) : list int :=
  let l' := fst (absorb l regs bs) in
  let total := c + (Z.of_nat (length l) + Z.of_nat (length bs)) / 64 in
  snd (absorb_i (map word8_array_value l') (snd (absorb l regs bs))
    (sha_pad (Int64.repr (64 * total + Z.of_nat (length l'))))).

Definition mk_hash256 (rs : list int) : hash256.
Proof.
  refine (Hash256 (firstn 8 (rs ++ repeat Int.zero 8)) _).
  rewrite firstn_length, app_length, repeat_length. lia.
Defined.

Lemma hash256_ext (a b : hash256) : hash256_reg a = hash256_reg b -> a = b.
Proof.
  destruct a as [ra Ha], b as [rb Hb]. cbn. intros E. subst rb.
  f_equal. apply UIP_dec. decide equality.
Qed.

Lemma mk_hash256_word (w : Ty.tySem Word256) (rs : list int) :
  state_regs w = rs -> from_hash256 (mk_hash256 rs) = w.
Proof.
  intros H. rewrite <- (from_to_hash256 w). f_equal. apply hash256_ext.
  rewrite hash256_reg_chunks. fold (state_regs w). rewrite H. cbn [mk_hash256 hash256_reg].
  assert (HL : length rs = 8%nat).
  { rewrite <- H. unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
  rewrite firstn_app, HL, Nat.sub_diag, firstn_O, app_nil_r.
  rewrite <- HL. apply firstn_all.
Qed.

Theorem ctx8_hash_closed (bs : list (Ty.tySem (Word 3)))
    (buf : Ty.tySem (buffer_type (Word 3) 5)) (count : Ty.tySem (Word 6)) (h : Ty.tySem (Word 8)) :
  bs <> [] ->
  let l := buffer_list (Word 3) 5 buf in
  @toZ (WordToZ 6) count + (Z.of_nat (length l) + Z.of_nat (length bs)) / 64 < ctx8_limit ->
  match ctx8_add_list (buf, (count, h)) bs with
  | Some c' => @ctx8_finalize_spec optalg c'
  | None => None
  end = Some (from_hash256 (mk_hash256 (sha_stream l (state_regs h) (@toZ (WordToZ 6) count) bs))).
Proof.
  intros Hne l HT.
  destruct (ctx8_add_list_closed bs buf count h Hne) as [HC _]. fold l in HC.
  destruct (HC HT) as (buf' & h' & HAdd & HB & HR). rewrite HAdd.
  set (total := @toZ (WordToZ 6) count + (Z.of_nat (length l) + Z.of_nat (length bs)) / 64) in *.
  pose proof (word64_range count) as HCnt.
  assert (HD : 0 <= (Z.of_nat (length l) + Z.of_nat (length bs)) / 64) by (apply div64_nonneg; lia).
  assert (HTZ : @toZ (WordToZ 6) (@fromZ (WordToZ 6) total) = total).
  { rewrite to_fromZ. apply Z.mod_small. unfold ctx8_limit in HT.
    change (two_power_nat (bitSize (WordToZ 6))) with 18446744073709551616. lia. }
  destruct (ctx8_finalize_closed buf' (@fromZ (WordToZ 6) total) h') as [HF _].
  rewrite HTZ in HF. destruct (HF HT) as (hf & HFin & HRegs).
  refine (eq_trans HFin _). f_equal. symmetry. apply mk_hash256_word.
  rewrite HRegs. unfold sha_stream. fold total. rewrite HB, HR. reflexivity.
Qed.
