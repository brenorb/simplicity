(** The canonical hash values ([sha_stream] over Simplicity bytes, used by
    the accepted environment relations) in terms of the integer-level
    absorbing state [absorb_i] that the C execution theorems produce.  Pure
    reasoning; no program. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_model C.jet_sha_ctx8_bridge C.jet_sha_uchars_prep C.jet_sha_finalize_exec.
Require Import C.jet_sha_ctx_abs C.jet_sha_hash_closed.
Import ListNotations.
Local Open Scope Z_scope.

Lemma sha_stream_absorb_i (l : list (Ty.tySem (Word 3))) (regs : list int) (c : Z)
    (bs : list (Ty.tySem (Word 3))) :
  (length l < 64)%nat ->
  sha_stream l regs c bs =
    snd (absorb_i (fst (absorb_i (map word8_array_value l) regs (map word8_array_value bs)))
                  (snd (absorb_i (map word8_array_value l) regs (map word8_array_value bs)))
                  (sha_pad (Int64.repr (64 * c + Z.of_nat (length l) + Z.of_nat (length bs))))).
Proof.
  intros HL. unfold sha_stream. cbv zeta.
  rewrite absorb_i_fst, absorb_i_snd.
  destruct (absorb_length bs l regs HL) as [HLen _].
  replace (64 * (c + (Z.of_nat (length l) + Z.of_nat (length bs)) / 64) +
           Z.of_nat (length (fst (absorb l regs bs))))
    with (64 * c + Z.of_nat (length l) + Z.of_nat (length bs)); [reflexivity|].
  rewrite HLen.
  pose proof (Z.div_mod (Z.of_nat (length l) + Z.of_nat (length bs)) 64 ltac:(lia)). lia.
Qed.

Lemma mk_hash256_reg (rs : list int) : length rs = 8%nat -> hash256_reg (mk_hash256 rs) = rs.
Proof.
  intros HL. cbn [mk_hash256 hash256_reg].
  rewrite firstn_app, HL, Nat.sub_diag, firstn_O, app_nil_r. rewrite <- HL. apply firstn_all.
Qed.

Lemma state_regs_length (h : Ty.tySem (Word 8)) : length (state_regs h) = 8%nat.
Proof. unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). Qed.
