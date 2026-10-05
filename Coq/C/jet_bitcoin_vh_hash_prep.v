(** Preparation for the hash-computing indexed Bitcoin jets: sequencing two
    output effects around steps that leave the output frame alone, and the
    registers of the value-and-script hash. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Zbits Integers AST Memory Values.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_sequence_step C.jet_encoding C.jet_constant_layout.
Require Import C.jet_bitcoin_effects.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_word32_chunks C.jet_sha256_iv_init.
Require Import C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_be32_write C.jet_sha_be64_exec.
Require Import C.jet_sha_finalize_exec C.jet_sha_finalize_bridge C.jet_sha_hash_closed.
Require Import C.jet_bitcoin_composite_hash C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_vh_hash_spec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Lemma write_cells_seq m m1 m1' m2 bf base bw edge cursor n1 n2 cells1 cells2 :
  Z.of_nat (length cells1) = n1 -> 0 <= n2 ->
  write_frame_at m bf base bw edge cursor (n1 + n2) ->
  write_effect m m1 bf base bw edge cursor n1 cells1 ->
  (forall ch ofs, Mem.load ch m1' bw ofs = Mem.load ch m1 bw ofs) ->
  write_effect m1' m2 bf base bw edge (cursor - n1) n2 cells2 ->
  frame_output_cells_at m2 bw edge cursor (cells1 ++ cells2) /\
  write_prefix_at m m2 bw edge cursor /\
  frame_fields_at m2 bf base bw edge (cursor - (n1 + n2)).
Proof.
  intros HL1 Hn2 HFrame (O1 & P1 & F1 & L1 & Pm1 & V1) HW (O2 & P2 & F2 & L2 & Pm2 & V2).
  pose proof HFrame as [HB [HF [HE [HC [HM [HD [PD HWd]]]]]]].
  assert (Hn1 : 0 <= n1) by (rewrite <- HL1; lia).
  assert (O1' : frame_output_cells_at m1' bw edge cursor cells1).
  { eapply frame_output_cells_preserved; [|exact O1]. intros ofs w HL. rewrite HW. exact HL. }
  assert (P1' : write_prefix_at m m1' bw edge cursor).
  { eapply write_prefix_at_preserved with (mr := m) (me := m1); [| |exact P1].
    - intros ofs w HL. exact HL.
    - intros ofs w HL. rewrite HW. exact HL. }
  split; [|split].
  - apply frame_output_cells_at_app. split.
    + eapply frame_output_cells_prefix_preserved with (m := m1') (bf := bf) (base := base)
        (cursor := cursor - n1) (low := edge + 8 * ((cursor - n1 - n2) / 64)).
      * exact HD.
      * rewrite HL1. lia.
      * exact P2.
      * exact L2.
      * exact O1'.
    + rewrite HL1. exact O2.
  - eapply write_prefix_at_chain with (mi := m1') (next := cursor - n1)
      (low := edge + 8 * ((cursor - n1 - n2) / 64)).
    + exact HD.
    + lia.
    + exact P1'.
    + exact P2.
    + exact L2.
  - replace (cursor - (n1 + n2)) with (cursor - n1 - n2) by lia. exact F2.
Qed.

Lemma repr_signed_word (x : int64) :
  Int64.repr (@toZ (WordToZ 6) (@fromZ (WordToZ 6) (Int64.signed x))) = x.
Proof.
  rewrite to_fromZ. change (two_power_nat (ToZ.Theory.bitSize (WordToZ 6))) with Int64.modulus.
  rewrite <- (Int64.repr_signed x) at 2. apply Int64.eqm_samerepr.
  apply Int64.eqm_sym. apply Zbits.eqmod_mod. reflexivity.
Qed.

Theorem vh_regs_eq (x : int64) (H : hash256) :
  snd (absorb_i (c_be64_bytes x ++ be_bytes (hash256_reg H)) sha256_iv_words
    (sha_pad (Int64.repr 40))) =
  hash256_reg (sha256_bytes_of
    (vh_bytes (@fromZ (WordToZ 6) (Int64.signed x)) (from_hash256 H))).
Proof.
  set (v := @fromZ (WordToZ 6) (Int64.signed x)). set (h := from_hash256 H).
  assert (HLen : length (vh_bytes v h) = 40%nat).
  { unfold vh_bytes. rewrite app_length, !vector_values_length. reflexivity. }
  rewrite short_hash_regs by (rewrite HLen; lia). rewrite HLen.
  change (Z.of_nat 40) with 40. do 2 f_equal.
  unfold vh_bytes. rewrite map_app. f_equal.
  - rewrite <- be64_bytes_word. unfold v. rewrite repr_signed_word. reflexivity.
  - rewrite <- be_bytes_state_regs. f_equal. unfold h, state_regs.
    rewrite <- hash256_reg_chunks, to_from_hash256. reflexivity.
Qed.
