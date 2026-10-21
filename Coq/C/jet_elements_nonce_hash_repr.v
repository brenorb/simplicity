(** The actual C confNonce helper against the canonical nonce serializer.
    A missing nonce requires its prefix only, not initialized payload words. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_read8s_layout.
Require Import C.jets_elements C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_nonce_hash_spec.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_ctx_abs.
Require Import C.jet_elements_support_sha_ctxi C.jet_elements_support_sha_uchars_prep.
Require Import C.jet_elements_support_sha_be32_write C.jet_elements_conf_hash_bridge.
Require Import C.jet_elements_confidential_exec C.jet_elements_confidential_wrap.
Require Import C.jet_elements_indexed_ptr_jets.
Import Ctypes Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 15.

Lemma elements_nonce_canonical_bytes n :
  conf_bytes (Int.repr 2) (Int.repr 3) (nonce_prefix n) (nonce_words n) =
    map word8_array_value (elements_nonce_bytes (encode_nonce n)).
Proof.
  destruct n as [[[odd h]|h]|].
  - destruct odd.
    + change (Int.repr 3 :: be_bytes (hash256_reg h) = word8_array_value nonce_byte_three ::
        map word8_array_value (C.jet_buffer_input.vector_values Word8 5 (from_hash256 h))).
      rewrite elements_hash_words_bytes. reflexivity.
    + change (Int.repr 2 :: be_bytes (hash256_reg h) = word8_array_value nonce_byte_two ::
        map word8_array_value (C.jet_buffer_input.vector_values Word8 5 (from_hash256 h))).
      rewrite elements_hash_words_bytes. reflexivity.
  - change (Int.repr 1 :: be_bytes (hash256_reg h) = word8_array_value C.jet_bitcoin_ctx_hash_spec.byte_one ::
      map word8_array_value (C.jet_buffer_input.vector_values Word8 5 (from_hash256 h))).
    rewrite elements_hash_words_bytes. reflexivity.
  - reflexivity.
Qed.

Section Nonce.
Variable Hmodel : memcpy_model.
Variables bx bm : block.
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem eval_sha256_nonce_repr m l regs c ovf bn on (n : option nonce) :
  ctxi m bx bm l regs c ovf ->
  0 <= on /\ on + 36 <= Ptrofs.max_unsigned ->
  bn <> bx -> bn <> bm -> nonce_rep m bn on n ->
  let B := map word8_array_value (elements_nonce_bytes (encode_nonce n)) in
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_sha256_confNonce)
      [Vptr bx (Ptrofs.repr 0); Vptr bn (Ptrofs.repr on)] E0 mf Vundef /\
    ctxi mf bx bm (fst (absorb_i l regs B)) (snd (absorb_i l regs B))
      (Int64.add c (Int64.repr (Z.of_nat (length B)))) (conf_overflow c ovf (nonce_prefix n)) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch mf b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HC HO Hbx Hbm [HW HP] B.
  unfold B. rewrite <- elements_nonce_canonical_bytes.
  apply (eval_sha256_confNonce Hmodel bx bm l regs c ovf Hmx Hgx Hgm Hcx Hcm
    bn on (nonce_words n) HO (nonce_words_length n) Hbx Hbm m (nonce_prefix n) HC HP).
  - destruct n as [[[odd h]|h]|].
    + destruct odd; [right; right; right; reflexivity|right; right; left; reflexivity].
    + right; left; reflexivity.
    + left; reflexivity.
  - intros Hnonzero j Hj. apply HW.
    + intro E. subst n. apply Hnonzero. reflexivity.
    + apply nth_error_nth'. rewrite nonce_words_length. exact Hj.
Qed.
End Nonce.

Lemma elements_nonce_rep_mono m1 m2 b ofs n :
  nonce_rep m1 b ofs n ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 36 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) ->
  nonce_rep m2 b ofs n.
Proof.
  intros [HD HP] HL. split.
  - intro HSome. eapply uint32_array_at_mono; [apply nonce_words_length|apply HD; exact HSome|].
    intros chunk o v Hlo Hhi. apply HL; [exact Hlo|lia].
  - apply (HL Mint32 (ofs + 32) _); [lia|change (size_chunk Mint32) with 4; lia|exact HP].
Qed.
