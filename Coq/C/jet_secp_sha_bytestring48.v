(** The exact register formula proved for the original generator finalizer
    is Digest.byteStringHash on every 48-byte message. Reuse the existing
    byte/word conversion proof; do not substitute a host hash function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require sha.SHA256 sha.general_lemmas sha.functional_prog.
Require Import Simplicity.Digest.
Require Import C.jet_sha256_iv_init C.jet_sha_ctx8_model C.jet_sha_be32_exec
  C.jet_sha_be64_exec C.jet_sha_finalize_exec C.jet_entropy_streaming_byte_blocks.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma secp_sha48_padded_words (message:list byte) : length message=48%nat ->
  be_words (map byte_int message++sha_pad (Int64.repr 48))=SHA256.generate_and_pad message.
Proof.
  intro Len;unfold SHA256.generate_and_pad;rewrite Zlength_correct,Len.
  change (be_words (map byte_int message++
      (map byte_int (Byte.repr 128::repeat Byte.zero 7)++c_be64_bytes (Int64.repr 384)))=
    sha.general_lemmas.bytelist_to_intlist (message++[Byte.repr 128]++repeat Byte.zero 7)++
      [Int.zero;Int.repr 384]).
  rewrite app_assoc,<-map_app.
  rewrite (be_words_app4 14) by (rewrite map_length,app_length,Len;reflexivity).
  rewrite be_words_bytes;reflexivity.
Qed.

Theorem secp_sha48_bytestring (message:list byte) : length message=48%nat ->
  SHA256.hash_block sha256_iv_words (be_words (map byte_int message++sha_pad (Int64.repr 48)))=
    hash256_reg (byteStringHash message).
Proof.
  intro Len;unfold byteStringHash;cbn [hash256_reg].
  rewrite <-sha.functional_prog.generate_and_pad'_eq.
  rewrite sha.functional_prog.process_msg_hash_blocks.
  - rewrite <-secp_sha48_padded_words by exact Len;rewrite <-sha256_iv_words_registers.
    pose proof (hash_blocks_app sha256_iv_words
      (be_words (map byte_int message++sha_pad (Int64.repr 48))) []
      ltac:(apply be_words_length;rewrite app_length,map_length,Len;reflexivity)) as Single.
    rewrite app_nil_r in Single;rewrite Single,SHA256.hash_blocks_equation;reflexivity.
  - rewrite sha.functional_prog.length_generate_and_pad;apply sha.functional_prog.roundup_divide;lia.
  - reflexivity.
Qed.
