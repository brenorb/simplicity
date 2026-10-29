(** The canonical BIP340 challenge's two compression blocks, in the machine
    register/byte representation used by the original streaming SHA proofs. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Word Simplicity.Ty Simplicity.Alg.
Require Import C.jet_secp_schnorr_tagged_spec C.jet_sha_ctx8_model
 C.jet_buffer_input C.jet_read8s_layout C.jet_sha_finalize_exec.
Require Simplicity.SHA256.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition schnorr_challenge_pad_word : Ty.tySem (Word 8) :=
 @fromZ (WordToZ 8) 0x8000000000000000000000000000000000000000000000000000000000000500.
Definition schnorr_challenge_hash_word (r pk msg:Ty.tySem (Word 8)) :=
 @Simplicity.SHA256.hashBlock Alg.CoreFunSem
  (@Simplicity.SHA256.hashBlock Alg.CoreFunSem (schnorr_challenge_iv_word,(r,pk)),
   (msg,schnorr_challenge_pad_word)).
Definition schnorr_word_bytes (w:Ty.tySem (Word 8)) :=
 map word8_array_value (vector_values (Word 3) 5 w).
Lemma schnorr_challenge_pad_bytes :
 schnorr_word_bytes schnorr_challenge_pad_word=sha_pad (Int64.repr 160).
Proof. vm_compute;reflexivity. Qed.
Lemma schnorr_challenge_hash_registers r pk msg :
 state_regs (schnorr_challenge_hash_word r pk msg)=
 SHA256.hash_block
  (SHA256.hash_block (state_regs schnorr_challenge_iv_word)
   (be_words (schnorr_word_bytes r++schnorr_word_bytes pk)))
  (be_words (schnorr_word_bytes msg++sha_pad (Int64.repr 160))).
Proof.
 unfold schnorr_challenge_hash_word;rewrite !hashBlock_regs.
 change (map word8_array_value (vector_values (Word 3) 6 (r,pk))) with
  (map word8_array_value (vector_values (Word 3) 5 r++vector_values (Word 3) 5 pk)).
 change (map word8_array_value (vector_values (Word 3) 6 (msg,schnorr_challenge_pad_word))) with
  (map word8_array_value (vector_values (Word 3) 5 msg++vector_values (Word 3) 5 schnorr_challenge_pad_word)).
 rewrite !map_app.
 change (map word8_array_value (vector_values (Word 3) 5 schnorr_challenge_pad_word))
  with (schnorr_word_bytes schnorr_challenge_pad_word).
 rewrite schnorr_challenge_pad_bytes;reflexivity.
Qed.

