(** Fixed Elements TapLeaf tag constants, checked against the canonical SHA block program. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_spec C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_iv_init C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_elements_support_sha_finalize_exec C.jet_sha_finalize_spec.
Require Import C.jet_sha_tapdata_spec C.jet_sha_hash_closed.
Import ListNotations.
Local Open Scope Z_scope.

Definition el_tapleaf_prefix : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 83970051202569989602708926655285927901916640901273030772312966214490629467063.
Definition el_tapleaf_tag_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 47944646764705210021156776179323602979926143895054722190763568939633257100263.
Definition el_tapleaf_tag_block : Ty.tySem (Word 9) :=
  @fromZ (WordToZ 9) 4419371652836376396888994988571890273822652584182276922452174307670250315246913112929002520183573778328560409293391556981662558374071350956693047392338048.
Definition el_tapleaf_tag_bytes : list int := map Int.repr [84; 97; 112; 76; 101; 97; 102; 47; 101; 108; 101; 109; 101; 110; 116; 115].

Lemma el_tapleaf_tag_hash_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, el_tapleaf_tag_block) = el_tapleaf_tag_word.
Proof. vm_compute. reflexivity. Qed.

Lemma el_tapleaf_prefix_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (el_tapleaf_tag_word, el_tapleaf_tag_word)) = el_tapleaf_prefix.
Proof. vm_compute. reflexivity. Qed.

Lemma el_tapleaf_tag_block_bytes :
  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 el_tapleaf_tag_block)) =
  map Int.unsigned (el_tapleaf_tag_bytes ++ sha_pad (Int64.repr 16)).
Proof. vm_compute. reflexivity. Qed.
