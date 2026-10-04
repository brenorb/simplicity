(** Literal port of Programs.Sha256.lib.tapdataInit:
      tapdataInit = buffer63Empty &&& (one word64 &&& tapdataPrefix)
    where [tapdataPrefix] scribes the SHA-256 midstate after the tagged-hash
    prefix SHA256("TapData") || SHA256("TapData").  The constant is written
    out; that it is this midstate, and that SHA256("TapData") is the tag
    digest, are checked by evaluating the canonical [hashBlock] program. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_spec C.jet_buffer_empty_spec C.jet_buffer_input C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha256_iv_init C.jet_read8s_layout C.jet_word32_chunks.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_uchars_prep C.jet_sha_be64_exec.
Require Import C.jet_sha_finalize_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Definition tapdata_prefix : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 40667712476135943074815926098399800589563142586032845238766438666671440893918.

(** one w = true >>> left_pad_low word1 w *)
Definition one64_spec {term : Alg.Core.Algebra} : @Alg.Core.domain term Ty.Unit (Word 6) :=
  AC.comp Bit.true (left_pad_low_1_n 6).

Definition tapdata_init_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Ty.Unit sha256_ctx8_type :=
  AC.pair (buffer_empty_spec (Word 3) 5 Ty.Unit) (AC.pair one64_spec (Alg.scribe tapdata_prefix)).

Lemma tapdata_init_spec_parametric : Alg.Core.Parametric (@tapdata_init_spec).
Proof.
  intros alg1 alg2 R. unfold tapdata_init_spec, one64_spec.
  apply Alg.pair_Parametric; [apply buffer_empty_spec_parametric|].
  apply Alg.pair_Parametric; [|apply Alg.scribe_Parametric].
  apply Alg.comp_Parametric; [apply Bit.true_Parametric|apply left_pad_low_1_n_parametric].
Qed.

Definition one64 : Ty.tySem (Word 6) := @one64_spec Alg.CoreFunSem tt.

Lemma one64_value : @toZ (WordToZ 6) one64 = 1.
Proof. reflexivity. Qed.

Lemma tapdata_init_spec_value :
  @tapdata_init_spec Alg.CoreFunSem tt = (buffer_empty_value (Word 3) 5, (one64, tapdata_prefix)).
Proof.
  unfold tapdata_init_spec.
  change (@AC.pair _ _ _ Alg.CoreFunSem (buffer_empty_spec (Word 3) 5 Ty.Unit)
      (AC.pair one64_spec (Alg.scribe tapdata_prefix)) tt) with
    (@buffer_empty_spec (Word 3) 5 Ty.Unit Alg.CoreFunSem tt,
     (one64, @Alg.scribe Ty.Unit (Word 8) tapdata_prefix Alg.CoreFunSem tt)).
  rewrite buffer_empty_spec_value, Alg.scribe_correct. reflexivity.
Qed.

(** ** The two concrete compressions *)
Definition iv_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19.
Definition tag_word : Ty.tySem (Word 8) :=
  @fromZ (WordToZ 8) 112633728163065979925619053251602456653929709242813588906169298812374638486850.
Definition tag_block : Ty.tySem (Word 9) :=
  @fromZ (WordToZ 9) 4419371627814514849444849851556384968781224120886322008369998198262556832457228456145577973000179191792448113899619522729437796388078023106436640385531960.

Definition tag_bytes : list int :=
  map Int.repr [84; 97; 112; 68; 97; 116; 97].

Lemma tag_hash_eval : @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, tag_block) = tag_word.
Proof. vm_compute. reflexivity. Qed.

Lemma tapdata_prefix_eval :
  @Simplicity.SHA256.hashBlock Alg.CoreFunSem (iv_word, (tag_word, tag_word)) = tapdata_prefix.
Proof. vm_compute. reflexivity. Qed.

Lemma iv_word_regs : state_regs iv_word = sha256_iv_words.
Proof. vm_compute. reflexivity. Qed.

Lemma tag_block_bytes :
  map Int.unsigned (map word8_array_value (vector_values (Word 3) 6 tag_block)) =
  map Int.unsigned (tag_bytes ++ sha_pad (Int64.repr 7)).
Proof. vm_compute. reflexivity. Qed.
