(** The byte key read by the original total_fee wrapper denotes exactly the
    canonical asset-key equality. No table meaning or memcmp behavior is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit Simplicity.Digest.
Require Import C.jet_word32_chunks C.jet_read32s_layout C.jet_memcmp_words
 C.jet_sha_ctx8_model C.jet_elements_total_fee_read C.jet_equality_spec.
Import ListNotations.
Set Default Timeout 10.
Local Opaque equality_spec.

Definition fee_word_key (a:Ty.tySem Word256):list int:=
 total_fee_input_key(word32_chunks 3 a).

Lemma fee_word_key_length a:length(fee_word_key a)=32%nat.
Proof.
 unfold fee_word_key,total_fee_input_key;rewrite C.jet_memcmp_words.words_bytes_length,
 map_length,word32_chunks_length;reflexivity.
Qed.

Lemma fee_word32_map_injective xs ys:
 map word32_array_value xs=map word32_array_value ys ->xs=ys.
Proof.
 revert ys;induction xs as[|x xs IH];intros[|y ys];cbn;intro Same;try discriminate;[reflexivity|].
 pose proof(f_equal(@hd int Int.zero)Same)as Head.
 pose proof(f_equal(@tl int)Same)as Tail.
 cbn [hd tl]in Head,Tail.
 f_equal;[apply word32_array_value_injective;exact Head|apply IH;exact Tail].
Qed.

Theorem fee_word_key_injective (a b:Ty.tySem Word256):fee_word_key a=fee_word_key b ->a=b.
Proof.
 unfold fee_word_key,total_fee_input_key;intro Same.
 apply (word32_chunks_injective 3),fee_word32_map_injective.
 apply C.jet_memcmp_words.words_bytes_inj;[rewrite !map_length,!word32_chunks_length;reflexivity|exact Same].
Qed.

Lemma fee_word_key_hash h:
 fee_word_key(from_hash256 h)=C.jet_memcmp_words.words_bytes(hash256_reg h).
Proof.
 unfold fee_word_key,total_fee_input_key;rewrite <-hash256_reg_chunks,to_from_hash256;reflexivity.
Qed.

Theorem fee_word_key_hash_iff (a:Ty.tySem Word256)h:
 fee_word_key a=C.jet_memcmp_words.words_bytes(hash256_reg h) <->a=from_hash256 h.
Proof.
 rewrite <-fee_word_key_hash;split;[apply fee_word_key_injective|intros ->;reflexivity].
Qed.

Theorem fee_word_key_equality (a:Ty.tySem Word256)h:
 (if list_eq_dec Int.eq_dec(fee_word_key a)(C.jet_memcmp_words.words_bytes(hash256_reg h))
  then Datatypes.true else Datatypes.false)=
 Bit.toBool(@equality_spec Word256 Alg.CoreFunSem(a,from_hash256 h)).
Proof.
 apply Bool.eq_true_iff_eq;rewrite equality_spec_true.
 destruct(list_eq_dec Int.eq_dec(fee_word_key a)(C.jet_memcmp_words.words_bytes(hash256_reg h)))as[Same|Different].
 - apply fee_word_key_hash_iff in Same;split;[intros _;exact Same|intros _;reflexivity].
 - split;[discriminate|];intro Same;apply fee_word_key_hash_iff in Same;contradiction.
Qed.

Theorem fee_word_key_cmp_eq (a:Ty.tySem Word256)h:
 C.jet_memcmp_model.bytes_cmp(fee_word_key a)(C.jet_memcmp_words.words_bytes(hash256_reg h))=Eq <->
 Bit.toBool(@equality_spec Word256 Alg.CoreFunSem(a,from_hash256 h))=Datatypes.true.
Proof.
 rewrite equality_spec_true;split.
 - intro Compare;apply fee_word_key_hash_iff.
   apply C.jet_memcmp_model.bytes_cmp_eq;[rewrite <-fee_word_key_hash,!fee_word_key_length;reflexivity|exact Compare].
 - intro Same;apply fee_word_key_hash_iff in Same;rewrite Same;apply C.jet_memcmp_model.bytes_cmp_refl.
Qed.
