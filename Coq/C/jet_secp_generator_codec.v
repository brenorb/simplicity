(** The actual saver's two 32-byte outputs are valid loader inputs and
    recover exactly the canonical coordinate residues. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_toZ C.jet_secp_fe_math C.jet_secp_fe_b32 C.jet_secp_input_bytes
  C.jet_secp_output_bytes C.jet_secp_write_fe_numeric C.jet_secp_generator_save_values
  C.jet_secp_generator_load_write C.jet_secp_rescale_literal
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_checkpoint_columns.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma generator_be_chunks_length count value : length (be_chunks count value)=count.
Proof. induction count;cbn [be_chunks length];congruence. Qed.
Lemma generator_be_chunks_value count value :
  be_val (be_chunks count value)=value mod 256^Z.of_nat count.
Proof.
  induction count as [|count IH].
  - change (0=value mod 1);rewrite Z.mod_1_r;reflexivity.
  - cbn [be_chunks];rewrite be_val_cons,generator_be_chunks_length,IH.
    replace (2^(8*Z.of_nat count)) with (256^Z.of_nat count) by
      (rewrite Z.pow_mul_r by lia;reflexivity).
    rewrite Nat2Z.inj_succ,Z.pow_succ_r by lia.
    rewrite Zmod_recombine by (try lia;apply Z.pow_pos_nonneg;lia).
    reflexivity.
Qed.
Lemma generator_be_bytes_value value : 0<=value<2^256 -> be_val (be_bytes value)=value.
Proof.
  intro Range;rewrite <-be_chunks_32,generator_be_chunks_value.
  change (value mod 2^256=value);apply Z.mod_small;exact Range.
Qed.

Definition generator_saved_bytes rho offset := be_bytes (generator_save_value rho offset).
Lemma generator_saved_bytes_length rho offset : length (generator_saved_bytes rho offset)=32%nat.
Proof. unfold generator_saved_bytes,be_bytes;rewrite map_length,seq_length;reflexivity. Qed.
Lemma generator_saved_bytes_bound rho offset :
  Forall (fun x=>0<=x<=255) (generator_saved_bytes rho offset).
Proof.
  unfold generator_saved_bytes;rewrite <-be_chunks_32.
  eapply Forall_impl;[|apply be_chunks_byte_bounds];intros byte Range.
  change (0<=byte<256) in Range;lia.
Qed.
Lemma generator_saved_value_range rho offset : 0<=generator_save_value rho offset<2^256.
Proof. unfold generator_save_value;apply field_mod_256_range. Qed.
Lemma generator_saved_bytes_decode rho offset :
  be_val (generator_saved_bytes rho offset)=generator_save_value rho offset.
Proof. apply generator_be_bytes_value;apply generator_saved_value_range. Qed.
Lemma generator_saved_output_value rho offset :
  @toZ (WordToZ 8) (rescale_field_output (generator_loaded_words (generator_saved_bytes rho offset)))=
    generator_save_value rho offset.
Proof.
  rewrite generator_loaded_output_value by (first [apply generator_saved_bytes_length|apply generator_saved_bytes_bound]).
  rewrite generator_saved_bytes_decode,field_prime_matches_normalizer.
  unfold generator_save_value;rewrite Z.mod_mod by (unfold feP,feR;lia);reflexivity.
Qed.
