(** Canonical storage bounds derived from a successful whole-table check.
    The actual closed certificates are discharged by the lookup-call endpoint. *)
From Coq Require Import ZArith List Lia.
Require Import C.jet_secp_fe_math C.jet_secp_generate_numeric C.jet_secp_generator_prefix C.jet_secp_generator_globals
 C.jet_secp_generator_tables_check C.jet_secp_generator_rows C.jet_secp_generator_table_samples
 C.jet_secp_storage_numeric C.jet_secp_storage_unpack C.jet_secp_multiply_finish_product.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_affine_bounds (v : Z*Z) := 0<=fst v<feP /\ 0<=snd v<feP.
Lemma generator_norm_bounds a : generator_affine_bounds (literal_norm_fast a).
Proof.
 destruct a as [[x y] z];unfold generator_affine_bounds,literal_norm_fast;cbn [fst snd];
   split;apply Z.mod_pos_bound;unfold feP,feR;lia.
Qed.
Lemma generator_prefix_values_bounds depth base a : Forall generator_affine_bounds (generator_prefix_values depth base a).
Proof.
 revert a;induction depth as [|depth IH];intro a;cbn [generator_prefix_values].
 - constructor;[apply generator_norm_bounds|constructor].
 - apply Forall_app;split;apply IH.
Qed.
Lemma generator_signed_rows_bounds high neg : generator_tables_check high neg=Some [] ->
 Forall generator_affine_bounds (generator_table_signed_rows high neg).
Proof. intro Check;rewrite (generator_tables_check_values high neg Check);apply generator_prefix_values_bounds. Qed.
Lemma generator_entry_positive high index :
 generator_entry_signed_numeric high index false=generator_entry_numeric high index.
Proof. unfold generator_entry_signed_numeric;destruct (generator_entry_numeric high index);reflexivity. Qed.

Theorem generator_actual_entry_bounds high index : generator_tables_check high false=Some [] ->
 Z.of_nat index<8192 -> generator_affine_bounds (generator_entry_numeric high index).
Proof.
 intros Check Index;pose proof (generator_signed_rows_bounds high false Check) as Bounds.
 rewrite Forall_nth in Bounds.
 rewrite <-generator_entry_positive,<- (generator_table_signed_rows_lookup high false index (0,0) Index).
 apply Bounds.
 unfold generator_table_signed_rows;rewrite map_length.
 pose proof (proj2 (generator_table_rows_exact high));lia.
Qed.
Theorem generator_decoded_fields_bounds high index : generator_tables_check high false=Some [] ->
 Z.of_nat index<8192 ->
 0<=radix_value (storage_unpack_words (generator_entry_words high index))<feP /\
 0<=radix_value (storage_unpack_words (fun j=>generator_entry_words high index (4+j)%nat))<feP.
Proof.
 intros Check Index;pose proof (generator_actual_entry_bounds high index Check Index) as Bounds.
 rewrite !storage_unpack_preserves_value;exact Bounds.
Qed.

Theorem generator_signed_entry_bounds high index neg : generator_tables_check high false=Some [] ->
 Z.of_nat index<8192 -> generator_affine_bounds (generator_entry_signed_numeric high index neg).
Proof.
 intros Check Index;pose proof (generator_actual_entry_bounds high index Check Index) as Bounds.
 unfold generator_affine_bounds,generator_entry_signed_numeric in *.
 destruct (generator_entry_numeric high index) as [x y];cbn [fst snd] in *.
 destruct neg;split;try tauto;apply Z.mod_pos_bound;unfold feP,feR;lia.
Qed.
