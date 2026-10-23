(** A checked first block of the actual frozen tables, for both signed
    paths and both bases. This covers 16 entries per path, not all tables. *)
From Coq Require Import ZArith List.
Require Import C.jet_secp_generate_literal C.jet_secp_generate_numeric
 C.jet_secp_generator_bits C.jet_secp_generator_prefix C.jet_secp_generator_prefix_check
 C.jet_secp_generator_rows C.jet_secp_generator_fast_check
 C.jet_secp_generator_fast_points.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_block16_rows high (neg : bool) :=
 let rows:=map (fun row=>generator_row_signed_numeric row neg)
   (firstn 16 (generator_table_rows high)) in
 if neg then rev rows else rows.
Definition generator_block16_seed high (neg : bool) :=
 literal_generate_bits (literal_affine_denote (literal_generator_base_word high)) (repeat neg 11).
Definition generator_block16_check high neg :=
 generator_prefix_rows_check 4 (literal_affine_denote (literal_generator_base_word high))
   (generator_block16_seed high neg) (generator_block16_rows high neg).

Theorem generator_block16_checked high (neg : bool) : generator_block16_check high neg=Some [].
Proof.
 unfold generator_block16_check.
 rewrite <- generator_prefix_fast_check_matches.
 unfold generator_block16_seed; rewrite <- generator_bits_fast_matches.
 destruct high,neg.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
Qed.
Theorem generator_block16_values high neg :
 generator_block16_rows high neg=generator_prefix_values 4
   (literal_affine_denote (literal_generator_base_word high)) (generator_block16_seed high neg).
Proof.
 apply generator_prefix_rows_check_consumed;apply generator_block16_checked.
Qed.
