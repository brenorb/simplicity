(** Assemble the exhaustive certificates without unfolding the full checker
    during conversion, then derive the literal raw-digit result. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word C.jet_toZ.
Require Import C.jet_secp_generator_tables_check C.jet_secp_generate_literal
 C.jet_secp_generator_table_samples C.jet_secp_table_index C.jet_secp_wnaf_literal_mask.
Require Import C.jet_secp_generator_table_g_positive C.jet_secp_generator_table_g_negative
 C.jet_secp_generator_table_g128_positive C.jet_secp_generator_table_g128_negative.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque generator_tables_check.

Theorem generator_tables_checked high neg : generator_tables_check high neg=Some [].
Proof.
 destruct high,neg;
   [exact generator_g128_negative_checked|exact generator_g128_positive_checked|
    exact generator_g_negative_checked|exact generator_g_positive_checked].
Qed.

Theorem generator_tables_literal_digit high (word : Ty.tySem (Word 4)) :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 let n:=literal_wnaf_signed16 word in
 let expected:=generator_entry_signed_numeric high (Z.to_nat (table_storage_index n)) (negb (0<?n)) in
 @literal_generate_small high Alg.CoreFunSem word=
 (@fromZ (WordToZ 8) (fst expected),@fromZ (WordToZ 8) (snd expected)).
Proof. apply generator_tables_match_digit;apply generator_tables_checked. Qed.
