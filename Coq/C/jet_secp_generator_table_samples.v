(** Small closed checks of the actual table payload against the exact literal
    generator. These samples are not an exhaustive table certificate. *)
From Coq Require Import ZArith.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word C.jet_toZ C.jet_secp_fe_math
 C.jet_secp_generator_globals C.jet_secp_storage_numeric
 C.jet_secp_generate_literal C.jet_secp_generate_numeric.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition generator_entry_numeric high index :=
 (field_storage_value (generator_entry_words high index),
  field_storage_value (fun i => generator_entry_words high index (4+i)%nat)).
Definition generator_entry_signed_numeric high index (neg : bool) :=
 let '(x,y):=generator_entry_numeric high index in (x,if neg then (feP-y) mod feP else y).

Theorem generator_table_first_numeric high (neg : bool) :
 literal_generate_small_fast high (@fromZ (WordToZ 4) (if neg then -1 else 1))=
 generator_entry_signed_numeric high 0 neg.
Proof.
 destruct high,neg.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
Qed.
Theorem generator_table_second_numeric high (neg : bool) :
 literal_generate_small_fast high (@fromZ (WordToZ 4) (if neg then -3 else 3))=
 generator_entry_signed_numeric high 1 neg.
Proof.
 destruct high,neg.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
 - vm_compute;reflexivity.
Qed.
Theorem generator_table_first_literal high (neg : bool) :
 @literal_generate_small high Alg.CoreFunSem (@fromZ (WordToZ 4) (if neg then -1 else 1))=
 (@fromZ (WordToZ 8) (fst (generator_entry_signed_numeric high 0 neg)),
  @fromZ (WordToZ 8) (snd (generator_entry_signed_numeric high 0 neg))).
Proof. rewrite literal_generate_small_fast_word,generator_table_first_numeric;reflexivity. Qed.
Theorem generator_table_second_literal high (neg : bool) :
 @literal_generate_small high Alg.CoreFunSem (@fromZ (WordToZ 4) (if neg then -3 else 3))=
 (@fromZ (WordToZ 8) (fst (generator_entry_signed_numeric high 1 neg)),
  @fromZ (WordToZ 8) (snd (generator_entry_signed_numeric high 1 neg))).
Proof. rewrite literal_generate_small_fast_word,generator_table_second_numeric;reflexivity. Qed.
