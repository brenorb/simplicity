(** Exhaustive ordinary Coq certificate: all 8192 actual table rows,
    G128 base, negative signed path. *)
From Coq Require Import List.
Require Import C.jet_secp_generator_tables_check.
Import ListNotations.
Set Default Timeout 600.

Definition generator_g128_negative_result := generator_tables_check true true.
Theorem generator_g128_negative_checked : generator_g128_negative_result=Some [].
Proof. Time vm_compute;reflexivity. Qed.
