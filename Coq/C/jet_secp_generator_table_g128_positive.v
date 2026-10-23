(** Exhaustive ordinary Coq certificate: all 8192 actual table rows,
    G128 base, positive signed path. *)
From Coq Require Import List.
Require Import C.jet_secp_generator_tables_check.
Import ListNotations.
Set Default Timeout 600.

Definition generator_g128_positive_result := generator_tables_check true false.
Theorem generator_g128_positive_checked : generator_g128_positive_result=Some [].
Proof. Time vm_compute;reflexivity. Qed.
