(** Exhaustive ordinary Coq certificate: all 8192 actual table rows,
    G base, positive signed path. *)
From Coq Require Import List.
Require Import C.jet_secp_generator_tables_check.
Import ListNotations.
Set Default Timeout 600.

Definition generator_g_positive_result := generator_tables_check false false.
Theorem generator_g_positive_checked : generator_g_positive_result=Some [].
Proof. Time vm_compute;reflexivity. Qed.
