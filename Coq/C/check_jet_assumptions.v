(** Audit the public implementation-to-Simplicity results after a full build. *)
Require Import C.jet_increment8_spec C.jet_one8_call.
Print Assumptions eval_increment8_matches_spec.
Print Assumptions eval_one8_initial_matches_spec.
Print Assumptions increment8_output_denotes_spec.
Print Assumptions increment8_spec_initial.
