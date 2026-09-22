(** Audit the public implementation-to-Simplicity results after a full build. *)
Require Import C.jet_increment8_spec C.jet_one8_call C.jet_one8_general.
Require Import C.jet_increment8_general.
Require Import C.jet_one8_position C.jet_word_position.
Require Import C.jet_increment8_position C.jet_increment8_position_word.
Require Import C.jet_one8_crossing C.jet_crossing_word.
Require Import C.jet_increment8_cursors.
Require Import C.jet_add8_call.
Print Assumptions eval_add8_position_call.
Print Assumptions eval_increment8_cursors_matches_spec.
Print Assumptions eval_one8_crossing_matches_spec.
Print Assumptions crossing_byte_one.
Print Assumptions eval_increment8_position_matches_spec.
Print Assumptions increment8_word_at_decode.
Print Assumptions eval_one8_position_matches_spec.
Print Assumptions put_byte_projection.
Print Assumptions eval_increment8_frame_matches_spec.
Print Assumptions eval_one8_frame_matches_spec.
Print Assumptions eval_increment8_matches_spec.
Print Assumptions eval_one8_initial_matches_spec.
Print Assumptions increment8_output_denotes_spec.
Print Assumptions increment8_spec_initial.
