(** Whole original Elements input_hash against the literal primitive-bearing
    SigHash inputHash program. Caller representation, SHA readiness and the
    external memcpy model remain explicit obligations. *)
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_application_sep.
Require Import C.jet_elements_words_hash_program C.jet_elements_single_input_literal.
Require Import C.jet_elements_single_input_jet C.jet_memcpy_model C.jet_elements_sha_program.

Theorem elements_single_input_hash_literal_local_spec : memcpy_model ->
  application_jet_local_spec_sep f_simplicity_input_hash elements_ge Elements.env
    Word32 (Ty.Sum Ty.Unit Word256) elements_single_input_hash_rep
    (fun a environment => @literal_elements_single_input_hash elements_hash_alg a environment).
Proof.
  rewrite literal_elements_single_input_hash_matches.
  rewrite <- elements_sha_genv. exact elements_single_input_hash_program_local_spec.
Qed.
