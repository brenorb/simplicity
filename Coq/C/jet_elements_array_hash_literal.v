(** Literal Elements array-hashing programs and the original C cache getters.
    Raw scripts/proofs remain part of the logical environment. Actual caller
    cache construction is a separate obligation, not assumed execution. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_hash_getter_local.
Require Import C.jet_elements_words_hash_program C.jet_sha_hash_words_literal.
Module AC := Alg.Core.Combinators.
Module EFP := PrimitiveElements.Primitive.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_elements_array_hash k w
    (p : Elements.t (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k)))
    {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  let term := EFP.CanonicalStructures.toAssertion alg in
  @literal_sha_hash_words k w term Ty.Unit
    (@AC.drop Ty.Unit (Word w) (Ty.Sum Ty.Unit (Vector (Word 3) k))
      (Alg.Assertion.toCore term) (@EFP.Combinators.prim _ _ alg p)).

Lemma literal_elements_array_hash_matches k w p alg :
  @literal_elements_array_hash k w p alg = @elements_prim_words_hash_spec k w p alg.
Proof.
  unfold literal_elements_array_hash, elements_prim_words_hash_spec.
  rewrite literal_sha_hash_words_matches. reflexivity.
Qed.

Lemma literal_elements_array_hash_parametric k w p :
  EFP.Parametric (@literal_elements_array_hash k w p).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_array_hash_matches k w p alg1),
    (literal_elements_array_hash_matches k w p alg2).
  exact (elements_prim_words_hash_spec_parametric k w p alg1 alg2 R).
Qed.

Definition literal_elements_output_scripts_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_array_hash 5 5 Elements.OutputScriptHash alg.

Theorem elements_output_scripts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_scripts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_output_scripts_words e)) 0 88 760)
    (fun a environment => @literal_elements_output_scripts_hash elements_hash_alg a environment).
Proof.
  unfold literal_elements_output_scripts_hash. rewrite literal_elements_array_hash_matches.
  exact elements_output_scripts_hash_program_local_spec.
Qed.

Definition literal_elements_output_range_proofs_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_array_hash 5 5 Elements.OutputRangeProof alg.

Theorem elements_output_range_proofs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_range_proofs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_output_range_proofs_words e)) 0 120 760)
    (fun a environment => @literal_elements_output_range_proofs_hash elements_hash_alg a environment).
Proof.
  unfold literal_elements_output_range_proofs_hash. rewrite literal_elements_array_hash_matches.
  exact elements_output_range_proofs_hash_program_local_spec.
Qed.

Definition literal_elements_output_surjection_proofs_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_array_hash 5 5 Elements.OutputSurjectionProof alg.

Theorem elements_output_surjection_proofs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_surjection_proofs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_output_surjection_proofs_words e)) 0 152 760)
    (fun a environment => @literal_elements_output_surjection_proofs_hash elements_hash_alg a environment).
Proof.
  unfold literal_elements_output_surjection_proofs_hash. rewrite literal_elements_array_hash_matches.
  exact elements_output_surjection_proofs_hash_program_local_spec.
Qed.

Definition literal_elements_input_scripts_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_array_hash 5 5 Elements.InputScriptHash alg.

Theorem elements_input_scripts_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_scripts_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_input_scripts_words e)) 0 280 760)
    (fun a environment => @literal_elements_input_scripts_hash elements_hash_alg a environment).
Proof.
  unfold literal_elements_input_scripts_hash. rewrite literal_elements_array_hash_matches.
  exact elements_input_scripts_hash_program_local_spec.
Qed.

Definition literal_elements_input_sequences_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_array_hash 2 5 Elements.InputSequence alg.

Theorem elements_input_sequences_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_sequences_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 2 5 (elements_input_sequences_words e)) 0 344 760)
    (fun a environment => @literal_elements_input_sequences_hash elements_hash_alg a environment).
Proof.
  unfold literal_elements_input_sequences_hash. rewrite literal_elements_array_hash_matches.
  exact elements_input_sequences_hash_program_local_spec.
Qed.

Definition literal_elements_input_script_sigs_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_array_hash 5 5 Elements.InputScriptSigHash alg.

Theorem elements_input_script_sigs_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_script_sigs_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 5 (elements_input_script_sigs_words e)) 0 408 760)
    (fun a environment => @literal_elements_input_script_sigs_hash elements_hash_alg a environment).
Proof.
  unfold literal_elements_input_script_sigs_hash. rewrite literal_elements_array_hash_matches.
  exact elements_input_script_sigs_hash_program_local_spec.
Qed.

Definition literal_elements_tappath_hash {alg : EFP.Algebra} : EFP.domain alg Ty.Unit Word256 :=
  @literal_elements_array_hash 5 3 Elements.Tappath alg.

Theorem elements_tappath_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_tappath_hash elements_ge Elements.env Ty.Unit Word256
    (hash_getter_rep (fun e => elements_words_hash_of 5 3 (elements_tappath_words e)) 8 40 176)
    (fun a environment => @literal_elements_tappath_hash elements_hash_alg a environment).
Proof.
  unfold literal_elements_tappath_hash. rewrite literal_elements_array_hash_matches.
  exact elements_tappath_hash_program_local_spec.
Qed.
