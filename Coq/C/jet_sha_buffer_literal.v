(** Canonical ctx8AddBuffer recursion, retaining the empty-buffer assertion. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word.
Require Import C.jet_buffer_empty_spec C.jet_sha256_ctx8_init_spec.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_literal C.jet_sha_add_buffer_spec.
Local Open Scope term_scope.
Set Default Timeout 10.

Fixpoint literal_ctx8_add_buffer d {term : Alg.Assertion.Algebra} :
    term (Ty.Prod sha256_ctx8_type (buffer_type (Word 3) d)) sha256_ctx8_type :=
  match d with
  | Datatypes.O => I H &&& O H >>>
      case (I (iden &&& @literal_ctx8_verify_count term >>> O H))
           (I H &&& O H >>> @literal_ctx8_add1 term)
  | Datatypes.S k =>
      (I O H &&& O H >>> case (I H) (I H &&& O H >>> @literal_ctx8_addn (S k) term))
        &&& I I H >>> @literal_ctx8_add_buffer k term
  end.

Lemma literal_ctx8_add_buffer_algebra_matches d term :
  @literal_ctx8_add_buffer d term = @ctx8_add_buffer_spec d term.
Proof.
  induction d as [|d IHd].
  - cbn [literal_ctx8_add_buffer ctx8_add_buffer_spec].
    rewrite literal_ctx8_verify_count_matches, literal_ctx8_add1_algebra_matches. reflexivity.
  - cbn [literal_ctx8_add_buffer ctx8_add_buffer_spec].
    rewrite literal_ctx8_addn_algebra_matches, IHd. reflexivity.
Qed.

Lemma literal_ctx8_add_buffer_matches d :
  @literal_ctx8_add_buffer d optalg = @ctx8_add_buffer_spec d optalg.
Proof.
  induction d as [|d IHd].
  - cbn [literal_ctx8_add_buffer ctx8_add_buffer_spec].
    rewrite literal_ctx8_verify_count_matches, literal_ctx8_add1_matches. reflexivity.
  - cbn [literal_ctx8_add_buffer ctx8_add_buffer_spec].
    rewrite literal_ctx8_addn_matches, IHd. reflexivity.
Qed.
