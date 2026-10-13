(** Literal scalar_add port: add256, carry expansion, scalar_normalize512.
    Reuse the already reviewed common carry-expansion term rather than a
    numerical substitute. This alone is not a public C-jet theorem. *)
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Bit.
Require Import C.jet_canonical_add_adapter C.jet_secp_literal_add_program.
Require Import C.jet_secp_canonical_scalar_negate.
Require Import C.jet_secp_canonical_scalar_negate_parametric.
Local Open Scope term_scope.
Set Default Timeout 10.

Definition canonical_scalar_add {term : Alg.Core.Algebra} :
    term (Ty.Prod (Word 8) (Word 8)) (Word 8) :=
  @canonical_add_word 8 term >>> @literal_fe_add_expand term
    >>> @canonical_scalar_normalize512 term.

Lemma canonical_scalar_add_parametric : Alg.Core.Parametric (@canonical_scalar_add).
Proof.
  intros term1 term2 R; unfold canonical_scalar_add.
  apply Alg.comp_Parametric.
  - apply canonical_add_word_parametric.
  - apply Alg.comp_Parametric;
      [apply literal_fe_add_expand_parametric|apply canonical_scalar_normalize512_parametric].
Qed.
