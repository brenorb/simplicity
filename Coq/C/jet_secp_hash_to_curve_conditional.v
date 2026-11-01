(** Public contract of the original [simplicity_hash_to_curve] against its
    frozen Simplicity assertion, conditional on the open SHA-256-dependent
    property [hash_to_curve_accepted_finite]: no key whose two digests are
    field elements maps to two SWU points whose sum is infinity.

    C does not reject an infinity sum; the specification fails on it.  That
    predicate difference is reported in [JET_SECP_HASH_TO_CURVE_MISMATCHES.md]
    (not corrected); [hash_to_curve_differs_if_infinite] proves the divergence
    at any such key.  Here the property is a visible premise of the public
    theorem, alongside the existing explicit libc/builtin models: never an
    axiom, never proved, never refuted. *)
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Simplicity.Alg.
Require Import C.jet_memcpy_model C.jet_ctz_model C.jets_secp C.jet_secp_initialized_partial_contract.
Require Import C.jet_secp_hash_to_curve_spec C.jet_secp_hash_to_curve_reduction.

Theorem hash_to_curve_conditional_local_spec :
  memcpy_model -> ctz_model -> hash_to_curve_accepted_finite ->
  secp_jet_initialized_partial_local_spec hash_ready f_simplicity_hash_to_curve (Word 8)
    (Ty.Prod (Word 8) (Word 8)) (@literal_hash_to_curve (Alg.AssertionSem option_Monad_Zero)).
Proof. exact hash_to_curve_initialized_local_spec_if_finite. Qed.
