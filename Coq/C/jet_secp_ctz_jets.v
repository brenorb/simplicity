(** Public secp jets whose only remaining dependency was the original
    [secp256k1_ctz64_var] call. Each theorem is the existing full initialized
    local contract, conditional on the explicit [ctz_model] premise for the
    abstract [__builtin_ctzl] external call (see [jet_ctz_model]). These are
    conditional results, reported as such in coverage, like [memcpy_model].

    The previously deferred premise (complete original helper execution
    returning the trailing-zero count, with unchanged memory and empty trace)
    is derived here from that external-call model and the checked helper
    execution [eval_ctz64_from_external]; it is no longer a parameter. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_ctz_model C.jets_secp C.jet_secp_linkage
 C.jet_secp_ctz_external_call C.jet_secp_initialized_contract
 C.jet_secp_invert_literal C.jet_secp_modinfo_fe_caller C.jet_secp_fe_invert_local
 C.jet_secp_scalar_invert_literal C.jet_secp_modinfo_scalar_initialized C.jet_secp_scalar_invert_local
 C.jet_secp_gej_norm_branch C.jet_secp_gej_norm_local C.jet_secp_gej_odd_literal C.jet_secp_gej_odd_local
 C.jet_secp_swu_literal C.jet_secp_swu_startup C.jet_secp_swu_local.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

(** The original helper's complete execution for every nonzero argument. *)
Lemma ctz_model_count_calls : ctz_model ->
 forall mc x, Int64.unsigned x<>0 ->
  Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
   E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x)))).
Proof.
 intros Model mc x Nonzero;apply eval_ctz64_from_external;exact (Model _ mc x Nonzero).
Qed.

Theorem fe_invert_initialized_local_spec :
 ctz_model ->
 secp_jet_initialized_local_spec modinfo_fe_state f_simplicity_fe_invert
  (Word 8) (Word 8) (@literal_fe_invert Alg.CoreFunSem).
Proof.
 intro Model;apply fe_invert_initialized_local_spec_from_count_calls;exact (ctz_model_count_calls Model).
Qed.

Theorem scalar_invert_initialized_local_spec :
 ctz_model ->
 secp_jet_initialized_local_spec modinfo_scalar_initialized f_simplicity_scalar_invert
  (Word 8) (Word 8) (@literal_scalar_invert Alg.CoreFunSem).
Proof.
 intro Model;apply scalar_invert_initialized_local_spec_from_count_calls;exact (ctz_model_count_calls Model).
Qed.

Theorem gej_normalize_initialized_local_spec :
 ctz_model ->
 secp_jet_initialized_local_spec modinfo_fe_state f_simplicity_gej_normalize
  (Ty.Prod (Ty.Prod Word256 Word256) Word256) (Ty.Sum Ty.Unit (Ty.Prod Word256 Word256))
  (@literal_gej_normalize Alg.CoreFunSem).
Proof.
 intro Model;apply gej_normalize_initialized_local_spec_from_count_calls;exact (ctz_model_count_calls Model).
Qed.

Theorem gej_y_is_odd_initialized_local_spec :
 ctz_model ->
 secp_jet_initialized_local_spec modinfo_fe_state f_simplicity_gej_y_is_odd
  (Ty.Prod (Ty.Prod Word256 Word256) Word256) Bit (@literal_gej_y_is_odd Alg.CoreFunSem).
Proof.
 intro Model;apply gej_y_is_odd_initialized_local_spec_from_count_calls;exact (ctz_model_count_calls Model).
Qed.

Theorem swu_initialized_local_spec :
 ctz_model ->
 secp_jet_initialized_local_spec swu_startup f_simplicity_swu (Word 8)
  (Ty.Prod (Word 8) (Word 8)) (@literal_swu Alg.CoreFunSem).
Proof.
 intro Model;apply swu_initialized_local_spec_from_count_calls;exact (ctz_model_count_calls Model).
Qed.
