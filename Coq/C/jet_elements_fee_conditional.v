(** Public contracts of the original [simplicity_output_is_fee] and
    [simplicity_total_fee] against their canonical Simplicity programs,
    conditional on the open SHA-256 property [empty_script_digest_unique].

    The C builder classifies an output as a fee by an empty script; the
    canonical programs test the script's SHA-256 digest against the digest of
    the empty string.  The predicates differ (reported in
    [JET_ELEMENTS_FEE_MISMATCHES.md], not corrected), and the exact reductions
    [fee_results_agree_everywhere_iff] and
    [total_fee_results_agree_everywhere_iff] show the jets agree with their
    programs on every environment iff the property holds.  Here the property
    is a visible premise of each public theorem: never an axiom, never proved,
    never refuted.  [total_fee] also keeps its explicit libc [memcmp_model]. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jet_application_sep C.jet_memcmp_model C.jets_elements C.jet_elements_linkage.
Require Import C.jet_elements_output_is_fee_spec C.jet_elements_output_is_fee_compare.
Require Import C.jet_elements_total_fee_spec C.jet_elements_total_fee_compare.
Require Import C.jet_elements_fee_flag_caller C.jet_elements_amount_jets C.jet_elements_asset_jets C.jet_elements_indexed_ptr.

Local Open Scope Z_scope.

Theorem output_is_fee_conditional_local_spec :
  empty_script_digest_unique ->
  application_jet_local_spec_sep f_simplicity_output_is_fee elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Ty.Unit))
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e)) processed_fee_rep 248 0 8 704)
    (fun a environment => @elements_output_is_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof. exact elements_output_is_fee_local_spec_if_digest_unique. Qed.

Theorem total_fee_conditional_local_spec :
  memcmp_model -> empty_script_digest_unique ->
  application_jet_local_spec_sep f_simplicity_total_fee elements_ge Elements.env Word256 Word64
    total_fee_env_rep
    (fun a environment => @elements_total_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof. exact elements_total_fee_local_spec_if_digest_unique. Qed.
