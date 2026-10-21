(** Complete original C issuance getters against literal primitive-bearing programs.
    The initial cached-value relation is unchanged; builder correctness is separate. *)
From Coq Require Import ZArith.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import Simplicity.Util.Option C.jet_elements_prim C.jet_elements_prim_sem C.jet_elements_current_spec.
Require Import C.jet_elements_issuance_calc_literal C.jet_elements_issuance_entropy_spec C.jet_elements_issuance_computed_exec C.jet_elements_issuance_computed_local.
Require Import C.jet_application_sep C.jet_elements_indexed_ptr C.jet_elements_linkage C.jets_elements.
Module LC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition literal_new_issuance_entropy_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_digest_option issuance_prevout_option) issuance_digest_option :=
  LC.case (LC.injl LC.unit)
    (LC.case (LC.injr (LC.injl LC.unit))
      (LC.comp (LC.pair (LC.drop LC.iden) (LC.take LC.iden))
        (LC.case (LC.injl LC.unit) (LC.injr (LC.injr literal_calculate_issuance_entropy))))).

Lemma literal_new_issuance_entropy_route_matches core : @literal_new_issuance_entropy_route core = @new_issuance_entropy_route core.
Proof.
  unfold literal_new_issuance_entropy_route, new_issuance_entropy_route.
  rewrite literal_calculate_issuance_entropy_matches. reflexivity.
Qed.

Definition literal_issuance_entropy_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_digest_option (Ty.Prod issuance_digest_option issuance_prevout_option))
      issuance_digest_option :=
  LC.case (LC.injl LC.unit)
    (LC.case (LC.drop literal_new_issuance_entropy_route) (LC.take (LC.injr (LC.injr LC.iden)))).

Lemma literal_issuance_entropy_route_matches core : @literal_issuance_entropy_route core = @issuance_entropy_route core.
Proof.
  unfold literal_issuance_entropy_route, issuance_entropy_route.
  rewrite literal_new_issuance_entropy_route_matches. reflexivity.
Qed.

Definition literal_elements_issuance_entropy {alg : Primitive.Algebra} :
    alg Word32 issuance_digest_option :=
  elements_comp
    (elements_pair (Primitive.Combinators.prim Elements.ReissuanceEntropy)
      (elements_pair (Primitive.Combinators.prim Elements.NewIssuanceContract)
        (Primitive.Combinators.prim Elements.InputPrevOutpoint)))
    (elements_core (@literal_issuance_entropy_route)).

Lemma literal_elements_issuance_entropy_matches alg : @literal_elements_issuance_entropy alg = @elements_issuance_entropy_spec alg.
Proof.
  unfold literal_elements_issuance_entropy, elements_issuance_entropy_spec, elements_comp, elements_pair, elements_core.
  rewrite literal_issuance_entropy_route_matches. reflexivity.
Qed.

Definition literal_issuance_asset_route {core : Alg.Core.Algebra} :
    core issuance_digest_option issuance_digest_option :=
  LC.copair (LC.injl LC.unit)
    (LC.injr (LC.copair (LC.injl LC.unit) (LC.injr literal_calculate_asset))).

Lemma literal_issuance_asset_route_matches core : @literal_issuance_asset_route core = @issuance_asset_route core.
Proof.
  unfold literal_issuance_asset_route, issuance_asset_route.
  rewrite literal_calculate_asset_matches. reflexivity.
Qed.

Definition literal_elements_issuance_asset {alg : Primitive.Algebra} :
    alg Word32 issuance_digest_option :=
  elements_comp literal_elements_issuance_entropy (elements_core (@literal_issuance_asset_route)).

Lemma literal_elements_issuance_asset_matches alg : @literal_elements_issuance_asset alg = @elements_issuance_asset_spec alg.
Proof.
  unfold literal_elements_issuance_asset, elements_issuance_asset_spec, elements_comp, elements_pair, elements_core.
  rewrite literal_elements_issuance_entropy_matches, literal_issuance_asset_route_matches. reflexivity.
Qed.

Definition literal_issuance_token_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_digest_option issuance_amount_option) issuance_digest_option :=
  LC.case (LC.injl LC.unit)
    (LC.case (LC.injr (LC.injl LC.unit))
      (LC.comp (LC.pair (LC.drop LC.iden) (LC.take LC.iden))
        (LC.case (LC.injl LC.unit)
          (LC.case (LC.injl LC.unit)
            (LC.injr (LC.injr
              (LC.case (LC.drop literal_calculate_confidential_token)
                       (LC.drop literal_calculate_explicit_token)))))))).

Lemma literal_issuance_token_route_matches core : @literal_issuance_token_route core = @issuance_token_route core.
Proof.
  unfold literal_issuance_token_route, issuance_token_route.
  rewrite literal_calculate_explicit_token_matches, literal_calculate_confidential_token_matches. reflexivity.
Qed.

Definition literal_elements_issuance_token {alg : Primitive.Algebra} :
    alg Word32 issuance_digest_option :=
  elements_comp
    (elements_pair literal_elements_issuance_entropy (Primitive.Combinators.prim Elements.IssuanceAssetAmount))
    (elements_core (@literal_issuance_token_route)).

Lemma literal_elements_issuance_token_matches alg : @literal_elements_issuance_token alg = @elements_issuance_token_spec alg.
Proof.
  unfold literal_elements_issuance_token, elements_issuance_token_spec, elements_comp, elements_pair, elements_core.
  rewrite literal_elements_issuance_entropy_matches, literal_issuance_token_route_matches. reflexivity.
Qed.

Lemma literal_elements_issuance_entropy_parametric : Primitive.Parametric (@literal_elements_issuance_entropy).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuance_entropy_matches alg1), (literal_elements_issuance_entropy_matches alg2).
  exact (elements_issuance_entropy_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_issuance_entropy_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_entropy elements_ge Elements.env Word32 issuance_digest_option
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (computed_issuance_hash_rep 72 issuance_entropy_of_input) 544 0 0 696)
    (fun a environment => @literal_elements_issuance_entropy (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  rewrite literal_elements_issuance_entropy_matches.
  exact elements_issuance_entropy_local_spec.
Qed.

Lemma literal_elements_issuance_asset_parametric : Primitive.Parametric (@literal_elements_issuance_asset).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuance_asset_matches alg1), (literal_elements_issuance_asset_matches alg2).
  exact (elements_issuance_asset_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_issuance_asset_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_asset elements_ge Elements.env Word32 issuance_digest_option
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (computed_issuance_hash_rep 168 issuance_asset_of_input) 544 0 0 696)
    (fun a environment => @literal_elements_issuance_asset (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  rewrite literal_elements_issuance_asset_matches.
  exact elements_issuance_asset_local_spec.
Qed.

Lemma literal_elements_issuance_token_parametric : Primitive.Parametric (@literal_elements_issuance_token).
Proof.
  intros alg1 alg2 R.
  rewrite (literal_elements_issuance_token_matches alg1), (literal_elements_issuance_token_matches alg2).
  exact (elements_issuance_token_spec_parametric alg1 alg2 R).
Qed.

Theorem elements_issuance_token_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token elements_ge Elements.env Word32 issuance_digest_option
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (computed_issuance_hash_rep 200 issuance_token_of_input) 544 0 0 696)
    (fun a environment => @literal_elements_issuance_token (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  rewrite literal_elements_issuance_token_matches.
  exact elements_issuance_token_local_spec.
Qed.
