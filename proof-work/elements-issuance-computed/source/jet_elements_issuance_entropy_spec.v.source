(** Primitive-based Programs/Issuance.hs. No cache, execution or output
    predicate appears in these Simplicity programs. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Alg.
Require Import Simplicity.Util.Option C.jet_elements_prim C.jet_elements_current_spec C.jet_elements_prim_sem.
Require Import C.jet_elements_issuance_calc_spec.
Module EC := Alg.Core.Combinators.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque calculate_issuance_entropy_spec calculate_asset_spec
  calculate_explicit_token_spec calculate_confidential_token_spec.

Definition issuance_digest_option : Ty := Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256).
Definition issuance_prevout_option : Ty := Ty.Sum Ty.Unit (Ty.Prod Word256 Word32).

Definition new_issuance_entropy_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_digest_option issuance_prevout_option) issuance_digest_option :=
  EC.case (EC.injl EC.unit)
    (EC.case (EC.injr (EC.injl EC.unit))
      (EC.comp (EC.pair (EC.drop EC.iden) (EC.take EC.iden))
        (EC.case (EC.injl EC.unit) (EC.injr (EC.injr calculate_issuance_entropy_spec))))).

Lemma new_issuance_entropy_route_parametric : Alg.Core.Parametric (@new_issuance_entropy_route).
Proof.
  intros alg1 alg2 R. unfold new_issuance_entropy_route.
  pose proof (calculate_issuance_entropy_spec_parametric alg1 alg2 R) as HCalc.
  solve [repeat first [exact HCalc | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.case_Parametric | apply Alg.injl_Parametric | apply Alg.injr_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.unit_Parametric |
    apply Alg.iden_Parametric]].
Qed.

Definition issuance_entropy_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_digest_option (Ty.Prod issuance_digest_option issuance_prevout_option))
      issuance_digest_option :=
  EC.case (EC.injl EC.unit)
    (EC.case (EC.drop new_issuance_entropy_route) (EC.take (EC.injr (EC.injr EC.iden)))).

Lemma issuance_entropy_route_parametric : Alg.Core.Parametric (@issuance_entropy_route).
Proof.
  intros alg1 alg2 R. unfold issuance_entropy_route.
  pose proof (new_issuance_entropy_route_parametric alg1 alg2 R) as HNew.
  solve [repeat first [exact HNew | apply Alg.case_Parametric |
    apply Alg.injl_Parametric | apply Alg.injr_Parametric | apply Alg.take_Parametric |
    apply Alg.drop_Parametric | apply Alg.unit_Parametric | apply Alg.iden_Parametric]].
Qed.

Definition elements_issuance_entropy_spec {alg : Primitive.Algebra} :
    alg Word32 issuance_digest_option :=
  elements_comp
    (elements_pair (Primitive.Combinators.prim Elements.ReissuanceEntropy)
      (elements_pair (Primitive.Combinators.prim Elements.NewIssuanceContract)
        (Primitive.Combinators.prim Elements.InputPrevOutpoint)))
    (elements_core (@issuance_entropy_route)).

Lemma elements_issuance_entropy_spec_parametric : Primitive.Parametric (@elements_issuance_entropy_spec).
Proof.
  intros alg1 alg2 [R [[HC HA] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_entropy_spec, elements_comp, elements_pair, elements_core.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [apply HP|apply (Alg.pair_Parametric RC); apply HP].
  - exact (issuance_entropy_route_parametric _ _ RC).
Qed.

Definition issuance_entropy_of_input (txi : sigTxInput) : Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl new) => inr (@calculate_issuance_entropy_spec Alg.CoreFunSem
      ((from_hash256 (opHash (sigTxiPreviousOutpoint txi)),
        @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi)))),
       from_hash256 (newIssuanceContractHash new)))
  | Some (inr re) => inr (from_hash256 (reissuanceEntropy re))
  end.

Definition issuance_entropy_result (elems : list sigTxInput) (a : Ty.tySem Word32) :
    Ty.tySem issuance_digest_option :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | None => inl tt
  | Some txi => inr (issuance_entropy_of_input txi)
  end.

Theorem elements_issuance_entropy_sem a environment :
  @elements_issuance_entropy_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_entropy_result (sigTxIn (Elements.envTx environment)) a).
Proof.
  unfold elements_issuance_entropy_spec. rewrite elements_comp_sem, !elements_pair_sem.
  change (match Elements.sem Elements.ReissuanceEntropy a environment,
    Elements.sem Elements.NewIssuanceContract a environment,
    Elements.sem Elements.InputPrevOutpoint a environment with
    | Some r, Some n, Some p => @elements_core _ _ (@issuance_entropy_route)
        (PrimitivePrimSem option_Monad_Zero) (r, (n, p)) environment
    | _, _, _ => None end =
    Some (issuance_entropy_result (sigTxIn (Elements.envTx environment)) a)).
  unfold Elements.sem, issuance_entropy_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi | ].
  - destruct (sigTxiIssuance txi) as [[new | re] | ] eqn:HI;
      cbn [Datatypes.option_map];
      rewrite (elements_core_sem (@issuance_entropy_route) issuance_entropy_route_parametric);
      unfold issuance_entropy_of_input; rewrite HI; reflexivity.
  - rewrite (elements_core_sem (@issuance_entropy_route) issuance_entropy_route_parametric).
    reflexivity.
Qed.

Definition issuance_asset_route {core : Alg.Core.Algebra} :
    core issuance_digest_option issuance_digest_option :=
  EC.copair (EC.injl EC.unit)
    (EC.injr (EC.copair (EC.injl EC.unit) (EC.injr calculate_asset_spec))).

Lemma issuance_asset_route_parametric : Alg.Core.Parametric (@issuance_asset_route).
Proof.
  intros alg1 alg2 R. unfold issuance_asset_route, EC.copair, EC.elimS.
  pose proof (calculate_asset_spec_parametric alg1 alg2 R) as HCalc.
  solve [repeat first [exact HCalc | apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.case_Parametric | apply Alg.injl_Parametric | apply Alg.injr_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.unit_Parametric |
    apply Alg.iden_Parametric]].
Qed.

Definition elements_issuance_asset_spec {alg : Primitive.Algebra} :
    alg Word32 issuance_digest_option :=
  elements_comp elements_issuance_entropy_spec (elements_core (@issuance_asset_route)).

Lemma elements_issuance_asset_spec_parametric : Primitive.Parametric (@elements_issuance_asset_spec).
Proof.
  intros alg1 alg2 RP.
  pose proof (elements_issuance_entropy_spec_parametric alg1 alg2 RP) as HE.
  destruct RP as [R [[HC HA] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_asset_spec, elements_comp, elements_core.
  apply (Alg.comp_Parametric RC).
  - exact HE.
  - exact (issuance_asset_route_parametric _ _ RC).
Qed.

Definition issuance_asset_of_input (txi : sigTxInput) : Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match issuance_entropy_of_input txi with
  | inl _ => inl tt
  | inr h => inr (@calculate_asset_spec Alg.CoreFunSem h)
  end.

Definition issuance_asset_result (elems : list sigTxInput) (a : Ty.tySem Word32) :
    Ty.tySem issuance_digest_option :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | None => inl tt
  | Some txi => inr (issuance_asset_of_input txi)
  end.

Theorem elements_issuance_asset_sem a environment :
  @elements_issuance_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_asset_result (sigTxIn (Elements.envTx environment)) a).
Proof.
  unfold elements_issuance_asset_spec. rewrite elements_comp_sem, elements_issuance_entropy_sem.
  rewrite (elements_core_sem (@issuance_asset_route) issuance_asset_route_parametric).
  unfold issuance_entropy_result, issuance_asset_result.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi | ];
    [unfold issuance_asset_of_input; destruct (issuance_entropy_of_input txi)|]; reflexivity.
Qed.

Definition issuance_amount_option : Ty :=
  Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) Word64)).

Definition issuance_token_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_digest_option issuance_amount_option) issuance_digest_option :=
  EC.case (EC.injl EC.unit)
    (EC.case (EC.injr (EC.injl EC.unit))
      (EC.comp (EC.pair (EC.drop EC.iden) (EC.take EC.iden))
        (EC.case (EC.injl EC.unit)
          (EC.case (EC.injl EC.unit)
            (EC.injr (EC.injr
              (EC.case (EC.drop calculate_confidential_token_spec)
                       (EC.drop calculate_explicit_token_spec)))))))).

Lemma issuance_token_route_parametric : Alg.Core.Parametric (@issuance_token_route).
Proof.
  intros alg1 alg2 R. unfold issuance_token_route.
  pose proof (calculate_confidential_token_spec_parametric alg1 alg2 R) as HC.
  pose proof (calculate_explicit_token_spec_parametric alg1 alg2 R) as HE.
  apply (Alg.case_Parametric R).
  - apply Alg.injl_Parametric, Alg.unit_Parametric.
  - apply (Alg.case_Parametric R).
    + apply Alg.injr_Parametric, Alg.injl_Parametric, Alg.unit_Parametric.
    + apply (Alg.comp_Parametric R).
      * apply (Alg.pair_Parametric R).
        -- apply Alg.drop_Parametric, Alg.iden_Parametric.
        -- apply Alg.take_Parametric, Alg.iden_Parametric.
      * apply (Alg.case_Parametric R).
        -- apply Alg.injl_Parametric, Alg.unit_Parametric.
        -- apply (Alg.case_Parametric R).
           ++ apply Alg.injl_Parametric, Alg.unit_Parametric.
           ++ apply Alg.injr_Parametric, Alg.injr_Parametric.
              apply (Alg.case_Parametric R).
              ** apply Alg.drop_Parametric. exact HC.
              ** apply Alg.drop_Parametric. exact HE.
Qed.

Definition elements_issuance_token_spec {alg : Primitive.Algebra} :
    alg Word32 issuance_digest_option :=
  elements_comp
    (elements_pair elements_issuance_entropy_spec (Primitive.Combinators.prim Elements.IssuanceAssetAmount))
    (elements_core (@issuance_token_route)).

Lemma elements_issuance_token_spec_parametric : Primitive.Parametric (@elements_issuance_token_spec).
Proof.
  intros alg1 alg2 RP.
  pose proof (elements_issuance_entropy_spec_parametric alg1 alg2 RP) as HE.
  destruct RP as [R [[HC HA] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_token_spec, elements_comp, elements_pair, elements_core.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); [exact HE|apply HP].
  - exact (issuance_token_route_parametric _ _ RC).
Qed.

Definition issuance_token_for_amount {P : Set} (amt : amountWith P) (h : Ty.tySem Word256) : Ty.tySem Word256 :=
  match amt with
  | Explicit _ => @calculate_explicit_token_spec Alg.CoreFunSem h
  | Confidential _ _ => @calculate_confidential_token_spec Alg.CoreFunSem h
  end.

Definition issuance_token_of_input (txi : sigTxInput) : Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl new) => inr (issuance_token_for_amount (newIssuanceAmount new)
      (@calculate_issuance_entropy_spec Alg.CoreFunSem
        ((from_hash256 (opHash (sigTxiPreviousOutpoint txi)),
          @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi)))),
         from_hash256 (newIssuanceContractHash new))))
  | Some (inr re) => inr (issuance_token_for_amount (reissuanceAmount re) (from_hash256 (reissuanceEntropy re)))
  end.

Definition issuance_token_result (elems : list sigTxInput) (a : Ty.tySem Word32) :
    Ty.tySem issuance_digest_option :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | None => inl tt
  | Some txi => inr (issuance_token_of_input txi)
  end.

Theorem elements_issuance_token_sem a environment :
  @elements_issuance_token_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_token_result (sigTxIn (Elements.envTx environment)) a).
Proof.
  unfold elements_issuance_token_spec.
  rewrite elements_comp_sem, elements_pair_sem, elements_issuance_entropy_sem.
  change (match Elements.sem Elements.IssuanceAssetAmount a environment with
    | Some amt => @elements_core _ _ (@issuance_token_route)
        (PrimitivePrimSem option_Monad_Zero)
        (issuance_entropy_result (sigTxIn (Elements.envTx environment)) a, amt) environment
    | None => None end = Some (issuance_token_result (sigTxIn (Elements.envTx environment)) a)).
  unfold Elements.sem, issuance_entropy_result, issuance_token_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi | ].
  - destruct (sigTxiIssuance txi) as [[new | re] | ] eqn:HI;
      cbn [Datatypes.option_map];
      rewrite (elements_core_sem (@issuance_token_route) issuance_token_route_parametric);
      unfold issuance_entropy_of_input, issuance_token_of_input; rewrite HI;
      cbn [Datatypes.option_map].
    + destruct (newIssuanceAmount new) as [v | [odd x] prf]; reflexivity.
    + destruct (reissuanceAmount re) as [v | [odd x] prf]; reflexivity.
    + reflexivity.
  - rewrite (elements_core_sem (@issuance_token_route) issuance_token_route_parametric).
    reflexivity.
Qed.
