(** Literal port of Programs/Issuance.hs, [issuance], not an arithmetic
    replacement specification: ReissuanceEntropy &&& NewIssuanceContract,
    followed by the original nested match/copair program. *)
From Coq Require Import ZArith List.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Alg.
Require Import Simplicity.Util.Option C.jet_elements_prim C.jet_elements_current_spec C.jet_elements_prim_sem.
Import ListNotations.
Set Default Timeout 10.
Module ISC := Alg.Core.Combinators.

Definition issuance_status_digest_option : Ty := Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256).
Definition issuance_status_payload : Ty := Ty.Sum Ty.Unit Bit.
Definition issuance_status_type : Ty := Ty.Sum Ty.Unit issuance_status_payload.

Definition issuance_status_route {core : Alg.Core.Algebra} :
    core (Ty.Prod issuance_status_digest_option issuance_status_digest_option) issuance_status_type :=
  ISC.case (ISC.injl ISC.unit)
    (ISC.case
      (ISC.drop (ISC.copair (ISC.injl ISC.unit)
        (ISC.copair (ISC.injr (ISC.injl ISC.unit)) (ISC.injr (ISC.injr Bit.false)))))
      (ISC.injr (ISC.injr Bit.true))).

Lemma issuance_status_route_parametric : Alg.Core.Parametric (@issuance_status_route).
Proof.
  intros alg1 alg2 R. unfold issuance_status_route, ISC.copair, Bit.true, Bit.false.
  solve [repeat first [apply Alg.comp_Parametric | apply Alg.pair_Parametric |
    apply Alg.case_Parametric | apply Alg.injl_Parametric | apply Alg.injr_Parametric |
    apply Alg.take_Parametric | apply Alg.drop_Parametric | apply Alg.unit_Parametric |
    apply Alg.iden_Parametric]].
Qed.

Definition elements_issuance_status_spec {alg : Primitive.Algebra} : alg Word32 issuance_status_type :=
  elements_comp
    (elements_pair (Primitive.Combinators.prim Elements.ReissuanceEntropy)
                   (Primitive.Combinators.prim Elements.NewIssuanceContract))
    (elements_core (@issuance_status_route)).

Lemma elements_issuance_status_spec_parametric : Primitive.Parametric (@elements_issuance_status_spec).
Proof.
  intros alg1 alg2 [R [[HC HA] [HP]]]. set (RC := Alg.Core.Parametric.Pack HC).
  unfold elements_issuance_status_spec, elements_comp, elements_pair, elements_core.
  apply (Alg.comp_Parametric RC).
  - apply (Alg.pair_Parametric RC); apply HP.
  - exact (issuance_status_route_parametric _ _ RC).
Qed.

Definition issuance_status_of_input (txi : sigTxInput) : Ty.tySem issuance_status_payload :=
  match sigTxiIssuance txi with
  | None => inl tt
  | Some (inl _) => inr (inl tt)
  | Some (inr _) => inr (inr tt)
  end.

Definition issuance_status_result (elems : list sigTxInput) (a : Ty.tySem Word32) : Ty.tySem issuance_status_type :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | None => inl tt
  | Some txi => inr (issuance_status_of_input txi)
  end.

Theorem elements_issuance_status_sem a environment :
  @elements_issuance_status_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_status_result (sigTxIn (Elements.envTx environment)) a).
Proof.
  unfold elements_issuance_status_spec. rewrite elements_comp_sem, elements_pair_sem.
  change (match Elements.sem Elements.ReissuanceEntropy a environment,
                Elements.sem Elements.NewIssuanceContract a environment with
    | Some b, Some c => @elements_core _ _ (@issuance_status_route)
          (PrimitivePrimSem option_Monad_Zero) (b, c) environment
    | _, _ => None end = Some (issuance_status_result (sigTxIn (Elements.envTx environment)) a)).
  unfold Elements.sem, issuance_status_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi | ].
  - destruct (sigTxiIssuance txi) as [[new | re] | ] eqn:HI;
      cbn [Datatypes.option_map];
      rewrite (elements_core_sem (@issuance_status_route) issuance_status_route_parametric);
      unfold issuance_status_of_input; rewrite HI; reflexivity.
  - rewrite (elements_core_sem (@issuance_status_route) issuance_status_route_parametric).
    reflexivity.
Qed.
