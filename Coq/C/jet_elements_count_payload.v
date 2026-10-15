(** C-to-literal-firstFail contracts independent of the indexed primitives'
    returned hash values. Counting observes only Left versus Right. These
    are actual unrestricted C local contracts, not just list identities. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Ctypes Clight Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_contract C.jet_firstFail_spec C.jet_firstFail_list.
Require Import C.jet_elements_count_canonical C.jet_elements_count_bridge C.jet_elements_count_local.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_count_observation_spec {X : Set}
    (elems : Elements.env -> list X) (payload : X -> tySem Word256) :
    tySem Ty.Unit -> Elements.env -> option (tySem Word32) :=
  @first_fail_program 5 Ty.Unit Word256
    (Alg.AssertionSem (ReaderT_CIMonadZero Elements.env option_Monad_Zero))
    (fun w e => indexed_list_primitive 5 (elems e) payload w).

Lemma elements_count_observation_spec_value {X : Set}
    (elems : Elements.env -> list X) (payload : X -> tySem Word256) e :
  Z.of_nat (length (elems e)) < 4294967296 ->
  elements_count_observation_spec elems payload tt e =
    Some (@fromZ (WordToZ 5) (Z.of_nat (length (elems e)))).
Proof.
  intros HLength. unfold elements_count_observation_spec.
  rewrite first_fail_program_reader_sem.
  apply first_fail_list_count. exact HLength.
Qed.

Lemma application_jet_local_spec_pointwise f ge E A B rep spec1 spec2 :
  (forall a e, spec1 a e = spec2 a e) ->
  application_jet_local_spec f ge E A B rep spec1 ->
  application_jet_local_spec f ge E A B rep spec2.
Proof.
  intros HE HS e env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a
    HR HB HA HF HC HM HI HW.
  destruct (HS e env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a
    HR HB HA HF HC HM HI HW) as (mf & value & HV & HRest).
  exists mf, value. split; [rewrite <- HE; exact HV|exact HRest].
Qed.

Theorem elements_num_inputs_any_payload_local_spec (payload : sigTxInput -> tySem Word256) :
  application_jet_local_spec f_simplicity_num_inputs elements_ge Elements.env Ty.Unit Word32
    elements_num_inputs_env_rep
    (elements_count_observation_spec (fun e => sigTxIn (Elements.envTx e)) payload).
Proof.
  eapply application_jet_local_spec_pointwise;
    [|exact elements_num_inputs_local_spec].
  intros [] e. rewrite elements_transaction_num_inputs_spec_length.
  symmetry. apply (@elements_count_observation_spec_value sigTxInput
    (fun env => sigTxIn (Elements.envTx env)) payload e).
  pose proof (sigTxInBounds (Elements.envTx e)) as HLength.
  rewrite Zlength_correct in HLength. change Int.modulus with 4294967296 in HLength. lia.
Qed.

Theorem elements_num_outputs_any_payload_local_spec (payload : txOutput -> tySem Word256) :
  application_jet_local_spec f_simplicity_num_outputs elements_ge Elements.env Ty.Unit Word32
    elements_num_outputs_env_rep
    (elements_count_observation_spec (fun e => sigTxOut (Elements.envTx e)) payload).
Proof.
  eapply application_jet_local_spec_pointwise;
    [|exact elements_num_outputs_local_spec].
  intros [] e. rewrite elements_transaction_num_outputs_spec_length.
  symmetry. apply (@elements_count_observation_spec_value txOutput
    (fun env => sigTxOut (Elements.envTx env)) payload e).
  pose proof (sigTxOutBounds (Elements.envTx e)) as HLength.
  rewrite Zlength_correct in HLength. change Int.modulus with 4294967296 in HLength. lia.
Qed.
