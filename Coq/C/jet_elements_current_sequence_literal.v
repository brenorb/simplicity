(** Actual C current_sequence against CurrentIndex >>> assert InputSequence,
    retaining the literal Haskell word conversions and full frame contract. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Clight Ctypes Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_contract C.jet_elements_current_spec.
Require Import C.jet_elements_current_jets C.jet_elements_indexed_scalar_jets.
Require Import C.jet_haskell_word_conversion C.jet_elements_count_payload.
Require Import C.jet_elements_sequence_literal.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_current_literal_result {B : Ty}
    (p : tySem Word32 -> Elements.env -> option (tySem (Ty.Sum Ty.Unit B)))
    (_ : tySem Ty.Unit) (environment : Elements.env) : option (tySem B) :=
  match p
      (haskell_to_word 5 (Z.of_nat (Elements.envIx environment))) environment with
  | Some (inr value) => Some value
  | _ => None
  end.

Lemma elements_current_literal_sem {B : Ty}
    (p q : tySem Word32 -> Elements.env -> option (tySem (Ty.Sum Ty.Unit B))) :
  (forall a e, p a e = q a e) ->
  forall a environment,
  @elements_current_spec (PrimitivePrimSem option_Monad_Zero) B p a environment =
    elements_current_literal_result q a environment.
Proof.
  intros HE a environment. unfold elements_current_spec.
  rewrite elements_comp_sem.
  change (@elements_assert_spec (PrimitivePrimSem option_Monad_Zero) Word32 B p
    (@fromZ (WordToZ 5) (Z.of_nat (Elements.envIx environment))) environment =
    elements_current_literal_result q a environment).
  rewrite elements_assert_sem, HE. unfold elements_current_literal_result.
  rewrite haskell_to_word_matches. reflexivity.
Qed.

Definition elements_current_sequence_literal_spec :=
  elements_current_literal_result elements_input_sequence_literal_spec.

Lemma elements_current_sequence_literal_matches a environment :
  @elements_current_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_sequence_literal_spec a environment.
Proof.
  apply elements_current_literal_sem. exact elements_input_sequence_literal_matches.
Qed.

Theorem elements_current_sequence_literal_local_spec :
  application_jet_local_spec f_simplicity_current_sequence elements_ge Elements.env Ty.Unit Word32
    (current_scalar_rep (fun e => sigTxIn (Elements.envTx e))
      (fun txi => Int.unsigned (sigTxiSequence txi)) 544 248 0 696)
    elements_current_sequence_literal_spec.
Proof.
  eapply application_jet_local_spec_pointwise;
    [exact elements_current_sequence_literal_matches|exact elements_current_sequence_local_spec].
Qed.

Print Assumptions elements_current_literal_sem.
Print Assumptions elements_current_sequence_literal_matches.
Print Assumptions elements_current_sequence_literal_local_spec.
