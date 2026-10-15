(** Shared indexed-result conversion and three actual C getter contracts.
    Hashes use the checked four-limb byte decoder. Outpoint indexes use the
    checked low-bit-first State traversal, not a second mathematical spec. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_sequence_literal.
Require Import C.jet_haskell_word_conversion C.jet_haskell_hash_word.
Require Import C.jet_elements_indexed_ptr C.jet_elements_indexed_ptr_jets.
Require Import C.jet_elements_current_ptr_jets C.jet_elements_current_input_jets.
Require Import C.jet_elements_current_sequence_literal C.jet_uint32_array_init.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition elements_indexed_literal_result {E X : Type} {B : Ty}
    (elems : E -> list X) (encode : X -> tySem B)
    (a : tySem Word32) (environment : E) : option (tySem (Ty.Sum Ty.Unit B)) :=
  Some (match nth_error (elems environment) (Z.to_nat (haskell_from_word 5 a)) with
        | None => inl tt | Some x => inr (encode x) end).

Lemma elements_indexed_literal_matches {E X : Type} {B : Ty}
    (elems : E -> list X) (old literal : X -> tySem B)
    (H : forall x, old x = literal x) a environment :
  Some (match nth_error (elems environment) (Z.to_nat (toZ a)) with
        | None => inl tt | Some x => inr (old x) end) =
    elements_indexed_literal_result elems literal a environment.
Proof.
  unfold elements_indexed_literal_result. rewrite haskell_from_word_matches.
  destruct (nth_error (elems environment) (Z.to_nat (toZ a))) as [x|];
    [rewrite H|]; reflexivity.
Qed.

Definition haskell_encode_outpoint (op : outpoint) : tySem (Ty.Prod Word256 Word32) :=
  (haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (opHash op))),
   haskell_to_word 5 (Int.unsigned (opIndex op))).

Lemma haskell_encode_outpoint_matches op :
  (from_hash256 (opHash op), @fromZ (WordToZ 5) (Int.unsigned (opIndex op))) =
    haskell_encode_outpoint op.
Proof.
  unfold haskell_encode_outpoint.
  rewrite haskell_hash_word256, haskell_to_word_matches. reflexivity.
Qed.

Definition elements_input_prev_outpoint_literal_spec :=
  elements_indexed_literal_result (fun e => sigTxIn (Elements.envTx e))
    (fun txi => haskell_encode_outpoint (sigTxiPreviousOutpoint txi)).

Lemma elements_input_prev_outpoint_literal_matches a environment :
  @elements_input_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_prev_outpoint_literal_spec a environment.
Proof.
  rewrite elements_input_prev_outpoint_sem.
  unfold elements_input_prev_outpoint_result, elements_input_prev_outpoint_literal_spec.
  apply (@elements_indexed_literal_matches Elements.env sigTxInput (Ty.Prod Word256 Word32)
    (fun e => sigTxIn (Elements.envTx e))
    (fun txi => (from_hash256 (opHash (sigTxiPreviousOutpoint txi)),
      @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi)))))
    (fun txi => haskell_encode_outpoint (sigTxiPreviousOutpoint txi))).
  intros txi. apply haskell_encode_outpoint_matches.
Qed.

Definition elements_current_prev_outpoint_literal_spec :=
  elements_current_literal_result elements_input_prev_outpoint_literal_spec.

Lemma elements_current_prev_outpoint_literal_matches a environment :
  @elements_current_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_current_prev_outpoint_literal_spec a environment.
Proof.
  unfold elements_current_prev_outpoint_spec, elements_current_prev_outpoint_literal_spec.
  apply elements_current_literal_sem. exact elements_input_prev_outpoint_literal_matches.
Qed.

Theorem elements_input_prev_outpoint_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_prev_outpoint elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) outpoint_rep 544 96 0 696)
    elements_input_prev_outpoint_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_prev_outpoint_literal_matches|exact elements_input_prev_outpoint_local_spec].
Qed.

Theorem elements_current_prev_outpoint_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_current_prev_outpoint elements_ge Elements.env Ty.Unit
    (Ty.Prod Word256 Word32)
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx outpoint_rep 544 96 0 696)
    elements_current_prev_outpoint_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_current_prev_outpoint_literal_matches|exact elements_current_prev_outpoint_local_spec].
Qed.

Definition elements_output_script_hash_literal_spec :=
  elements_indexed_literal_result (fun e => sigTxOut (Elements.envTx e))
    (fun txo => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (byteStringHash (txoScript txo))))).

Lemma elements_output_script_hash_literal_matches a environment :
  @elements_output_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_output_script_hash_literal_spec a environment.
Proof.
  rewrite elements_output_script_hash_sem.
  unfold elements_output_script_hash_result, elements_output_script_hash_literal_spec.
  apply (@elements_indexed_literal_matches Elements.env txOutput Word256
    (fun e => sigTxOut (Elements.envTx e))
    (fun txo => from_hash256 (byteStringHash (txoScript txo)))
    (fun txo => haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist (byteStringHash (txoScript txo)))))).
  intros txo. symmetry. apply haskell_hash_word256.
Qed.

Theorem elements_output_script_hash_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_output_script_hash elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) 248 180 8 704)
    elements_output_script_hash_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_output_script_hash_literal_matches|exact elements_output_script_hash_local_spec].
Qed.
