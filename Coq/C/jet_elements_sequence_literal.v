(** Literal Haskell toWord32 interpretation for the actual input_sequence jet.
    The generic state traversal is shared across widths; the full local C
    execution/framing contract is transported, not replaced by a list identity. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers Clight Ctypes Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage.
Require Import C.jet_application_sep C.jet_elements_indexed_scalar.
Require Import C.jet_elements_indexed_scalar_jets C.jet_haskell_word_conversion C.jet_predicate_spec.
Local Open Scope Z_scope.
Set Default Timeout 10.

Fixpoint haskell_from_word_acc n : Z -> tySem (Word n) -> Z :=
  match n as k return Z -> tySem (Word k) -> Z with
  | O => fun i w => match w with inl _ => 2 * i | inr _ => 2 * i + 1 end
  | S k => fun i w => let '(hi, lo) := w in
      haskell_from_word_acc k (haskell_from_word_acc k i hi) lo
  end.

Lemma haskell_from_word_acc_matches n i (a : tySem (Word n)) :
  haskell_from_word_acc n i a = i * word_modulus n + @toZ (WordToZ n) a.
Proof.
  revert i a. induction n as [|n IH]; intros i a.
  - destruct a as [[]|[]].
    + change (2 * i = i * 2 + 0). ring.
    + change (2 * i + 1 = i * 2 + 1). ring.
  - destruct a as [hi lo]. cbn [haskell_from_word_acc]. rewrite !IH.
    change ((i * word_modulus n + @toZ (WordToZ n) hi) * word_modulus n +
      @toZ (WordToZ n) lo = i * word_modulus (S n) +
      (@toZ (WordToZ n) hi * word_modulus n + @toZ (WordToZ n) lo)).
    rewrite word_modulus_S. ring.
Qed.

Definition haskell_from_word n (a : tySem (Word n)) := haskell_from_word_acc n 0 a.

Lemma haskell_from_word_matches n (a : tySem (Word n)) :
  haskell_from_word n a = @toZ (WordToZ n) a.
Proof.
  unfold haskell_from_word. rewrite haskell_from_word_acc_matches.
  ring.
Qed.

Definition elements_input_sequence_literal_spec
    (a : tySem Word32) (environment : Elements.env) :
    option (tySem (Ty.Sum Ty.Unit Word32)) :=
  Some (match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (haskell_from_word 5 a)) with
        | Some txi => inr (haskell_to_word 5 (Int.unsigned (sigTxiSequence txi)))
        | None => inl tt
        end).

Lemma elements_input_sequence_literal_matches a environment :
  @elements_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_input_sequence_literal_spec a environment.
Proof.
  rewrite elements_input_sequence_sem.
  unfold elements_input_sequence_literal_spec, indexed_scalar_result,
    elements_input_sequence_specv.
  rewrite haskell_from_word_matches.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a)));
    [rewrite haskell_to_word_matches|]; reflexivity.
Qed.

Lemma application_jet_local_spec_sep_pointwise f ge E A B rep spec1 spec2 :
  (forall a e, spec1 a e = spec2 a e) ->
  application_jet_local_spec_sep f ge E A B rep spec1 ->
  application_jet_local_spec_sep f ge E A B rep spec2.
Proof.
  intros HE HS e env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    HR HSep HB HA HF HC HM HI HW.
  destruct (HS e env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    HR HSep HB HA HF HC HM HI HW) as (mf & value & HV & HRest).
  exists mf, value. split; [rewrite <- HE; exact HV|exact HRest].
Qed.

Theorem elements_input_sequence_literal_local_spec :
  application_jet_local_spec_sep f_simplicity_input_sequence elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word32)
    (indexed_scalar_rep (fun e => sigTxIn (Elements.envTx e))
      (fun txi => Int.unsigned (sigTxiSequence txi)) 544 248 0 696)
    elements_input_sequence_literal_spec.
Proof.
  eapply application_jet_local_spec_sep_pointwise;
    [exact elements_input_sequence_literal_matches|exact elements_input_sequence_local_spec].
Qed.

Print Assumptions elements_input_sequence_literal_matches.
Print Assumptions application_jet_local_spec_sep_pointwise.
Print Assumptions elements_input_sequence_literal_local_spec.
