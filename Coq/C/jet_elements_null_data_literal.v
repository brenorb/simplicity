(** Literal output_null_datum indexing and22 constructor encodings, reusing
    the checked Haskell State-word and four-limb hash conversion bridges. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Bit Simplicity.Util.Option.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_prim.
Require Import C.jet_application_context_contract C.jet_application_context_transport.
Require Import C.jet_haskell_word_conversion C.jet_haskell_hash_word C.jet_elements_sequence_literal.
Require Import C.jet_elements_tap_getters_literal C.jet_elements_null_data_opcode C.jet_elements_null_data_index.
Require Import C.jet_elements_null_data_guard_compose C.jet_elements_null_data_layout.
Require Import C.jet_elements_null_data_environment C.jet_elements_null_data_contract.
Require Import C.jet_elements_null_data_parse.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Local Notation OpcodeTy := (Ty.Sum (Ty.Prod (Word 1) Word256) (Ty.Sum (Ty.Sum Ty.Unit Ty.Unit) (Word 2))).
Local Notation ResultTy := (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit OpcodeTy)).

Definition haskell_encode_null_datum (d : txNullDatumF hash256) : Ty.tySem OpcodeTy :=
  match d with
  | Immediate h => inl (haskell_to_word 1 0, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | PushData h => inl (haskell_to_word 1 1, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | PushData2 h => inl (haskell_to_word 1 2, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | PushData4 h => inl (haskell_to_word 1 3, haskell_to_word 8 (haskell_integer_hash256 (hash256_to_bytelist h)))
  | OP1Negate => inr (inl (inl tt))
  | OPReserved => inr (inl (inr tt))
  | OP1 => inr (inr (haskell_to_word 2 0))
  | OP2 => inr (inr (haskell_to_word 2 1))
  | OP3 => inr (inr (haskell_to_word 2 2))
  | OP4 => inr (inr (haskell_to_word 2 3))
  | OP5 => inr (inr (haskell_to_word 2 4))
  | OP6 => inr (inr (haskell_to_word 2 5))
  | OP7 => inr (inr (haskell_to_word 2 6))
  | OP8 => inr (inr (haskell_to_word 2 7))
  | OP9 => inr (inr (haskell_to_word 2 8))
  | OP10 => inr (inr (haskell_to_word 2 9))
  | OP11 => inr (inr (haskell_to_word 2 10))
  | OP12 => inr (inr (haskell_to_word 2 11))
  | OP13 => inr (inr (haskell_to_word 2 12))
  | OP14 => inr (inr (haskell_to_word 2 13))
  | OP15 => inr (inr (haskell_to_word 2 14))
  | OP16 => inr (inr (haskell_to_word 2 15))
  end.

Lemma haskell_encode_null_datum_matches d unused_hash :
  elements_datum_value d unused_hash = haskell_encode_null_datum d.
Proof.
  destruct d; cbn [haskell_encode_null_datum elements_datum_value elements_opcode_value
    elements_datum_push elements_datum_number elements_datum_bit elements_datum_small elements_datum_hash];
    rewrite ?haskell_hash_word256, ?haskell_to_word_matches; reflexivity.
Qed.

Definition elements_output_null_datum_literal_spec (a : Ty.tySem (Ty.Prod Word32 Word32)) (environment : Elements.env) :
    option (Ty.tySem ResultTy) :=
  Some (match hd_error (skipn (Z.to_nat (haskell_from_word 5 (fst a))) (sigTxOut (Elements.envTx environment))) with
        | None => inl tt
        | Some txo =>
            match txNullData (txoScript txo) with
            | None => inl tt
            | Some parsed => inr
                (match hd_error (skipn (Z.to_nat (haskell_from_word 5 (snd a))) parsed) with
                 | None => inl tt
                 | Some d => inr (haskell_encode_null_datum (mapNullDatum byteStringHash d))
                 end)
            end
        end).

Lemma elements_output_null_datum_literal_matches a environment :
  @elements_output_null_datum_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    elements_output_null_datum_literal_spec a environment.
Proof.
  destruct a as [iw jw].
  change (Elements.sem Elements.OutputNullDatum (iw, jw) environment =
    elements_output_null_datum_literal_spec (iw, jw) environment).
  unfold elements_output_null_datum_literal_spec. cbn [fst snd].
  rewrite !haskell_from_word_matches, <- !nth_error_is_list_to_maybe_drop.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ iw))) as [txo|] eqn:HO.
  - destruct (txNullData (txoScript txo)) as [parsed|] eqn:HP.
    + rewrite (elements_output_null_datum_parsed_sem environment iw jw txo parsed
        (Int64.repr (toZ jw)) (byteStringHash []) HO HP (word32_int64_unsigned jw)).
      unfold elements_null_data_index_value. rewrite word32_int64_unsigned.
      rewrite <- nth_error_is_list_to_maybe_drop.
      destruct (nth_error parsed (Z.to_nat (toZ jw))) as [d|];
        [rewrite haskell_encode_null_datum_matches|]; reflexivity.
    + cbn [Elements.sem fst snd]. rewrite HO, HP. reflexivity.
  - cbn [Elements.sem fst snd]. rewrite HO. reflexivity.
Qed.

Theorem elements_output_null_datum_literal_bitmachine_spec :
  application_jet_bitmachine_spec f_simplicity_output_null_datum elements_ge Elements.env
    (Ty.Prod Word32 Word32) ResultTy elements_null_data_environment_rep
    elements_output_null_datum_literal_spec.
Proof.
  eapply application_jet_bitmachine_spec_pointwise;
    [exact elements_output_null_datum_literal_matches|exact elements_output_null_datum_bitmachine_spec].
Qed.
