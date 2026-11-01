(** Canonical [outputIsFee] (Haskell/Simplicity/Elements/Programs/Transaction.hs:130)
    over the Elements primitives, and its value on every environment.

    [outputIsFee = outputAmount &&& (primitive OutputScriptHash &&& scribe (Right emptyHash) >>> eq)
       >>> match (injl unit) (injr (oih &&& (ooh &&& ih) >>> match false (drop (match false ih))))]
    with [emptyHash = toWord256 . integerHash256 $ bsHash mempty].

    No C execution is claimed here. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Digest Simplicity.Bit.
Require Import Simplicity.Util.Option Simplicity.Util.Monad.Reader.
Require Import C.jet_elements_prim C.jet_equality_spec.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets.
Import ListNotations.
Set Default Timeout 60.
Local Open Scope semantic_scope.

Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).
Local Notation AmountPair := (Ty.Prod (ConfTy Word256) (ConfTy Word64)).
Module AC := Alg.Core.Combinators.

(** [emptyHash]: the SHA-256 digest of the empty byte string. *)
Definition elements_empty_hash : Ty.tySem Word256 := from_hash256 (byteStringHash []).

(** [primitive OutputScriptHash &&& scribe (Right emptyHash) >>> eq]. *)
Definition fee_hash_test {alg : Core.Algebra} {A : Ty.Ty}
    (ph : alg A (Ty.Sum Ty.Unit Word256)) : alg A Bit :=
  AC.comp (AC.pair ph (Alg.scribe (inr elements_empty_hash : Ty.tySem (Ty.Sum Ty.Unit Word256))))
    (equality_spec (Ty.Sum Ty.Unit Word256)).

(** [match (injl unit) (injr (oih &&& (ooh &&& ih) >>> match false (drop (match false ih))))]. *)
Definition fee_tail {alg : Core.Algebra} :
    alg (Ty.Prod (Ty.Sum Ty.Unit AmountPair) Bit) (Ty.Sum Ty.Unit Bit) :=
  AC.case (AC.injl AC.unit)
    (AC.injr (AC.comp
      (AC.pair (AC.take (AC.drop AC.iden)) (AC.pair (AC.take (AC.take AC.iden)) (AC.drop AC.iden)))
      (AC.case Bit.false (AC.drop (AC.case Bit.false (AC.drop AC.iden)))))).

Definition fee_program {alg : Core.Algebra} {A : Ty.Ty}
    (pamt : alg A (Ty.Sum Ty.Unit AmountPair)) (ph : alg A (Ty.Sum Ty.Unit Word256)) :
    alg A (Ty.Sum Ty.Unit Bit) :=
  AC.comp (AC.pair pamt (fee_hash_test ph)) fee_tail.

Definition elements_output_is_fee_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Bit) :=
  fee_program elements_output_amount_spec (Primitive.Combinators.prim Elements.OutputScriptHash).

(** * Value *)

Definition fee_explicit {X : Ty.Ty} (c : Ty.tySem (ConfTy X)) : bool :=
  match c with inl _ => Datatypes.false | inr _ => Datatypes.true end.

(** The canonical fee bit of one output: explicit asset, explicit amount and
    script digest equal to the empty-string digest. *)
Definition canonical_fee_bit (o : txOutput) : bool :=
  fee_explicit (encode_asset (clearPrf (txoAsset o))) &&
  fee_explicit (encode_amount (clearPrf (txoAmount o))) &&
  Bit.toBool (|[ equality_spec (Ty.Sum Ty.Unit Word256) ]|
    (inr (from_hash256 (byteStringHash (txoScript o))), inr elements_empty_hash)).

Definition canonical_fee_result (a : Ty.tySem Word32) (environment : Elements.env) :
    Ty.tySem (Ty.Sum Ty.Unit Bit) :=
  match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some o => inr (if canonical_fee_bit o then inr tt else inl tt)
  | None => inl tt
  end.

(** * Reader semantics *)

Lemma fee_tail_parametric : Core.Parametric (fun term => @fee_tail term).
Proof. intros alg1 alg2 R. unfold fee_tail. auto 20 with parametricity. Qed.

Lemma fee_hash_const_parametric (A : Ty.Ty) :
  Core.Parametric (fun term => @Alg.scribe A (Ty.Sum Ty.Unit Word256)
    (inr elements_empty_hash) term).
Proof. intros alg1 alg2 R. apply Alg.scribe_Parametric. Qed.

Section Reader.
Context {E : Type}.
Local Notation RSem := (CoreSem (ReaderT_CIMonad E option_CIMonad)).

Lemma reader_pure {A B} (t : forall alg : Core.Algebra, alg A B) (Ht : Core.Parametric t)
    (x : Ty.tySem A) (environment : E) :
  @t RSem x environment = Some (|[ t _ ]| x).
Proof.
  pose proof (@CoreSem_initial (ReaderT_CIMonad E option_CIMonad) _ _ t Ht x) as Hs.
  exact (f_equal (fun f => f environment) Hs).
Qed.

Lemma fee_program_reader_sem {A : Ty.Ty}
    (pamt : RSem A (Ty.Sum Ty.Unit AmountPair)) (ph : RSem A (Ty.Sum Ty.Unit Word256))
    (a : Ty.tySem A) (environment : E) :
  fee_program pamt ph a environment =
    match pamt a environment, ph a environment with
    | Some p, Some h => Some (|[ fee_tail ]| (p,
        |[ equality_spec (Ty.Sum Ty.Unit Word256) ]| (h, inr elements_empty_hash)))
    | _, _ => None
    end.
Proof.
  pose proof (reader_pure (fun term => @fee_tail term) fee_tail_parametric) as HT.
  pose proof (reader_pure (fun term => @equality_spec (Ty.Sum Ty.Unit Word256) term)
    (equality_spec_parametric _)) as HE.
  pose proof (reader_pure _ (fee_hash_const_parametric A)) as HC.
  cbv beta in HT, HE, HC.
  unfold fee_program, fee_hash_test.
  remember (pamt a environment) as r1 eqn:HR1. remember (ph a environment) as r2 eqn:HR2.
  destruct r1 as [p|]; destruct r2 as [h|];
    lazy beta iota zeta delta -[fee_tail equality_spec Alg.scribe elements_empty_hash] in HR1, HR2 |- *;
    rewrite <- ?HR1, <- ?HR2; try reflexivity.
  - rewrite HC. lazy beta iota zeta delta -[fee_tail equality_spec Alg.scribe elements_empty_hash].
    rewrite (Alg.scribe_correct a). rewrite HE.
    lazy beta iota zeta delta -[fee_tail equality_spec Alg.scribe elements_empty_hash]. rewrite HT. reflexivity.
Qed.
End Reader.

Lemma fee_tail_value (x : Ty.tySem AmountPair) (b : Ty.tySem Bit) :
  |[ fee_tail ]| (inr x, b) =
    inr (if andb (@fee_explicit Word256 (fst x)) (@fee_explicit Word64 (snd x)) then b else inl tt).
Proof. destruct x as [[[c1 w1] | v1] [[c2 w2] | v2]]; reflexivity. Qed.

Lemma bit_of_toBool (b : Ty.tySem Bit) : (if Bit.toBool b then inr tt else inl tt) = b.
Proof. destruct b as [u|u]; destruct u; reflexivity. Qed.

Theorem elements_output_is_fee_sem a environment :
  @elements_output_is_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (canonical_fee_result a environment).
Proof.
  unfold elements_output_is_fee_spec.
  change (fee_program
    (@elements_output_amount_spec (PrimitivePrimSem option_Monad_Zero) :
      CoreSem (ReaderT_CIMonad Elements.env option_CIMonad) Word32 (Ty.Sum Ty.Unit AmountPair))
    (@Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word256)
      (PrimitivePrimSem option_Monad_Zero) Elements.OutputScriptHash :
      CoreSem (ReaderT_CIMonad Elements.env option_CIMonad) Word32 (Ty.Sum Ty.Unit Word256))
    a environment = Some (canonical_fee_result a environment)).
  rewrite fee_program_reader_sem.
  rewrite elements_output_amount_sem.
  change (@Primitive.Combinators.prim Word32 (Ty.Sum Ty.Unit Word256)
      (PrimitivePrimSem option_Monad_Zero) Elements.OutputScriptHash a environment)
    with (Elements.sem Elements.OutputScriptHash a environment).
  unfold Elements.sem, amount_pair_result, canonical_fee_result, canonical_fee_bit. cbv zeta.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [o|];
    [|reflexivity].
  cbn [Datatypes.option_map].
  f_equal. rewrite fee_tail_value. cbn [fst snd]. f_equal.
  destruct (fee_explicit (encode_asset (clearPrf (txoAsset o))));
  destruct (fee_explicit (encode_amount (clearPrf (txoAmount o))));
    cbn [andb]; try reflexivity.
  symmetry. apply bit_of_toBool.
Qed.
