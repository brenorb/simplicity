(** The original C [simplicity_output_is_fee] compared with the canonical
    [outputIsFee] program on every represented environment.

    C classifies by actual script emptiness (the builder's [emptyScript] flag);
    the canonical program compares the script's SHA-256 digest with the digest
    of the empty string.  This module proves, without any premise beyond those
    of the C execution contract, that the two results differ exactly at an
    output with explicit asset and amount whose script is nonempty and has the
    empty-string digest, and that the jet meets its canonical specification on
    every environment iff no such script exists.  Neither the existence nor
    the absence of such a SHA-256 preimage is proved or assumed here: see
    [JET_ELEMENTS_FEE_MISMATCHES.md]. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import Simplicity.Ty Simplicity.Alg Simplicity.Word Simplicity.Digest Simplicity.Bit.
Require Import Simplicity.Util.Option.
Require Import C.jet_elements_prim C.jet_equality_spec C.jet_application_sep.
Require Import C.jet_elements_asset_jets C.jet_elements_amount_jets C.jet_elements_indexed_ptr.
Require Import C.jet_elements_fee_flag_exec C.jet_elements_fee_flag_caller C.jet_elements_output_is_fee_spec.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sequence_literal.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope semantic_scope.
Set Default Timeout 60.

Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).

(** * The open SHA-256 property *)

(** Every supported script (the port bounds script length below 2^32) whose
    SHA-256 digest equals that of the empty string is itself empty. *)
Definition empty_script_digest_unique : Prop :=
  forall s : script, Zlength s < Int.modulus -> byteStringHash s = byteStringHash [] -> s = [].

(** An output on which the canonical and C fee bits can disagree. *)
Definition fee_digest_collision (o : txOutput) : Prop :=
  fee_explicit (encode_asset (clearPrf (txoAsset o))) = Datatypes.true /\
  fee_explicit (encode_amount (clearPrf (txoAmount o))) = Datatypes.true /\
  txoScript o <> [] /\ byteStringHash (txoScript o) = byteStringHash [].

(** * Bit-level comparison *)

Lemma canonical_digest_bit_iff (s : script) :
  Bit.toBool (|[ equality_spec (Ty.Sum Ty.Unit Word256) ]|
    (inr (from_hash256 (byteStringHash s)), inr elements_empty_hash)) = Datatypes.true <->
  byteStringHash s = byteStringHash [].
Proof.
  rewrite equality_spec_true. unfold elements_empty_hash.
  generalize (byteStringHash s) (byteStringHash []). intros h1 h2. split.
  - intro HQ. injection HQ as HQ.
    rewrite <- (to_from_hash256 h1), <- (to_from_hash256 h2), HQ. reflexivity.
  - intros ->. reflexivity.
Qed.

Lemma prefix_one_asset (c : assetWith Datatypes.unit) :
  Int.eq Int.one (conf_prefix c) = fee_explicit (encode_asset c).
Proof. destruct c as [h | [odd x] p]; [|destruct odd]; reflexivity. Qed.

Lemma prefix_one_amount (c : amountWith Datatypes.unit) :
  Int.eq Int.one (conf_prefix c) = fee_explicit (encode_amount c).
Proof. destruct c as [v | [odd x] p]; [|destruct odd]; reflexivity. Qed.

Lemma processed_fee_bit_explicit (o : txOutput) :
  processed_fee_bit o =
    andb (andb (processed_fee_empty o) (fee_explicit (encode_asset (clearPrf (txoAsset o)))))
      (fee_explicit (encode_amount (clearPrf (txoAmount o)))).
Proof.
  unfold processed_fee_bit, fee_classifier. rewrite prefix_one_asset, prefix_one_amount. reflexivity.
Qed.

Theorem fee_bits_agree_iff (o : txOutput) :
  processed_fee_bit o = canonical_fee_bit o <-> ~ fee_digest_collision o.
Proof.
  rewrite processed_fee_bit_explicit. unfold canonical_fee_bit, fee_digest_collision, processed_fee_empty.
  pose proof (canonical_digest_bit_iff (txoScript o)) as HD.
  destruct (txoScript o) as [|b s] eqn:HS.
  - assert (HT : Bit.toBool (|[ equality_spec (Ty.Sum Ty.Unit Word256) ]|
      (inr (from_hash256 (byteStringHash [])), inr elements_empty_hash)) = Datatypes.true)
      by (apply HD; reflexivity).
    rewrite HT. split; [intros _ (_ & _ & HN & _); exact (HN eq_refl)|intros _].
    destruct (fee_explicit (encode_asset (clearPrf (txoAsset o))));
    destruct (fee_explicit (encode_amount (clearPrf (txoAmount o)))); reflexivity.
  - destruct (fee_explicit (encode_asset (clearPrf (txoAsset o)))) eqn:HA;
    destruct (fee_explicit (encode_amount (clearPrf (txoAmount o)))) eqn:HM; cbn [andb];
    try (split; [intros _ (HA' & HM' & _); discriminate|reflexivity]).
    destruct (Bit.toBool (|[ equality_spec (Ty.Sum Ty.Unit Word256) ]|
      (inr (from_hash256 (byteStringHash (b :: s))), inr elements_empty_hash))) eqn:HB.
    + split; [discriminate|]. intro HN. exfalso. apply HN.
      repeat split; [discriminate|apply HD; reflexivity].
    + split; [intros _ (_ & _ & _ & HH); apply HD in HH; discriminate|reflexivity].
Qed.

(** * Result-level comparison *)

Lemma some_inj {A : Type} (x y : A) : Some x = Some y -> x = y.
Proof. intro E. injection E. trivial. Qed.

Definition fee_collision_at (a : Ty.tySem Word32) (environment : Elements.env) : Prop :=
  match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some o => fee_digest_collision o
  | None => False
  end.

Theorem fee_results_agree_iff a environment :
  processed_fee_result a environment = canonical_fee_result a environment <->
  ~ fee_collision_at a environment.
Proof.
  unfold processed_fee_result, canonical_fee_result, fee_collision_at.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [o | ].
  - rewrite <- fee_bits_agree_iff. split.
    + intro HQ. injection HQ as HQ.
      destruct (processed_fee_bit o), (canonical_fee_bit o); congruence.
    + intros ->. reflexivity.
  - split; [intros _ HF; destruct HF | reflexivity].
Qed.

(** A one-input, one-output environment whose output has explicit asset and
    amount and the given script. *)
Section Witness.
Variable s : script.
Hypothesis Hs : Zlength s < Int.modulus.

Let h0 := byteStringHash [].
Definition fee_witness_input : sigTxInput :=
  {| sigTxiPegin := None;
     sigTxiPreviousOutpoint := {| opHash := h0; opIndex := Int.zero |};
     sigTxiTxo := {| utxoAsset := Explicit h0; utxoAmount := Explicit Int64.zero;
       utxoScript := []; utxoScript_bound := ltac:(cbv; reflexivity) |};
     sigTxiSequence := Int.zero; sigTxiIssuance := None; sigTxiAnnex := None;
     sigTxiScriptSig := []; sigTxiScriptSig_bound := ltac:(cbv; reflexivity) |}.
Definition fee_witness_output : txOutput :=
  {| txoAsset := Explicit h0; txoAmount := Explicit Int64.one; txoNonce := None;
     txoScript := s; txoScript_bound := Hs |}.
Definition fee_witness_tx : sigTx :=
  {| sigTxVersion := Int.zero; sigTxIn := [fee_witness_input]; sigTxOut := [fee_witness_output];
     sigTxLock := Int.zero;
     sigTxInBounds := ltac:(cbv; split; reflexivity);
     sigTxOutBounds := ltac:(cbv; split; [discriminate|reflexivity]) |}.
Definition fee_witness_env : Elements.env :=
  {| Elements.envTx := fee_witness_tx; Elements.envIx := 0%nat;
     Elements.envTap := {| tapleafVersion := Byte.zero; tapInternalKey := h0; tappath := [];
       tapScriptCMR := h0 |};
     Elements.envGenesisBlock := h0;
     Elements.envIxBounded := ltac:(cbv; constructor);
     Elements.envIxWord32 := ltac:(cbv; reflexivity) |}.
End Witness.

Definition fee_witness_index : Ty.tySem Word32 := @fromZ (WordToZ 5) 0.

Lemma fee_witness_index_nat : Z.to_nat (toZ fee_witness_index) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

(** Divergence on the witness: a nonempty supported script with the
    empty-string digest makes the proved C result differ from the canonical
    result (no such script is exhibited or excluded here). *)
Theorem fee_witness_differs (s : script) (Hs : Zlength s < Int.modulus) :
  s <> [] -> byteStringHash s = byteStringHash [] ->
  Some (processed_fee_result fee_witness_index (fee_witness_env s Hs)) <>
    @elements_output_is_fee_spec (PrimitivePrimSem option_Monad_Zero)
      fee_witness_index (fee_witness_env s Hs).
Proof.
  intros HN HH HE. rewrite elements_output_is_fee_sem in HE. apply some_inj in HE.
  apply (proj1 (fee_results_agree_iff _ _) HE).
  unfold fee_collision_at. rewrite fee_witness_index_nat.
  unfold fee_witness_env, fee_witness_tx. cbn [Elements.envTx sigTxOut nth_error].
  unfold fee_digest_collision, fee_witness_output.
  cbn [txoAsset txoAmount txoScript clearPrf encode_asset encode_amount fee_explicit].
  split; [reflexivity|]. split; [reflexivity|]. split; [exact HN|exact HH].
Qed.

(** The C result agrees with the canonical program's on every input iff the
    open SHA-256 property holds. *)
Theorem fee_results_agree_everywhere_iff :
  (forall a environment, Some (processed_fee_result a environment) =
     @elements_output_is_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment) <->
  empty_script_digest_unique.
Proof.
  split.
  - intros HAll s Hs HH. destruct s as [|b s]; [reflexivity|exfalso].
    exact (fee_witness_differs (b :: s) Hs ltac:(discriminate) HH (HAll _ _)).
  - intros HU a environment. rewrite elements_output_is_fee_sem. f_equal.
    apply fee_results_agree_iff. unfold fee_collision_at.
    destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [o | ]; [|tauto].
    intros (_ & _ & HN & HH). apply HN. apply HU; [apply txoScript_bound|exact HH].
Qed.

(** * Jet-level statements *)

(** The complete original C call computes [processed_fee_result]; that result
    agrees with the canonical program exactly off [fee_collision_at]. *)
Theorem elements_output_is_fee_canonical_comparison :
  application_jet_local_spec_sep f_simplicity_output_is_fee elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Ty.Unit))
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e)) processed_fee_rep 248 0 8 704)
    (fun a environment => Some (processed_fee_result a environment)) /\
  (forall a environment,
    Some (processed_fee_result a environment) =
      @elements_output_is_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment <->
    ~ fee_collision_at a environment).
Proof.
  split; [exact elements_output_fee_flag_contract|].
  intros a environment. rewrite elements_output_is_fee_sem, <- fee_results_agree_iff.
  split; [apply some_inj|intros ->; reflexivity].
Qed.

(** Equivalence with the canonical specification, conditional on the open
    SHA-256 property (not proved, not assumed as an axiom). *)
Theorem elements_output_is_fee_local_spec_if_digest_unique :
  empty_script_digest_unique ->
  application_jet_local_spec_sep f_simplicity_output_is_fee elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Ty.Unit))
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e)) processed_fee_rep 248 0 8 704)
    (fun a environment => @elements_output_is_fee_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intro HU. eapply application_jet_local_spec_sep_pointwise;
    [|exact elements_output_fee_flag_contract].
  exact (proj2 fee_results_agree_everywhere_iff HU).
Qed.
