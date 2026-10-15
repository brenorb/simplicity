(** Actual Elements issuance_asset_amount jet against the literal canonical
    primitive IssuanceAssetAmount: the issuance type tag selects the amount
    helper on [issuance->assetAmt] or padding. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_elements C.jet_elements_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_elements_version_exec C.jet_elements_field_eval C.jet_elements_wrapper C.jet_elements_effects.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_index_eval.
Require Import C.jet_elements_indexed_exec C.jet_elements_indexed_ptr_then C.jet_elements_indexed_scalar.
Require Import C.jet_elements_hash_write C.jet_elements_hash_helpers C.jet_elements_indexed_ptr.
Require Import C.jet_elements_script_cmr_local C.jet_elements_indexed_scalar_jets.
Require Import C.jet_elements_indexed_ptr_jets C.jet_elements_input_hash_jets C.jet_elements_asset_helper.
Require Import C.jet_elements_asset_jets C.jet_elements_amt_helper C.jet_elements_indexed_gen C.jet_elements_indexed_ptr2.
Require Import C.jet_elements_amount_jets C.jet_elements_issuance_helper C.jet_elements_issuance_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.


Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).



(** [issuanceAmount = either newIssuanceAmount reissuanceAmount]. *)
Definition issuance_amount (i : issuance) : amountWith (list byte) :=
  match i with inl new => newIssuanceAmount new | inr re => reissuanceAmount re end.

Definition assetamt_pexpr : expr :=
  Eaddrof (Efield
    (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr))
    _assetAmt (Tstruct _confAmount noattr)) (tptr (Tstruct _confAmount noattr)).

Definition issuance_amount_rep (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  Mem.load Mint32 m b (ofs + 272) = Some (Vint (issuance_tag (sigTxiIssuance txi))) /\
  forall i, sigTxiIssuance txi = Some i -> amount_rep m b (ofs + 232) (clearPrf (issuance_amount i)).

Definition issuance_amount_pcells (txi : sigTxInput) : list Cell :=
  issuance_tagged_cells (opt_is_some (sigTxiIssuance txi)) 258
    (match sigTxiIssuance txi with Some i => amount_pcells (clearPrf (issuance_amount i)) | None => [] end).

Lemma issuance_amount_pcells_length txi : Z.of_nat (length (issuance_amount_pcells txi)) = 259.
Proof.
  unfold issuance_amount_pcells, issuance_tagged_cells. destruct (sigTxiIssuance txi) as [i|]; cbn [opt_is_some].
  - cbn [app length]. rewrite Nat2Z.inj_succ, amount_pcells_length. reflexivity.
  - reflexivity.
Qed.

Definition issuance_amount_result (elems : list sigTxInput) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))) :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | Some txi => inr (match sigTxiIssuance txi with
                     | Some i => inr (encode_amount (clearPrf (issuance_amount i)))
                     | None => inl tt
                     end)
  | None => inl tt
  end.

Definition elements_issuance_asset_amount_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))) :=
  Primitive.Combinators.prim Elements.IssuanceAssetAmount.

Lemma elements_issuance_asset_amount_sem a environment :
  @elements_issuance_asset_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_amount_result (sigTxIn (Elements.envTx environment)) a).
Proof.
  assert (H : @elements_issuance_asset_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.IssuanceAssetAmount a environment) by reflexivity.
  rewrite H. unfold Elements.sem, issuance_amount_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map. destruct (sigTxiIssuance txi) as [[new|re]|]; [| |reflexivity].
  - unfold issuance_amount. destruct (newIssuanceAmount new) as [v|[odd x] p]; reflexivity.
  - unfold issuance_amount. destruct (reissuanceAmount re) as [v|[odd x] p]; reflexivity.
Qed.

Lemma encode_inr_inr_conf64 (c : Ty.tySem (ConfTy Word64)) :
  @encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))) (inr (inr c)) =
    Some true :: Some true :: @encode (ConfTy Word64) c.
Proof. reflexivity. Qed.

Lemma elements_issuance_asset_amount_shape :
  elements_wrapper_shape f_simplicity_issuance_asset_amount
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput issuance_pexpr _issuanceAssetAmt
        (Tstruct _assetIssuance noattr)) (elements_skip_stmt 259)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Lemma issuance_tag_present o : negb (Int.eq (Int.repr 0) (issuance_tag o)) = opt_is_some o.
Proof. destruct o as [[new|re]|]; reflexivity. Qed.

Theorem elements_issuance_asset_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_asset_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_amount_rep 544 256 0 696)
    (fun a environment => @elements_issuance_asset_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxIn (Elements.envTx e)) 259
    issuance_amount_pcells issuance_amount_rep (Ty.Sum Ty.Unit (ConfTy Word64))
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _issuanceAssetAmt (Tstruct _assetIssuance noattr)
    696 0 544 256 280 issuance_pexpr
    (issuance_tagged_fun One (Int.repr 0) assetamt_pexpr _amt (Tstruct _confAmount noattr) 258)
    f_simplicity_issuance_asset_amount
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) issuance_amount_pcells_length ltac:(reflexivity) ltac:(intros bl; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_issuance_asset_amount_shape ltac:(reflexivity) _ _).
  - intros m1 m2 b ofs x [Ht Hh] Hl. split.
    + apply (Hl Mint32 (ofs + 272) _); [lia|change (size_chunk Mint32) with 4; lia|exact Ht].
    + intros i Hi. eapply amount_rep_mono; [exact (Hh i Hi)|].
      intros chunk o v H1 H2. apply Hl; lia.
  - intros bd dbase bw outedge m' bin ofs x cur [Ht Hh] H0 HM HSep HF.
    pose proof HF as [_ [_ [_ [HCur _]]]].
    unfold issuance_amount_pcells. rewrite <- (issuance_tag_present (sigTxiIssuance x)).
    refine (eval_elements_issuance_tagged One (Int.repr 0) assetamt_pexpr _amt (Tstruct _confAmount noattr) f_amt
      258 (fun t => negb (Int.eq (Int.repr 0) t)) _ m' bin ofs bd dbase bw outedge cur
      (issuance_tag (sigTxiIssuance x)) (ofs + 232)
      (fun t mm => elements_ne_cmp (Int.repr 0) t mm) ltac:(reflexivity) elements_amt_symbol elements_amt_funct
      ltac:(reflexivity) ltac:(lia) H0 HM HSep Ht HF
      (fun e le mm HI => eval_elements_issuance_field_addr e le mm _assetAmt 232 _confAmount bin ofs
        elements_assetIssuance_assetAmt H0 ltac:(lia) ltac:(lia) HI) _).
    intros Hb mb HLoadB HFb.
    rewrite (issuance_tag_present (sigTxiIssuance x)) in Hb.
    destruct (sigTxiIssuance x) as [i|] eqn:Hiss; [|discriminate Hb].
    assert (HRb : amount_rep mb bin (ofs + 232) (clearPrf (issuance_amount i))).
    { eapply amount_rep_mono; [exact (Hh i eq_refl)|].
      intros chunk o v H1 H2 Hl. rewrite HLoadB by lia. exact Hl. }
    assert (HSepA : out_sep bd dbase bw outedge (cur - 1) 258 bin (ofs + 232) (ofs + 232 + 40)).
    { eapply out_sep_range with (lo := ofs) (hi := ofs + 280); [|lia|lia].
      eapply out_sep_sub with (cursor := cur) (count := 1 + 258); [lia|lia|lia|lia|exact HSep]. }
    exact (amount_rep_runs bd dbase bw outedge mb bin (ofs + 232) _ (cur - 1) HRb ltac:(lia) ltac:(lia) HSepA HFb).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. exact (eval_issuance_pexpr e le' m' bin inbase r H4 HI Hi0 HM).
  - intros a environment. exists (issuance_amount_result (sigTxIn (Elements.envTx environment)) a).
    split; [apply elements_issuance_asset_amount_sem|].
    unfold issuance_amount_result, indexed_ptr_cells. unfold toZ32.
    destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|].
    + unfold issuance_amount_pcells, issuance_tagged_cells.
      destruct (sigTxiIssuance txi) as [i|]; cbn [opt_is_some].
      * rewrite encode_inr_inr_conf64, encode_amount_cells. reflexivity.
      * reflexivity.
    + vm_compute. reflexivity.
Qed.
