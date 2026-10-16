(** Original C issuance token-amount jets, reusing the checked complete static helper. *)
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
Set Default Timeout 10.


Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).



Require Import C.jet_elements_current_input_jets C.jet_elements_current_spec C.jet_elements_current_ptr C.jet_elements_current_ptr_jets.
Require Import C.jet_elements_token_select C.jet_elements_token_amount_exec.

Definition issuance_token_rep m b ofs (txi : sigTxInput) := token_issuance_rep m b ofs (sigTxiIssuance txi).
Definition issuance_token_pcells (txi : sigTxInput) := token_issuance_cells (sigTxiIssuance txi).
Definition issuance_token_value (txi : sigTxInput) : tySem (Ty.Sum Ty.Unit (ConfTy Word64)) :=
  match sigTxiIssuance txi with Some i => inr (encode_amount (token_selected_amount i)) | None => inl tt end.
Definition issuance_token_result (values : list sigTxInput) (a : tySem Word32) :
    tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))) :=
  match nth_error values (Z.to_nat (toZ a)) with Some txi => inr (issuance_token_value txi) | None => inl tt end.
Definition elements_issuance_token_amount_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))) :=
  Primitive.Combinators.prim Elements.IssuanceTokenAmount.

Lemma issuance_token_pcells_length txi : Z.of_nat (length (issuance_token_pcells txi)) = 259.
Proof.
  unfold issuance_token_pcells, token_issuance_cells, token_issuance_tail.
  destruct (sigTxiIssuance txi) as [i|]; cbn [opt_is_some app length]; [|reflexivity].
  rewrite Nat2Z.inj_succ, amount_pcells_length. reflexivity.
Qed.

Lemma encode_issuance_token_cells txi :
  @encode (Ty.Sum Ty.Unit (ConfTy Word64)) (issuance_token_value txi) = issuance_token_pcells txi.
Proof.
  unfold issuance_token_value, issuance_token_pcells, token_issuance_cells, token_issuance_tail.
  destruct (sigTxiIssuance txi) as [i|]; cbn [opt_is_some app]; [|reflexivity].
  change (Some true :: @encode (ConfTy Word64) (encode_amount (token_selected_amount i)) =
    Some true :: amount_pcells (token_selected_amount i)).
  rewrite encode_amount_cells. reflexivity.
Qed.

Lemma elements_issuance_token_amount_sem a environment :
  @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_token_result (sigTxIn (Elements.envTx environment)) a).
Proof.
  change (Elements.sem Elements.IssuanceTokenAmount a environment =
    Some (issuance_token_result (sigTxIn (Elements.envTx environment)) a)).
  unfold Elements.sem, issuance_token_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold issuance_token_value, Datatypes.option_map.
  destruct (sigTxiIssuance txi) as [[new|re]|]; [|reflexivity|reflexivity].
  unfold token_selected_amount. destruct (newIssuanceTokenAmount new) as [v|[odd x] p]; reflexivity.
Qed.

Lemma issuance_token_rep_pres : forall m1 m2 b ofs x, issuance_token_rep m1 b ofs x ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 280 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> issuance_token_rep m2 b ofs x.
Proof. intros; eapply token_issuance_rep_pres; eauto. Qed.

Lemma issuance_token_rep_runs : forall bd dbase bw outedge m bin ofs x cur,
  issuance_token_rep m bin ofs x -> 0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned ->
  out_sep bd dbase bw outedge cur 259 bin ofs (ofs + 280) ->
  write_frame_at m bd dbase bw outedge cur 259 ->
  exists me, Clight2.eval_funcall elements_ge m (Internal f_issuanceTokenAmt)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
    write_effect m me bd dbase bw outedge cur 259 (issuance_token_pcells x).
Proof. intros; eapply eval_elements_issuanceTokenAmt; eauto. Qed.

Lemma elements_issuance_token_amount_shape :
  elements_wrapper_shape f_simplicity_issuance_token_amount
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput issuance_pexpr _issuanceTokenAmt
        (Tstruct _assetIssuance noattr)) (elements_skip_stmt 259)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_issuance_token_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_token_rep 544 256 0 696)
    (fun a environment => @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxIn (Elements.envTx e)) 259
    issuance_token_pcells issuance_token_rep (Ty.Sum Ty.Unit (ConfTy Word64))
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _issuanceTokenAmt (Tstruct _assetIssuance noattr)
    696 0 544 256 280 issuance_pexpr f_issuanceTokenAmt f_simplicity_issuance_token_amount
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) issuance_token_pcells_length ltac:(reflexivity) ltac:(intros bl; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    issuance_token_rep_pres issuance_token_rep_runs _ elements_issuance_token_amount_shape ltac:(reflexivity) _ _).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. exact (eval_issuance_pexpr e le' m' bin inbase r H4 HI Hi0 HM).
  - intros a environment. exists (issuance_token_result (sigTxIn (Elements.envTx environment)) a).
    split; [apply elements_issuance_token_amount_sem|]. unfold issuance_token_result, indexed_ptr_cells, toZ32.
    destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|].
    + rewrite <- encode_issuance_token_cells. reflexivity.
    + reflexivity.
Qed.

Definition elements_current_issuance_token_amount_spec {alg : Primitive.Algebra} :
    alg Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)) := elements_current_spec (@elements_issuance_token_amount_spec alg).

Lemma elements_current_issuance_token_amount_shape :
  elements_wrapper_shape f_simplicity_current_issuance_token_amount
    (elements_current_ptr_rest _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput
      elements_current_issuance_asset_amount_pexpr _issuanceTokenAmt (Tstruct _assetIssuance noattr)).
Proof. repeat split; try reflexivity. apply elements_current_ptr_disjoint. Qed.

Theorem elements_current_issuance_token_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_current_issuance_token_amount elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit (ConfTy Word64))
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx issuance_token_rep 544 256 0 696)
    (fun a environment => @elements_current_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_current_input_ptr 259 issuance_token_pcells issuance_token_rep (Ty.Sum Ty.Unit (ConfTy Word64))
    _issuanceTokenAmt (Tstruct _assetIssuance noattr) 256 280 elements_current_issuance_asset_amount_pexpr
    f_issuanceTokenAmt f_simplicity_current_issuance_token_amount
    ltac:(split; lia) ltac:(reflexivity) ltac:(intros bl; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(reflexivity) ltac:(split; lia)
    issuance_token_rep_pres issuance_token_rep_runs _ elements_current_issuance_token_amount_shape ltac:(reflexivity)
    (fun a e => @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a e)
    issuance_token_value (fun a e => elements_issuance_token_amount_sem a e)
    encode_issuance_token_cells issuance_token_pcells_length).
  intros e le' m' bin inbase ixv H2 H3 Hi0 HM. unfold elements_current_issuance_asset_amount_pexpr.
  exact (eval_elements_elem_field_addr e le' m' _t'2 _t'3 _sigInput 544 _issuance 256 _assetIssuance bin inbase ixv
    elements_sizeof_sigInput elements_sigInput_issuance H2 H3 Hi0 ltac:(split; lia) ltac:(lia)
    ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
Qed.
