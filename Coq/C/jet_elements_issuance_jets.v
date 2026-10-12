(** Actual Elements reissuance_blinding, new_issuance_contract and
    reissuance_entropy jets against the literal canonical primitives.  The
    element relation states the issuance type tag (NO_ISSUANCE = 0,
    NEW_ISSUANCE = 1, REISSUANCE = 2) and, only when the primitive yields a
    hash, the words of that hash in the corresponding C field. *)
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
Require Import C.jet_elements_amount_jets C.jet_elements_issuance_helper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.


Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).


Definition _anon_union2 : ident := 19015305760020270911%positive.

Lemma elements_assetIssuance_union : elements_field_at _assetIssuance _anon_union 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_assetIssuance_entropy : elements_field_at _assetIssuance _entropy 72.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_assetIssuance_assetAmt : elements_field_at _assetIssuance _assetAmt 232.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuance_union_new : elements_union_field_at __4839 _anon_union 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuance_union_re : elements_union_field_at __4839 _anon_union2 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuance_contractHash : elements_field_at __4840 _contractHash 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_issuance_blindingNonce : elements_field_at __4841 _blindingNonce 0.
Proof. vm_compute; reflexivity. Qed.

Lemma ptrofs_add0 p : Ptrofs.add p (Ptrofs.repr 0) = p.
Proof. change (Ptrofs.repr 0) with Ptrofs.zero. apply Ptrofs.add_zero. Qed.

(** [issuance->UNION.MEMBER.FIELD], all at offset zero. *)
Lemma eval_elements_issuance_union_hash e le m' member msid field bi ibase :
  elements_union_field_at __4839 member 0 -> elements_field_at msid field 0 ->
  le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
  eval_expr elements_ge e le m'
    (Eaddrof (Efield (Efield (Efield
      (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr))
      _anon_union (Tunion __4839 noattr)) member (Tstruct msid noattr)) field
      (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)))
    (Vptr bi (Ptrofs.repr ibase)).
Proof.
  intros HU HFd HI. eapply eval_Eaddrof.
  rewrite <- (ptrofs_add0 (Ptrofs.repr ibase)).
  eapply eval_elements_field_lvalue; [reflexivity|exact HFd|].
  rewrite <- (ptrofs_add0 (Ptrofs.repr ibase)).
  eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
  eapply eval_elements_union_field_lvalue; [reflexivity|exact HU|].
  rewrite <- (ptrofs_add0 (Ptrofs.repr ibase)).
  eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
  eapply eval_elements_field_lvalue; [reflexivity|exact elements_assetIssuance_union|].
  apply eval_elements_deref_struct. exact HI.
Qed.

(** [&issuance->FIELD] for a struct-valued field of the issuance. *)
Lemma eval_elements_issuance_field_addr e le m' field delta sid1 bi ibase :
  elements_field_at _assetIssuance field delta -> 0 <= ibase -> 0 <= delta ->
  ibase + delta <= Ptrofs.max_unsigned ->
  le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
  eval_expr elements_ge e le m'
    (Eaddrof (Efield
      (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr))
      field (Tstruct sid1 noattr)) (tptr (Tstruct sid1 noattr)))
    (Vptr bi (Ptrofs.repr (ibase + delta))).
Proof.
  intros HFd H0 Hd HM HI. eapply eval_Eaddrof.
  rewrite <- (elements_ptr_add_repr ibase delta) by lia.
  eapply eval_elements_field_lvalue; [reflexivity|exact HFd|].
  apply eval_elements_deref_struct. exact HI.
Qed.

(** NO_ISSUANCE = 0, NEW_ISSUANCE = 1, REISSUANCE = 2. *)
Definition issuance_tag (o : option issuance) : int :=
  match o with None => Int.repr 0 | Some (inl _) => Int.repr 1 | Some (inr _) => Int.repr 2 end.

Definition opt_is_some {A} (o : option A) : bool := match o with Some _ => true | None => false end.

Definition issuance_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _issuance
    (Tstruct _assetIssuance noattr)) (tptr (Tstruct _assetIssuance noattr)).

Lemma eval_issuance_pexpr e le' m' bin inbase r :
  le'!_t'4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
  0 <= inbase -> inbase + 544 * Int64.unsigned r + 256 + 280 <= Ptrofs.max_unsigned ->
  eval_expr elements_ge e le' m' issuance_pexpr (Vptr bin (Ptrofs.repr (inbase + 544 * Int64.unsigned r + 256))).
Proof.
  intros H4 HI Hi0 HM. unfold issuance_pexpr.
  exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigInput 544 _issuance 256 _assetIssuance bin inbase r
    elements_sizeof_sigInput elements_sigInput_issuance H4 HI Hi0 ltac:(split; lia) ltac:(lia)
    ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
Qed.

(** * The three optional issuance hashes *)

Definition issuance_hash_rep (delta : Z) (gh : option issuance -> option hash256)
    (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  Mem.load Mint32 m b (ofs + 272) = Some (Vint (issuance_tag (sigTxiIssuance txi))) /\
  forall h, gh (sigTxiIssuance txi) = Some h -> uint32_array_at m b (ofs + delta) (hash256_reg h).

Definition issuance_hash_pcells (gh : option issuance -> option hash256) (txi : sigTxInput) : list Cell :=
  issuance_tagged_cells (opt_is_some (gh (sigTxiIssuance txi))) 256
    (match gh (sigTxiIssuance txi) with Some h => hash_cells (hash256_reg h) | None => [] end).

Definition issuance_hash_result (gh : option issuance -> option hash256) (elems : list sigTxInput)
    (a : Ty.tySem Word32) : Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | Some txi => inr (match gh (sigTxiIssuance txi) with Some h => inr (from_hash256 h) | None => inl tt end)
  | None => inl tt
  end.

Lemma encode_inr_inr_hash (w : Ty.tySem Word256) :
  @encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) (inr (inr w)) = Some true :: Some true :: @encode Word256 w.
Proof. reflexivity. Qed.

Lemma issuance_hash_pcells_length gh txi : Z.of_nat (length (issuance_hash_pcells gh txi)) = 257.
Proof.
  unfold issuance_hash_pcells, issuance_tagged_cells. destruct (gh (sigTxiIssuance txi)) as [h|]; cbn [opt_is_some].
  - cbn [app length]. rewrite Nat2Z.inj_succ, (hash_cells_length_Z _ (hash256_len h)). reflexivity.
  - reflexivity.
Qed.

Theorem elements_issuance_hash_local (K : int) (delta : Z) (gh : option issuance -> option hash256)
    (pexpr_h : expr) (jid : ident) (f : function)
    (Hg : forall o, Int.eq K (issuance_tag o) = opt_is_some (gh o))
    (Hd : 0 <= delta /\ delta + 32 <= 280)
    (Hpty : typeof pexpr_h = tptr (Tstruct _sha256_midstate noattr))
    (Hpexpr : forall e le m' bi ibase, le!_issuance = Some (Vptr bi (Ptrofs.repr ibase)) ->
      0 <= ibase -> ibase + 280 <= Ptrofs.max_unsigned ->
      eval_expr elements_ge e le m' pexpr_h (Vptr bi (Ptrofs.repr (ibase + delta))))
    (Hnone : forall bl, (elements_version_locals bl)!jid = None)
    (Hsym : Genv.find_symbol (Clight.genv_genv elements_ge) jid = Some (elements_symbol_block jid))
    (Hfun : Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block jid) Ptrofs.zero) =
      Some (Internal (issuance_tagged_fun Oeq K pexpr_h _writeHash (Tstruct _sha256_midstate noattr) 256)))
    (Hshape : elements_wrapper_shape f
      (elements_indexed_rest _t'5 _t'6 _numInputs
        (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput issuance_pexpr jid (Tstruct _assetIssuance noattr))
        (elements_skip_stmt 257)))
    (spec : Ty.tySem Word32 -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))))
    (Hspec : forall a environment,
      spec a environment = Some (issuance_hash_result gh (sigTxIn (Elements.envTx environment)) a)) :
  application_jet_local_spec_sep f elements_ge Elements.env Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) (issuance_hash_rep delta gh) 544 256 0 696) spec.
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxIn (Elements.envTx e)) 257
    (issuance_hash_pcells gh) (issuance_hash_rep delta gh) (Ty.Sum Ty.Unit Word256)
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput jid (Tstruct _assetIssuance noattr)
    696 0 544 256 280 issuance_pexpr
    (issuance_tagged_fun Oeq K pexpr_h _writeHash (Tstruct _sha256_midstate noattr) 256) f
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) (issuance_hash_pcells_length gh) ltac:(reflexivity) Hnone
    Hsym Hfun ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ Hshape ltac:(reflexivity) spec _).
  - intros m1 m2 b ofs x [Ht Hh] Hl. split.
    + apply (Hl Mint32 (ofs + 272) _); [lia|change (size_chunk Mint32) with 4; lia|exact Ht].
    + intros h Hgh. eapply uint32_array_at_mono; [exact (hash256_len h)|exact (Hh h Hgh)|].
      intros chunk o v H1 H2. apply Hl; lia.
  - intros bd dbase bw outedge m' bin ofs x cur [Ht Hh] H0 HM HSep HF.
    pose proof HF as [_ [_ [_ [HCur _]]]].
    unfold issuance_hash_pcells. rewrite <- (Hg (sigTxiIssuance x)).
    refine (eval_elements_issuance_tagged Oeq K pexpr_h _writeHash (Tstruct _sha256_midstate noattr) f_writeHash
      256 (Int.eq K) _ m' bin ofs bd dbase bw outedge cur (issuance_tag (sigTxiIssuance x)) (ofs + delta)
      (fun t mm => elements_eq_cmp K t mm) Hpty elements_writeHash_symbol elements_writeHash_funct
      ltac:(reflexivity) ltac:(lia) H0 HM HSep Ht HF
      (fun e le mm HI => Hpexpr e le mm bin ofs HI H0 HM) _).
    intros Hb mb HLoadB HFb.
    rewrite (Hg (sigTxiIssuance x)) in Hb.
    destruct (gh (sigTxiIssuance x)) as [h|] eqn:Hgh; [|discriminate Hb].
    assert (HAb : uint32_array_at mb bin (ofs + delta) (hash256_reg h)).
    { intros i w Hi.
      assert (Hi8 : (i < 8)%nat) by (rewrite <- (hash256_len h); apply nth_error_Some; rewrite Hi; discriminate).
      rewrite HLoadB by (try change (size_chunk Mint32) with 4; lia). exact (Hh h eq_refl i w Hi). }
    assert (HSepH : out_sep bd dbase bw outedge (cur - 1) 256 bin (ofs + delta) (ofs + delta + 32)).
    { eapply out_sep_range with (lo := ofs) (hi := ofs + 280); [|lia|lia].
      eapply out_sep_sub with (cursor := cur) (count := 1 + 256); [lia|lia|lia|lia|exact HSep]. }
    exact (eval_elements_writeHash_layout mb bin (ofs + delta) bd dbase bw outedge (cur - 1) (hash256_reg h)
      (hash256_len h) ltac:(lia) ltac:(lia) HSepH HAb HFb).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. exact (eval_issuance_pexpr e le' m' bin inbase r H4 HI Hi0 HM).
  - intros a environment. exists (issuance_hash_result gh (sigTxIn (Elements.envTx environment)) a).
    split; [apply Hspec|].
    unfold issuance_hash_result, indexed_ptr_cells. unfold toZ32.
    destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|].
    + unfold issuance_hash_pcells, issuance_tagged_cells.
      destruct (gh (sigTxiIssuance txi)) as [h|]; cbn [opt_is_some].
      * rewrite encode_inr_inr_hash, encode_from_hash256. reflexivity.
      * reflexivity.
    + vm_compute. reflexivity.
Qed.

Lemma elements_issuance_jet_shape_disjoint :
  list_disjoint [_dst; _src; _env] [_i; _t'2; _t'1; _t'6; _t'5; _t'4; _t'3].
Proof. exact elements_ptr_disjoint. Qed.

(** ** reissuance_blinding *)

Definition gh_blinding (o : option issuance) : option hash256 :=
  match o with Some (inr re) => Some (reissuanceBlindingNonce re) | _ => None end.

Definition blinding_pexpr : expr :=
  Eaddrof (Efield (Efield (Efield
    (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr))
    _anon_union (Tunion __4839 noattr)) _anon_union2 (Tstruct __4841 noattr)) _blindingNonce
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Definition elements_reissuance_blinding_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  Primitive.Combinators.prim Elements.ReissuanceBlinding.

Lemma elements_reissuance_blinding_sem a environment :
  @elements_reissuance_blinding_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_hash_result gh_blinding (sigTxIn (Elements.envTx environment)) a).
Proof.
  assert (H : @elements_reissuance_blinding_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.ReissuanceBlinding a environment) by reflexivity.
  rewrite H. unfold Elements.sem, issuance_hash_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map, gh_blinding. destruct (sigTxiIssuance txi) as [[new|re]|]; reflexivity.
Qed.

Lemma elements_reissuance_blinding_shape :
  elements_wrapper_shape f_simplicity_reissuance_blinding
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput issuance_pexpr _reissuanceBlinding
        (Tstruct _assetIssuance noattr)) (elements_skip_stmt 257)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_reissuance_blinding_local_spec :
  application_jet_local_spec_sep f_simplicity_reissuance_blinding elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) (issuance_hash_rep 0 gh_blinding) 544 256 0 696)
    (fun a environment => @elements_reissuance_blinding_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_issuance_hash_local (Int.repr 2) 0 gh_blinding blinding_pexpr _reissuanceBlinding
    f_simplicity_reissuance_blinding _ ltac:(split; lia) ltac:(reflexivity) _ ltac:(intros bl; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) elements_reissuance_blinding_shape _
    elements_reissuance_blinding_sem).
  - intros [[new|re]|]; reflexivity.
  - intros e le m' bi ibase HI H0 HM. rewrite Z.add_0_r.
    exact (eval_elements_issuance_union_hash e le m' _anon_union2 __4841 _blindingNonce bi ibase
      elements_issuance_union_re elements_issuance_blindingNonce HI).
Qed.

(** ** new_issuance_contract *)

Definition gh_contract (o : option issuance) : option hash256 :=
  match o with Some (inl new) => Some (newIssuanceContractHash new) | _ => None end.

Definition contract_pexpr : expr :=
  Eaddrof (Efield (Efield (Efield
    (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr))
    _anon_union (Tunion __4839 noattr)) _anon_union (Tstruct __4840 noattr)) _contractHash
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Definition elements_new_issuance_contract_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  Primitive.Combinators.prim Elements.NewIssuanceContract.

Lemma elements_new_issuance_contract_sem a environment :
  @elements_new_issuance_contract_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_hash_result gh_contract (sigTxIn (Elements.envTx environment)) a).
Proof.
  assert (H : @elements_new_issuance_contract_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.NewIssuanceContract a environment) by reflexivity.
  rewrite H. unfold Elements.sem, issuance_hash_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map, gh_contract. destruct (sigTxiIssuance txi) as [[new|re]|]; reflexivity.
Qed.

Lemma elements_new_issuance_contract_shape :
  elements_wrapper_shape f_simplicity_new_issuance_contract
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput issuance_pexpr _newIssuanceContract
        (Tstruct _assetIssuance noattr)) (elements_skip_stmt 257)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_new_issuance_contract_local_spec :
  application_jet_local_spec_sep f_simplicity_new_issuance_contract elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) (issuance_hash_rep 0 gh_contract) 544 256 0 696)
    (fun a environment => @elements_new_issuance_contract_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_issuance_hash_local (Int.repr 1) 0 gh_contract contract_pexpr _newIssuanceContract
    f_simplicity_new_issuance_contract _ ltac:(split; lia) ltac:(reflexivity) _ ltac:(intros bl; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) elements_new_issuance_contract_shape _
    elements_new_issuance_contract_sem).
  - intros [[new|re]|]; reflexivity.
  - intros e le m' bi ibase HI H0 HM. rewrite Z.add_0_r.
    exact (eval_elements_issuance_union_hash e le m' _anon_union __4840 _contractHash bi ibase
      elements_issuance_union_new elements_issuance_contractHash HI).
Qed.

(** ** reissuance_entropy *)

Definition gh_entropy (o : option issuance) : option hash256 :=
  match o with Some (inr re) => Some (reissuanceEntropy re) | _ => None end.

Definition entropy_pexpr : expr :=
  Eaddrof (Efield
    (Ederef (Etempvar _issuance (tptr (Tstruct _assetIssuance noattr))) (Tstruct _assetIssuance noattr))
    _entropy (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Definition elements_reissuance_entropy_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  Primitive.Combinators.prim Elements.ReissuanceEntropy.

Lemma elements_reissuance_entropy_sem a environment :
  @elements_reissuance_entropy_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (issuance_hash_result gh_entropy (sigTxIn (Elements.envTx environment)) a).
Proof.
  assert (H : @elements_reissuance_entropy_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.ReissuanceEntropy a environment) by reflexivity.
  rewrite H. unfold Elements.sem, issuance_hash_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map, gh_entropy. destruct (sigTxiIssuance txi) as [[new|re]|]; reflexivity.
Qed.

Lemma elements_reissuance_entropy_shape :
  elements_wrapper_shape f_simplicity_reissuance_entropy
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput issuance_pexpr _reissuanceEntropy
        (Tstruct _assetIssuance noattr)) (elements_skip_stmt 257)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_reissuance_entropy_local_spec :
  application_jet_local_spec_sep f_simplicity_reissuance_entropy elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) (issuance_hash_rep 72 gh_entropy) 544 256 0 696)
    (fun a environment => @elements_reissuance_entropy_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_issuance_hash_local (Int.repr 2) 72 gh_entropy entropy_pexpr _reissuanceEntropy
    f_simplicity_reissuance_entropy _ ltac:(split; lia) ltac:(reflexivity) _ ltac:(intros bl; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) elements_reissuance_entropy_shape _
    elements_reissuance_entropy_sem).
  - intros [[new|re]|]; reflexivity.
  - intros e le m' bi ibase HI H0 HM.
    exact (eval_elements_issuance_field_addr e le m' _entropy 72 _sha256_midstate bi ibase
      elements_assetIssuance_entropy H0 ltac:(lia) ltac:(lia) HI).
Qed.
