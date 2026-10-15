(** Actual Elements input_asset and output_asset jets against the literal
    canonical primitives InputAsset / OutputAsset.  The element relation
    states that the C [confidential] holds the prefix tag (EXPLICIT = 1,
    EVEN_Y = 2, ODD_Y = 3) and the hash words of the logical asset: an initial
    representation requirement on the environment. *)
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
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).

Lemma elements_utxo_asset : elements_field_at _utxo _asset 32.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_sigOutput_asset : elements_field_at _sigOutput _asset 0.
Proof. vm_compute; reflexivity. Qed.

(** The C prefix tag and data words of a logical confidential value. *)
Definition conf_prefix {A : Set} (c : confidential unit A) : int :=
  match c with
  | Explicit _ => Int.repr 1
  | Confidential (Point odd _) _ => if odd then Int.repr 3 else Int.repr 2
  end.

Definition asset_words (a : assetWith unit) : list int :=
  hash256_reg (match a with Explicit h => h | Confidential (Point _ x) _ => x end).

Lemma asset_words_length a : length (asset_words a) = 8%nat.
Proof. unfold asset_words. exact (hash256_len _). Qed.

Definition asset_rep (m : mem) (b : block) (ofs : Z) (a : assetWith unit) : Prop :=
  uint32_array_at m b ofs (asset_words a) /\
  Mem.load Mint32 m b (ofs + 32) = Some (Vint (conf_prefix a)).

Definition conf_toBit (b : bool) : Ty.tySem (Ty.Sum Ty.Unit Ty.Unit) := if b then inr tt else inl tt.

(** [encodeAsset] of the canonical primitive semantics. *)
Definition encode_asset (a : assetWith unit) : Ty.tySem (ConfTy Word256) :=
  match a with
  | Explicit h => inr (from_hash256 h)
  | Confidential (Point odd x) _ => inl (conf_toBit odd, from_hash256 x)
  end.

Lemma encode_conf_inr (w : Ty.tySem Word256) :
  @encode (Ty.Sum Ty.Unit (ConfTy Word256)) (inr (inr w)) =
    Some true :: Some true :: None :: @encode Word256 w.
Proof. reflexivity. Qed.

Lemma encode_conf_inl (b : bool) (w : Ty.tySem Word256) :
  @encode (Ty.Sum Ty.Unit (ConfTy Word256)) (inr (inl (conf_toBit b, w))) =
    Some true :: Some false :: Some b :: @encode Word256 w.
Proof. destruct b; reflexivity. Qed.

Lemma asset_cells_explicit xs : asset_cells (Int.repr 1) xs = Some true :: None :: hash_cells xs.
Proof. reflexivity. Qed.
Lemma asset_cells_odd xs : asset_cells (Int.repr 3) xs = Some false :: Some true :: hash_cells xs.
Proof. reflexivity. Qed.
Lemma asset_cells_even xs : asset_cells (Int.repr 2) xs = Some false :: Some false :: hash_cells xs.
Proof. reflexivity. Qed.

Lemma encode_asset_cells (a : assetWith unit) :
  @encode (Ty.Sum Ty.Unit (ConfTy Word256)) (inr (encode_asset a)) =
    Some true :: asset_cells (conf_prefix a) (asset_words a).
Proof.
  destruct a as [h|[odd x] p]; unfold encode_asset, conf_prefix, asset_words.
  - rewrite encode_conf_inr, asset_cells_explicit, encode_from_hash256. reflexivity.
  - rewrite encode_conf_inl, encode_from_hash256.
    destruct odd; [rewrite asset_cells_odd|rewrite asset_cells_even]; reflexivity.
Qed.

Lemma encode_conf_cells (a : assetWith unit) :
  @encode (ConfTy Word256) (encode_asset a) = asset_cells (conf_prefix a) (asset_words a).
Proof.
  pose proof (encode_asset_cells a) as H.
  change (@encode (Ty.Sum Ty.Unit (ConfTy Word256)) (inr (encode_asset a))) with
    (Some true :: @encode (ConfTy Word256) (encode_asset a)) in H.
  congruence.
Qed.

Definition asset_pcells (a : assetWith unit) : list Cell := asset_cells (conf_prefix a) (asset_words a).

Lemma asset_rep_mono m1 m2 b ofs a : asset_rep m1 b ofs a ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 36 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> asset_rep m2 b ofs a.
Proof.
  intros [Hr Hp] Hl. split.
  - eapply uint32_array_at_mono; [apply asset_words_length|exact Hr|].
    intros chunk o v H1 H2. apply Hl; [exact H1|lia].
  - apply (Hl Mint32 (ofs + 32) _); [lia|change (size_chunk Mint32) with 4; lia|exact Hp].
Qed.

Lemma asset_rep_runs bd dbase bw outedge m' bin ofs a cur :
  asset_rep m' bin ofs a -> 0 <= ofs -> ofs + 36 <= Ptrofs.max_unsigned ->
  out_sep bd dbase bw outedge cur 258 bin ofs (ofs + 36) ->
  write_frame_at m' bd dbase bw outedge cur 258 ->
  exists me, Clight2.eval_funcall elements_ge m' (Internal f_asset)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
    write_effect m' me bd dbase bw outedge cur 258 (asset_pcells a).
Proof.
  intros [Hr Hp] H0 HM HSep HF.
  exact (eval_elements_asset_layout m' bin ofs bd dbase bw outedge cur (asset_words a) (conf_prefix a)
    (asset_words_length a) H0 HM HSep Hr Hp HF).
Qed.

(** * input_asset *)

Definition elements_input_asset_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit (ConfTy Word256)) :=
  Primitive.Combinators.prim Elements.InputAsset.

Definition elements_input_asset_result (environment : Elements.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (ConfTy Word256)) :=
  match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txi => inr (encode_asset (utxoAsset (sigTxiTxo txi)))
  | None => inl tt
  end.

Lemma elements_input_asset_sem environment a :
  @elements_input_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (elements_input_asset_result environment a).
Proof.
  assert (H : @elements_input_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.InputAsset a environment) by reflexivity.
  rewrite H. unfold Elements.sem, elements_input_asset_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition elements_input_asset_pexpr : expr :=
  Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _txo (Tstruct _utxo noattr))
    _asset (Tstruct _confidential noattr)) (tptr (Tstruct _confidential noattr)).

Lemma elements_input_asset_shape :
  elements_wrapper_shape f_simplicity_input_asset
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput elements_input_asset_pexpr
        _asset (Tstruct _confidential noattr)) (elements_skip_stmt 258)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_input_asset_local_spec :
  application_jet_local_spec_sep f_simplicity_input_asset elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (ConfTy Word256))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi))) 544 168 0 696)
    (fun a environment => @elements_input_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxIn (Elements.envTx e)) 258
    (fun txi => asset_pcells (utxoAsset (sigTxiTxo txi)))
    (fun m b ofs txi => asset_rep m b ofs (utxoAsset (sigTxiTxo txi))) (ConfTy Word256)
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _asset (Tstruct _confidential noattr)
    696 0 544 168 36 elements_input_asset_pexpr f_asset f_simplicity_input_asset
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) _ ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_asset_symbol elements_asset_funct ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_input_asset_shape ltac:(reflexivity) _ _).
  - intros x. apply asset_cells_length_Z. apply asset_words_length.
  - intros m1 m2 b ofs x Hr Hl. exact (asset_rep_mono m1 m2 b ofs _ Hr Hl).
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    exact (asset_rep_runs bd dbase bw outedge m' bin ofs _ cur Hr H0 HM HSep HF).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_input_asset_pexpr.
    pose proof (eval_elements_elem_nested_field_addr e le' m' _t'4 _i _sigInput 544 _txo 136 _utxo
      _asset 32 _confidential bin inbase r elements_sizeof_sigInput elements_sigInput_txo
      elements_utxo_asset H4 HI Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)) as H.
    exact H.
  - intros a environment. exists (elements_input_asset_result environment a). split.
    + apply elements_input_asset_sem.
    + unfold elements_input_asset_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|].
      * apply encode_asset_cells.
      * vm_compute. reflexivity.
Qed.

(** * output_asset *)

Definition elements_output_asset_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit (ConfTy Word256)) :=
  Primitive.Combinators.prim Elements.OutputAsset.

Definition elements_output_asset_result (environment : Elements.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (ConfTy Word256)) :=
  match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txo => inr (encode_asset (clearPrf (txoAsset txo)))
  | None => inl tt
  end.

Lemma elements_output_asset_sem environment a :
  @elements_output_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (elements_output_asset_result environment a).
Proof.
  assert (H : @elements_output_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.OutputAsset a environment) by reflexivity.
  rewrite H. unfold Elements.sem, elements_output_asset_result. cbv zeta.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition elements_output_asset_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _asset
    (Tstruct _confidential noattr)) (tptr (Tstruct _confidential noattr)).

Lemma elements_output_asset_shape :
  elements_wrapper_shape f_simplicity_output_asset
    (elements_indexed_rest _t'5 _t'6 _numOutputs
      (elements_indexed_then_ptr _t'3 _t'4 _output _sigOutput elements_output_asset_pexpr
        _asset (Tstruct _confidential noattr)) (elements_skip_stmt 258)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_output_asset_local_spec :
  application_jet_local_spec_sep f_simplicity_output_asset elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (ConfTy Word256))
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => asset_rep m b ofs (clearPrf (txoAsset txo))) 248 0 8 704)
    (fun a environment => @elements_output_asset_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxOut (Elements.envTx e)) 258
    (fun txo => asset_pcells (clearPrf (txoAsset txo)))
    (fun m b ofs txo => asset_rep m b ofs (clearPrf (txoAsset txo))) (ConfTy Word256)
    _t'5 _t'6 _t'3 _t'4 _numOutputs _output _sigOutput _asset (Tstruct _confidential noattr)
    704 8 248 0 36 elements_output_asset_pexpr f_asset f_simplicity_output_asset
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) _ ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_asset_symbol elements_asset_funct ltac:(reflexivity)
    elements_elementsTransaction_numOutputs elements_elementsTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_output_asset_shape ltac:(reflexivity) _ _).
  - intros x. apply asset_cells_length_Z. apply asset_words_length.
  - intros m1 m2 b ofs x Hr Hl. exact (asset_rep_mono m1 m2 b ofs _ Hr Hl).
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    exact (asset_rep_runs bd dbase bw outedge m' bin ofs _ cur Hr H0 HM HSep HF).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_output_asset_pexpr.
    exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigOutput 248 _asset 0 _confidential bin inbase r
      elements_sizeof_sigOutput elements_sigOutput_asset H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (elements_output_asset_result environment a). split.
    + apply elements_output_asset_sem.
    + unfold elements_output_asset_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|].
      * apply encode_asset_cells.
      * vm_compute. reflexivity.
Qed.

(** * output_nonce *)

Lemma elements_sigOutput_nonce : elements_field_at _sigOutput _nonce 144.
Proof. vm_compute; reflexivity. Qed.

Definition elements_output_nonce_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word256))) :=
  Primitive.Combinators.prim Elements.OutputNonce.

(** A present nonce as a confidential value: [(parity, x)] or an explicit hash. *)
Definition nonce_conf (x : nonce) : assetWith unit :=
  match x with
  | inl (odd, w) => Confidential (Point odd w) tt
  | inr h => Explicit h
  end.

Definition nonce_prefix (n : option nonce) : int :=
  match n with Some x => conf_prefix (nonce_conf x) | None => Int.repr 0 end.

Definition nonce_words (n : option nonce) : list int :=
  match n with Some x => asset_words (nonce_conf x) | None => repeat Int.zero 8 end.

Lemma nonce_words_length n : length (nonce_words n) = 8%nat.
Proof. destruct n; [apply asset_words_length|reflexivity]. Qed.

(** The data words are only required when a nonce is present. *)
Definition nonce_rep (m : mem) (b : block) (ofs : Z) (n : option nonce) : Prop :=
  (n <> None -> uint32_array_at m b ofs (nonce_words n)) /\
  Mem.load Mint32 m b (ofs + 32) = Some (Vint (nonce_prefix n)).

Definition encode_nonce (n : option nonce) : Ty.tySem (Ty.Sum Ty.Unit (ConfTy Word256)) :=
  match n with
  | Some x => inr (encode_asset (nonce_conf x))
  | None => inl tt
  end.

Definition elements_output_nonce_result (environment : Elements.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word256))) :=
  match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txo => inr (encode_nonce (txoNonce txo))
  | None => inl tt
  end.

Lemma elements_output_nonce_sem environment a :
  @elements_output_nonce_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (elements_output_nonce_result environment a).
Proof.
  assert (H : @elements_output_nonce_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.OutputNonce a environment) by reflexivity.
  rewrite H. unfold Elements.sem, elements_output_nonce_result. cbv zeta.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|]; [|reflexivity].
  unfold Datatypes.option_map. destruct (txoNonce txo) as [[[odd w]|h]|]; reflexivity.
Qed.

Lemma conf_prefix_nonzero {A : Set} (c : confidential unit A) : Int.eq (Int.repr 0) (conf_prefix c) = false.
Proof. destruct c as [x|[[] x] p]; reflexivity. Qed.

Definition nonce_pcells (n : option nonce) : list Cell := nonce_cells (nonce_prefix n) (nonce_words n).

Lemma encode_nonce_cells (n : option nonce) :
  @encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word256))) (inr (encode_nonce n)) =
    Some true :: nonce_pcells n.
Proof.
  unfold nonce_pcells, nonce_cells, encode_nonce. destruct n as [x|].
  - unfold nonce_prefix, nonce_words. rewrite conf_prefix_nonzero.
    change (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word256))) (inr (inr (encode_asset (nonce_conf x)))))
      with (Some true :: Some true :: @encode (ConfTy Word256) (encode_asset (nonce_conf x))).
    rewrite encode_conf_cells. reflexivity.
  - reflexivity.
Qed.

Definition elements_output_nonce_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _nonce
    (Tstruct _confidential noattr)) (tptr (Tstruct _confidential noattr)).

Lemma elements_output_nonce_shape :
  elements_wrapper_shape f_simplicity_output_nonce
    (elements_indexed_rest _t'5 _t'6 _numOutputs
      (elements_indexed_then_ptr _t'3 _t'4 _output _sigOutput elements_output_nonce_pexpr
        _nonce (Tstruct _confidential noattr)) (elements_skip_stmt 259)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_output_nonce_local_spec :
  application_jet_local_spec_sep f_simplicity_output_nonce elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word256)))
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => nonce_rep m b ofs (txoNonce txo)) 248 144 8 704)
    (fun a environment => @elements_output_nonce_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxOut (Elements.envTx e)) 259
    (fun txo => nonce_pcells (txoNonce txo))
    (fun m b ofs txo => nonce_rep m b ofs (txoNonce txo)) (Ty.Sum Ty.Unit (ConfTy Word256))
    _t'5 _t'6 _t'3 _t'4 _numOutputs _output _sigOutput _nonce (Tstruct _confidential noattr)
    704 8 248 144 36 elements_output_nonce_pexpr f_nonce f_simplicity_output_nonce
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) _ ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_nonce_symbol elements_nonce_funct ltac:(reflexivity)
    elements_elementsTransaction_numOutputs elements_elementsTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_output_nonce_shape ltac:(reflexivity) _ _).
  - intros x. apply nonce_cells_length_Z. apply nonce_words_length.
  - intros m1 m2 b ofs x [Hr Hp] Hl. split.
    + intros Hn. eapply uint32_array_at_mono; [apply nonce_words_length|exact (Hr Hn)|].
      intros chunk o v H1 H2. apply Hl; [exact H1|lia].
    + apply (Hl Mint32 (ofs + 32) _); [lia|change (size_chunk Mint32) with 4; lia|exact Hp].
  - intros bd dbase bw outedge m' bin ofs x cur [Hr Hp] H0 HM HSep HF.
    refine (eval_elements_nonce_layout m' bin ofs bd dbase bw outedge cur (nonce_words (txoNonce x))
      (nonce_prefix (txoNonce x)) (nonce_words_length _) H0 HM HSep _ Hp HF).
    intros Hz. apply Hr. intros Hnone. rewrite Hnone in Hz. discriminate Hz.
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_output_nonce_pexpr.
    exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigOutput 248 _nonce 144 _confidential bin inbase r
      elements_sizeof_sigOutput elements_sigOutput_nonce H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (elements_output_nonce_result environment a). split.
    + apply elements_output_nonce_sem.
    + unfold elements_output_nonce_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|].
      * apply encode_nonce_cells.
      * vm_compute. reflexivity.
Qed.
