(** Actual Elements issuance_token_amount and current_issuance_token_amount
    jets against the IssuanceTokenAmount primitive (resp. its current-input
    program), with executability and no-premise statements.  They depend on
    the forward-memory prerequisite through the helper proof, hence live in
    this derived directory. *)
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
Require Import C.jet_elements_asset_jets C.jet_elements_amt_helper C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_helper C.jet_elements_issuance_jets C.jet_elements_issuance_amount_jets.
Require Import C.jet_elements_current_exec C.jet_elements_current_spec C.jet_elements_current_ptr.
Require Import C.jet_elements_current_ptr_jets C.jet_elements_current_input_jets.
Require Import C.jet_frame_constructible_app C.jet_env_constructible C.jet_elements_env_constructible.
Require Import C.jet_elements_elem_buildable C.jet_elements_executable C.jet_elements_executable_conf.
Require Import C.jet_elements_executable_current C.jet_elements_runs_everywhere.
Require Import JetForward.jet_elements_issuance_token_then JetForward.jet_elements_issuance_token_helper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).


(** [issuanceTokenAmount = either newIssuanceTokenAmount (const (Amount (Explicit 0)))]. *)
Definition issuance_token_amount (i : issuance) : amountWith (list byte) :=
  match i with inl new => newIssuanceTokenAmount new | inr _ => Explicit Int64.zero end.

(** The C record holds a token amount only for a new issuance. *)
Definition token_amount_rep (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  Mem.load Mint32 m b (ofs + 272) = Some (Vint (issuance_tag (sigTxiIssuance txi))) /\
  forall new, sigTxiIssuance txi = Some (inl new) ->
    amount_rep m b (ofs + 32) (clearPrf (newIssuanceTokenAmount new)).

Definition token_pcells (txi : sigTxInput) : list Cell :=
  issuance_tagged_cells (opt_is_some (sigTxiIssuance txi)) 258
    (match sigTxiIssuance txi with
     | Some i => amount_pcells (clearPrf (issuance_token_amount i))
     | None => []
     end).

Lemma token_pcells_length txi : Z.of_nat (length (token_pcells txi)) = 259.
Proof.
  unfold token_pcells, issuance_tagged_cells. destruct (sigTxiIssuance txi) as [i|]; cbn [opt_is_some].
  - cbn [app length]. rewrite Nat2Z.inj_succ, amount_pcells_length. reflexivity.
  - reflexivity.
Qed.

(** The parameters handed to the helper contract. *)
Definition token_amount_of (o : option issuance) : amountWith unit :=
  match o with Some i => clearPrf (issuance_token_amount i) | None => Explicit Int64.zero end.

Lemma token_cells_pcells txi :
  token_cells (issuance_tag (sigTxiIssuance txi))
    (conf_prefix (token_amount_of (sigTxiIssuance txi)))
    (amount_words (token_amount_of (sigTxiIssuance txi)))
    (amount_value (token_amount_of (sigTxiIssuance txi))) = token_pcells txi.
Proof.
  unfold token_pcells, token_cells, token_amount_of.
  destruct (sigTxiIssuance txi) as [[new|re]|]; reflexivity.
Qed.

Lemma token_amount_rep_pres : forall m1 m2 b ofs x, token_amount_rep m1 b ofs x ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 280 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> token_amount_rep m2 b ofs x.
Proof.
  intros m1 m2 b ofs x [Ht Hh] Hl. split.
  - apply (Hl Mint32 (ofs + 272) _); [lia|change (size_chunk Mint32) with 4; lia|exact Ht].
  - intros new Hn. eapply amount_rep_mono; [exact (Hh new Hn)|].
    intros chunk o v H1 H2. apply Hl; lia.
Qed.

Lemma token_amount_rep_runs : forall bd dbase bw outedge m' bin ofs x cur,
  token_amount_rep m' bin ofs x -> 0 <= ofs -> ofs + 280 <= Ptrofs.max_unsigned ->
  out_sep bd dbase bw outedge cur 259 bin ofs (ofs + 280) ->
  write_frame_at m' bd dbase bw outedge cur 259 ->
  exists me, Clight2.eval_funcall elements_ge m' (Internal f_issuanceTokenAmt)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
    write_effect m' me bd dbase bw outedge cur 259 (token_pcells x).
Proof.
  intros bd dbase bw outedge m' bin ofs x cur [Ht Hh] H0 HM HSep HF.
  rewrite <- token_cells_pcells.
  refine (eval_elements_issuanceTokenAmt_layout m' bin ofs bd dbase bw outedge cur
    (issuance_tag (sigTxiIssuance x)) _ _ _ (amount_words_length _) H0 HM HSep Ht _ HF).
  unfold token_amount_of. destruct (sigTxiIssuance x) as [[new|re]|] eqn:Hiss; intros Hc;
    try discriminate Hc.
  destruct (Hh new eq_refl) as [Hd Hp]. cbn [issuance_token_amount].
  split; [exact Hp|].
  destruct (clearPrf (newIssuanceTokenAmount new)) as [v|[[] h] p]; split; intros Hx;
    first [exact Hd | discriminate Hx].
Qed.

Definition token_amount_result (elems : list sigTxInput) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))) :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | Some txi => inr (match sigTxiIssuance txi with
                     | Some i => inr (encode_amount (clearPrf (issuance_token_amount i)))
                     | None => inl tt
                     end)
  | None => inl tt
  end.

Definition elements_issuance_token_amount_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))) :=
  Primitive.Combinators.prim Elements.IssuanceTokenAmount.

Lemma elements_issuance_token_amount_sem a environment :
  @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (token_amount_result (sigTxIn (Elements.envTx environment)) a).
Proof.
  assert (H : @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.IssuanceTokenAmount a environment) by reflexivity.
  rewrite H. unfold Elements.sem, token_amount_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map. destruct (sigTxiIssuance txi) as [[new|re]|]; [| |reflexivity].
  - unfold issuance_token_amount. destruct (newIssuanceTokenAmount new) as [v|[odd x] p]; reflexivity.
  - reflexivity.
Qed.

Lemma encode_token_amount_cells txi :
  @encode (Ty.Sum Ty.Unit (ConfTy Word64))
    (match sigTxiIssuance txi with
     | Some i => inr (encode_amount (clearPrf (issuance_token_amount i)))
     | None => inl tt
     end) = token_pcells txi.
Proof.
  unfold token_pcells, issuance_tagged_cells.
  destruct (sigTxiIssuance txi) as [i|]; cbn [opt_is_some].
  - change (@encode (Ty.Sum Ty.Unit (ConfTy Word64)) (inr (encode_amount (clearPrf (issuance_token_amount i)))))
      with (Some true :: @encode (ConfTy Word64) (encode_amount (clearPrf (issuance_token_amount i)))).
    rewrite encode_amount_cells. reflexivity.
  - reflexivity.
Qed.

(** * issuance_token_amount *)

Lemma elements_issuance_token_amount_shape :
  elements_wrapper_shape f_simplicity_issuance_token_amount
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput issuance_pexpr _issuanceTokenAmt
        (Tstruct _assetIssuance noattr)) (elements_skip_stmt 259)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_issuance_token_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance_token_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) token_amount_rep 544 256 0 696)
    (fun a environment => @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxIn (Elements.envTx e)) 259
    token_pcells token_amount_rep (Ty.Sum Ty.Unit (ConfTy Word64))
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _issuanceTokenAmt (Tstruct _assetIssuance noattr)
    696 0 544 256 280 issuance_pexpr f_issuanceTokenAmt f_simplicity_issuance_token_amount
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) token_pcells_length ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_issuanceTokenAmt_symbol elements_issuanceTokenAmt_funct ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    token_amount_rep_pres token_amount_rep_runs _ elements_issuance_token_amount_shape ltac:(reflexivity) _ _).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. exact (eval_issuance_pexpr e le' m' bin inbase r H4 HI Hi0 HM).
  - intros a environment. exists (token_amount_result (sigTxIn (Elements.envTx environment)) a).
    split; [apply elements_issuance_token_amount_sem|].
    unfold token_amount_result, indexed_ptr_cells. unfold toZ32.
    destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|].
    + change (@encode (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)))
        (inr (match sigTxiIssuance txi with
              | Some i => inr (encode_amount (clearPrf (issuance_token_amount i)))
              | None => inl tt
              end))) with
        (Some true :: @encode (Ty.Sum Ty.Unit (ConfTy Word64))
          (match sigTxiIssuance txi with
           | Some i => inr (encode_amount (clearPrf (issuance_token_amount i)))
           | None => inl tt
           end)).
      rewrite encode_token_amount_cells. reflexivity.
    + vm_compute. reflexivity.
Qed.

(** * current_issuance_token_amount *)

Definition elements_current_issuance_token_amount_spec {alg : Primitive.Algebra} :
    alg Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)) :=
  elements_current_spec (@elements_issuance_token_amount_spec alg).

Definition elements_current_issuance_token_amount_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _sigInput noattr))) (Etempvar _t'3 tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _issuance
    (Tstruct _assetIssuance noattr)) (tptr (Tstruct _assetIssuance noattr)).

Lemma elements_current_issuance_token_amount_shape :
  elements_wrapper_shape f_simplicity_current_issuance_token_amount
    (elements_current_ptr_rest _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput
      elements_current_issuance_token_amount_pexpr _issuanceTokenAmt (Tstruct _assetIssuance noattr)).
Proof. repeat split; try reflexivity. apply elements_current_ptr_disjoint. Qed.

Theorem elements_current_issuance_token_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_current_issuance_token_amount elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit (ConfTy Word64))
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx token_amount_rep 544 256 0 696)
    (fun a environment =>
      @elements_current_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_current_input_ptr 259 token_pcells token_amount_rep (Ty.Sum Ty.Unit (ConfTy Word64))
    _issuanceTokenAmt (Tstruct _assetIssuance noattr) 256 280
    elements_current_issuance_token_amount_pexpr f_issuanceTokenAmt f_simplicity_current_issuance_token_amount
    ltac:(split; lia) ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_issuanceTokenAmt_symbol elements_issuanceTokenAmt_funct ltac:(reflexivity) ltac:(split; lia)
    token_amount_rep_pres token_amount_rep_runs
    _ elements_current_issuance_token_amount_shape ltac:(reflexivity)
    (fun a e => @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a e)
    (fun txi => match sigTxiIssuance txi with
                | Some i => inr (encode_amount (clearPrf (issuance_token_amount i)))
                | None => inl tt
                end)
    (fun a e => elements_issuance_token_amount_sem a e)
    encode_token_amount_cells token_pcells_length).
  intros e le' m' bin inbase ixv H2 H3 Hi0 HM. unfold elements_current_issuance_token_amount_pexpr.
  exact (eval_elements_elem_field_addr e le' m' _t'2 _t'3 _sigInput 544 _issuance 256 _assetIssuance bin inbase ixv
    elements_sizeof_sigInput elements_sigInput_issuance H2 H3 Hi0 ltac:(split; lia) ltac:(lia)
    ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
Qed.

(** * Executability and no-premise statements *)

Lemma token_amount_elem_stable : elem_stable token_amount_rep.
Proof.
  intros m m' b ofs x HE [H1 H2]. split.
  - eapply memory_extension_load; eassumption.
  - intros new Hn. eapply amount_rep_stable; [exact HE|exact (H2 new Hn)].
Qed.

Lemma token_amount_rep_local : elem_local token_amount_rep 280.
Proof. intros m1 m2 b ofs x Hr Hl. exact (token_amount_rep_pres m1 m2 b ofs x Hr Hl). Qed.

Definition new_of (txi : sigTxInput) : option newIssuance :=
  match sigTxiIssuance txi with Some (inl new) => Some new | _ => None end.

Lemma token_amount_rep_buildable : elem_buildable 8 token_amount_rep 280.
Proof.
  eapply elem_buildable_impl;
    [|apply (elem_buildable_pair 8
        (fun m b ofs (x : sigTxInput) =>
          forall new, new_of x = Some new -> amount_rep m b ofs (clearPrf (newIssuanceTokenAmount new)))
        (fun m b ofs (x : sigTxInput) =>
          Mem.load Mint32 m b ofs = Some (Vint (issuance_tag (sigTxiIssuance x))))
        32 40 272 4 280); try lia; try divides].
  - intros m b ofs x [H1 H2]. split; [exact H2|].
    intros new Hn. apply H1. unfold new_of. rewrite Hn. reflexivity.
  - apply elem_local_option. apply (amount_rep_local (fun n => clearPrf (newIssuanceTokenAmount n))).
  - apply elem_buildable_option; [lia|].
    apply (amount_rep_buildable (fun n => clearPrf (newIssuanceTokenAmount n))).
  - eapply elem_buildable_align; [|apply int32_buildable]. divides.
Qed.

Theorem elements_issuance_token_amount_local_spec_executable :
  application_sep_runs_on_fresh_frames f_simplicity_issuance_token_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) token_amount_rep 544 256 0 696)
    (fun a environment => @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply application_jet_local_spec_sep_executable;
    [vm_compute; discriminate|vm_compute; discriminate|exact elements_issuance_token_amount_local_spec|].
  apply indexed_ptr_rep_stable. exact token_amount_elem_stable.
Qed.

Theorem elements_current_issuance_token_amount_local_spec_executable :
  application_sep_runs_on_fresh_frames f_simplicity_current_issuance_token_amount elements_ge Elements.env
    Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))
    (current_ptr_rep (fun e => sigTxIn (Elements.envTx e)) Elements.envIx token_amount_rep 544 256 0 696)
    (fun a environment =>
      @elements_current_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply application_jet_local_spec_sep_executable;
    [vm_compute; discriminate|vm_compute; discriminate
    |exact elements_current_issuance_token_amount_local_spec|].
  apply current_ptr_rep_stable. exact token_amount_elem_stable.
Qed.

Theorem elements_issuance_token_amount_runs_everywhere :
  runs_everywhere f_simplicity_issuance_token_amount Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64)))
    (fun a environment => @elements_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply sep_runs_everywhere; [exact elements_issuance_token_amount_local_spec_executable|].
  intros e.
  eapply (@indexed_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e)) token_amount_rep
    544 256 280 0 696 8);
    first [exact token_amount_rep_local|exact token_amount_rep_buildable|side e].
Qed.

Theorem elements_current_issuance_token_amount_runs_everywhere :
  runs_everywhere f_simplicity_current_issuance_token_amount Ty.Unit (Ty.Sum Ty.Unit (ConfTy Word64))
    (fun a environment =>
      @elements_current_issuance_token_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply sep_runs_everywhere; [exact elements_current_issuance_token_amount_local_spec_executable|].
  intros e.
  eapply (@current_ptr_rep_constructible _ (fun e => sigTxIn (Elements.envTx e)) token_amount_rep
    544 256 280 0 696 8);
    first [exact token_amount_rep_local|exact token_amount_rep_buildable|side e].
Qed.
