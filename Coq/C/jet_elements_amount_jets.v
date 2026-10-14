(** Actual Elements input_amount and output_amount jets against their
    canonical specifications, the programs of
    Simplicity.Elements.Programs.Transaction that pair the amount and asset
    primitives.  The element relation states that the C [confidential] and
    [confAmount] of the selected element hold the logical asset and amount. *)
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
Require Simplicity.Alg.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.


Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).

Lemma elements_utxo_amt : elements_field_at _utxo _amt 72.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_sigOutput_amt : elements_field_at _sigOutput _amt 104.
Proof. vm_compute; reflexivity. Qed.

(** * Canonical specification

    [Simplicity.Elements.Programs.Transaction]:
    [primitive XAmount &&& primitive XAsset
       >>> match (injl unit) (ih &&& oh >>> match (injl unit) (injr iden))]. *)
Definition elements_amount_pair_spec {alg : Primitive.Algebra} {A CM CA : Ty}
    (pm : alg A (Ty.Sum Ty.Unit CM)) (pa : alg A (Ty.Sum Ty.Unit CA)) :
    alg A (Ty.Sum Ty.Unit (Ty.Prod CA CM)) :=
  Alg.Core.Combinators.comp (Alg.Core.Combinators.pair pm pa)
    (Alg.Core.Combinators.case (Alg.Core.Combinators.injl Alg.Core.Combinators.unit)
      (Alg.Core.Combinators.comp
        (Alg.Core.Combinators.pair (Alg.Core.Combinators.drop Alg.Core.Combinators.iden)
          (Alg.Core.Combinators.take Alg.Core.Combinators.iden))
        (Alg.Core.Combinators.case (Alg.Core.Combinators.injl Alg.Core.Combinators.unit)
          (Alg.Core.Combinators.injr Alg.Core.Combinators.iden)))).

Lemma elements_amount_pair_sem {A CM CA : Ty}
    (tm : Ty.tySem A -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit CM)))
    (ta : Ty.tySem A -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit CA))) (a : Ty.tySem A) env :
  @elements_amount_pair_spec (PrimitivePrimSem option_Monad_Zero) A CM CA tm ta a env =
    match tm a env, ta a env with
    | Some (inr am), Some (inr ast) => Some (inr (ast, am))
    | Some (inl _), Some _ => Some (inl tt)
    | Some (inr _), Some (inl _) => Some (inl tt)
    | _, _ => None
    end.
Proof.
  unfold elements_amount_pair_spec.
  remember (tm a env) as r1 eqn:HR1. remember (ta a env) as r2 eqn:HR2.
  destruct r1 as [[u1 | am] | ]; destruct r2 as [[u2 | ast] | ];
    lazy beta iota zeta delta in HR1, HR2 |- *;
    try rewrite <- HR1; try rewrite <- HR2; reflexivity.
Qed.

(** * Amount representation *)

Definition amount_words (a : amountWith unit) : list int :=
  match a with Explicit _ => repeat Int.zero 8 | Confidential (Point _ x) _ => hash256_reg x end.

Lemma amount_words_length a : length (amount_words a) = 8%nat.
Proof. destruct a as [v|[odd x] p]; [reflexivity|exact (hash256_len x)]. Qed.

Definition amount_value (a : amountWith unit) : int64 :=
  match a with Explicit v => v | Confidential _ _ => Int64.zero end.

(** An explicit amount holds its 64-bit value in the union; a confidential
    one the x-coordinate words of the commitment. *)
Definition amount_rep (m : mem) (b : block) (ofs : Z) (a : amountWith unit) : Prop :=
  match a with
  | Explicit v => Mem.load Mint64 m b ofs = Some (Vlong v)
  | Confidential (Point _ x) _ => uint32_array_at m b ofs (hash256_reg x)
  end /\
  Mem.load Mint32 m b (ofs + 32) = Some (Vint (conf_prefix a)).

Definition amount_pcells (a : amountWith unit) : list Cell :=
  amt_cells (conf_prefix a) (amount_words a) (amount_value a).

Lemma amount_pcells_length a : Z.of_nat (length (amount_pcells a)) = 258.
Proof. apply amt_cells_length_Z. apply amount_words_length. Qed.

(** [encodeAmount] of the canonical primitive semantics. *)
Definition encode_amount (a : amountWith unit) : Ty.tySem (ConfTy Word64) :=
  match a with
  | Explicit v => inr (@fromZ (WordToZ 6) (Int64.unsigned v))
  | Confidential (Point odd x) _ => inl (conf_toBit odd, from_hash256 x)
  end.

Lemma decode_wide64_unsigned' v :
  decode_wide W64 (Int64.zero_ext (wide_bits W64) v) = @fromZ (WordToZ 6) (Int64.unsigned v).
Proof.
  unfold decode_wide. change (wide_log W64) with 6%nat. change (wide_bits W64) with 64.
  rewrite Int64.zero_ext_above by (change Int64.zwordsize with 64; lia). reflexivity.
Qed.

Lemma encode_conf64_inr (w : Ty.tySem Word64) :
  @encode (ConfTy Word64) (inr w) = Some true :: repeat None 193 ++ @encode Word64 w.
Proof. reflexivity. Qed.

Lemma encode_conf64_inl (b : bool) (w : Ty.tySem Word256) :
  @encode (ConfTy Word64) (inl (conf_toBit b, w)) = Some false :: Some b :: @encode Word256 w.
Proof. destruct b; cbn; rewrite ?app_nil_r; reflexivity. Qed.

Lemma amt_cells_explicit xs v : amt_cells (Int.repr 1) xs v =
  Some true :: repeat None 193 ++ encode (decode_wide W64 (Int64.zero_ext (wide_bits W64) v)).
Proof. reflexivity. Qed.
Lemma amt_cells_odd xs v : amt_cells (Int.repr 3) xs v = Some false :: Some true :: hash_cells xs.
Proof. reflexivity. Qed.
Lemma amt_cells_even xs v : amt_cells (Int.repr 2) xs v = Some false :: Some false :: hash_cells xs.
Proof. reflexivity. Qed.

Lemma encode_amount_cells (a : amountWith unit) :
  @encode (ConfTy Word64) (encode_amount a) = amount_pcells a.
Proof.
  unfold amount_pcells. destruct a as [v|[odd x] p]; unfold encode_amount, conf_prefix, amount_words, amount_value.
  - rewrite encode_conf64_inr, amt_cells_explicit, decode_wide64_unsigned'. reflexivity.
  - rewrite encode_conf64_inl, encode_from_hash256.
    destruct odd; [rewrite amt_cells_odd|rewrite amt_cells_even]; reflexivity.
Qed.

Lemma amount_rep_mono m1 m2 b ofs a : amount_rep m1 b ofs a ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 40 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> amount_rep m2 b ofs a.
Proof.
  intros [Hr Hp] Hl. split.
  - destruct a as [v|[odd x] p].
    + apply (Hl Mint64 ofs _); [lia|change (size_chunk Mint64) with 8; lia|exact Hr].
    + eapply uint32_array_at_mono; [exact (hash256_len x)|exact Hr|].
      intros chunk o v H1 H2. apply Hl; [exact H1|lia].
  - apply (Hl Mint32 (ofs + 32) _); [lia|change (size_chunk Mint32) with 4; lia|exact Hp].
Qed.

Lemma amount_rep_runs bd dbase bw outedge m' bin ofs a cur :
  amount_rep m' bin ofs a -> 0 <= ofs -> ofs + 40 <= Ptrofs.max_unsigned ->
  out_sep bd dbase bw outedge cur 258 bin ofs (ofs + 40) ->
  write_frame_at m' bd dbase bw outedge cur 258 ->
  exists me, Clight2.eval_funcall elements_ge m' (Internal f_amt)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
    write_effect m' me bd dbase bw outedge cur 258 (amount_pcells a).
Proof.
  intros [Hr Hp] H0 HM HSep HF.
  refine (eval_elements_amt_layout m' bin ofs bd dbase bw outedge cur (amount_words a) (amount_value a)
    (conf_prefix a) (amount_words_length a) H0 HM HSep _ _ Hp HF).
  - destruct a as [v|[[] x] p]; intros Hc; first [exact Hr | discriminate Hc].
  - destruct a as [v|[[] x] p]; intros Hc; first [exact Hr | discriminate Hc].
Qed.

(** * The shared proof: asset then amount of the selected element *)

Definition amount_pair_result {A} (elems : list A) (ga : A -> assetWith unit) (gm : A -> amountWith unit)
    (a : Ty.tySem Word32) : Ty.tySem (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64))) :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | Some x => inr (encode_asset (ga x), encode_amount (gm x))
  | None => inl tt
  end.

Lemma encode_inr_pair (x : Ty.tySem (ConfTy Word256)) (y : Ty.tySem (ConfTy Word64)) :
  @encode (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64))) (inr (x, y)) =
    Some true :: (@encode (ConfTy Word256) x ++ @encode (ConfTy Word64) y).
Proof. reflexivity. Qed.

Lemma elements_amount_disjoint :
  list_disjoint [_dst; _src; _env] [_i; _t'2; _t'1; _t'8; _t'7; _t'6; _t'5; _t'4; _t'3].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Theorem elements_asset_amount_local {A} (elems_of : Elements.env -> list A)
    (ga : A -> assetWith unit) (gm : A -> amountWith unit)
    (countfield arrfield sid : ident) (cdelta adelta sz poffa poffm : Z)
    (pexpr1 pexpr2 : expr) (f : function)
    (Hpty1 : typeof pexpr1 = tptr (Tstruct _confidential noattr))
    (Hpty2 : typeof pexpr2 = tptr (Tstruct _confAmount noattr))
    (Hcf : elements_field_at _elementsTransaction countfield cdelta)
    (Haf : elements_field_at _elementsTransaction arrfield adelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 760) (Hab : 0 <= adelta /\ adelta + 8 <= 760)
    (Hsz : 0 < sz <= 1000) (Hpa : 0 <= poffa /\ poffa + 36 <= sz) (Hpm : 0 <= poffm /\ poffm + 40 <= sz)
    (Hptr1 : forall e le' m' bin inbase r,
      le'!_t'6 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
      eval_expr elements_ge e le' m' pexpr1 (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poffa))))
    (Hptr2 : forall e le' m' bin inbase r,
      le'!_t'4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
      eval_expr elements_ge e le' m' pexpr2 (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poffm))))
    (Hshape : elements_wrapper_shape f
      (elements_indexed_rest _t'7 _t'8 countfield
        (elements_indexed_then_ptr2 _t'5 _t'6 _t'3 _t'4 arrfield sid pexpr1 _asset (Tstruct _confidential noattr)
          pexpr2 _amt (Tstruct _confAmount noattr)) (elements_skip_stmt 516)))
    (spec : Ty.tySem Word32 -> Elements.env ->
      option (Ty.tySem (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64)))))
    (Hspec : forall a environment,
      spec a environment = Some (amount_pair_result (elems_of environment) ga gm a)) :
  application_jet_local_spec_sep f elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64)))
    (indexed_ptr_rep elems_of
      (fun m b ofs x => asset_rep m b (ofs + poffa) (ga x) /\ amount_rep m b (ofs + poffm) (gm x))
      sz 0 adelta cdelta) spec.
Proof.
  refine (elements_indexed_gen_local elems_of 516
    (fun x => asset_pcells (ga x) ++ amount_pcells (gm x))
    (fun m b ofs x => asset_rep m b (ofs + poffa) (ga x) /\ amount_rep m b (ofs + poffm) (gm x))
    (Ty.Prod (ConfTy Word256) (ConfTy Word64))
    _t'7 _t'8 countfield cdelta adelta sz _ f
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(split; lia) _ Hcf Hcb Hab Hsz _ _ Hshape ltac:(reflexivity) spec _).
  - intros x. rewrite app_length, Nat2Z.inj_add.
    unfold asset_pcells. rewrite (asset_cells_length_Z _ _ (asset_words_length (ga x))), amount_pcells_length.
    reflexivity.
  - intros m1 m2 b ofs x [Hra Hrm] Hl. split.
    + eapply asset_rep_mono; [exact Hra|]. intros chunk o v H1 H2. apply Hl; lia.
    + eapply amount_rep_mono; [exact Hrm|]. intros chunk o v H1 H2. apply Hl; lia.
  - intros bd dbase bw outedge.
    refine (exec_elements_indexed_then_ptr2 258 258 (fun x => asset_pcells (ga x)) (fun x => amount_pcells (gm x))
      (fun m b ofs x => asset_rep m b (ofs + poffa) (ga x) /\ amount_rep m b (ofs + poffm) (gm x))
      _t'5 _t'6 _t'3 _t'4 arrfield sid _asset _amt (Tstruct _confidential noattr) (Tstruct _confAmount noattr)
      adelta sz poffa poffm pexpr1 pexpr2 f_asset f_amt
      ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
      ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
      ltac:(lia) ltac:(lia) _ Hpty1 Hpty2 ltac:(intros bl; reflexivity) ltac:(intros bl; reflexivity)
      elements_asset_symbol elements_asset_funct ltac:(reflexivity)
      elements_amt_symbol elements_amt_funct ltac:(reflexivity)
      Haf Hab Hsz _ bd dbase bw outedge _ _ Hptr1 Hptr2).
    + intros x. unfold asset_pcells. exact (asset_cells_length_Z _ _ (asset_words_length (ga x))).
    + intros m1 m2 b ofs x [Hra Hrm] Hl. split.
      * eapply asset_rep_mono; [exact Hra|]. intros chunk o v H1 H2. apply Hl; lia.
      * eapply amount_rep_mono; [exact Hrm|]. intros chunk o v H1 H2. apply Hl; lia.
    + intros m' bin ofs x cur [Hra _] H0 HM HSep HF.
      eapply asset_rep_runs; [exact Hra|lia|lia| |exact HF].
      eapply out_sep_range; [exact HSep|lia|lia].
    + intros m' bin ofs x cur [_ Hrm] H0 HM HSep HF.
      eapply amount_rep_runs; [exact Hrm|lia|lia| |exact HF].
      eapply out_sep_range; [exact HSep|lia|lia].
  - intros a environment. exists (amount_pair_result (elems_of environment) ga gm a). split; [apply Hspec|].
    unfold amount_pair_result, indexed_ptr_cells. unfold toZ32.
    destruct (nth_error (elems_of environment) (Z.to_nat (toZ a))) as [x|].
    + rewrite encode_inr_pair, encode_conf_cells, encode_amount_cells. reflexivity.
    + vm_compute. reflexivity.
Qed.

(** * input_amount *)

Definition elements_input_amount_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64))) :=
  elements_amount_pair_spec (Primitive.Combinators.prim Elements.InputAmount)
    (Primitive.Combinators.prim Elements.InputAsset).

Lemma elements_input_amount_sem a environment :
  @elements_input_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (amount_pair_result (sigTxIn (Elements.envTx environment))
      (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi)) a).
Proof.
  assert (H : @elements_input_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    @elements_amount_pair_spec (PrimitivePrimSem option_Monad_Zero) _ _ _
      (fun a e => Elements.sem Elements.InputAmount a e) (fun a e => Elements.sem Elements.InputAsset a e)
      a environment) by reflexivity.
  rewrite H, elements_amount_pair_sem. unfold Elements.sem, amount_pair_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map.
  destruct (utxoAsset (sigTxiTxo txi)) as [h|[odd x] p]; destruct (utxoAmount (sigTxiTxo txi)) as [v|[odd' x'] p'];
    reflexivity.
Qed.

Definition elements_input_amount_pexpr1 : expr :=
  Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar _t'6 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _txo (Tstruct _utxo noattr))
    _asset (Tstruct _confidential noattr)) (tptr (Tstruct _confidential noattr)).

Definition elements_input_amount_pexpr2 : expr :=
  Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _txo (Tstruct _utxo noattr))
    _amt (Tstruct _confAmount noattr)) (tptr (Tstruct _confAmount noattr)).

Lemma elements_input_amount_shape :
  elements_wrapper_shape f_simplicity_input_amount
    (elements_indexed_rest _t'7 _t'8 _numInputs
      (elements_indexed_then_ptr2 _t'5 _t'6 _t'3 _t'4 _input _sigInput elements_input_amount_pexpr1 _asset
        (Tstruct _confidential noattr) elements_input_amount_pexpr2 _amt (Tstruct _confAmount noattr))
      (elements_skip_stmt 516)).
Proof. repeat split; try reflexivity. apply elements_amount_disjoint. Qed.

Theorem elements_input_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_input_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64)))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e))
      (fun m b ofs txi => asset_rep m b (ofs + 168) (utxoAsset (sigTxiTxo txi)) /\
        amount_rep m b (ofs + 208) (utxoAmount (sigTxiTxo txi))) 544 0 0 696)
    (fun a environment => @elements_input_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_asset_amount_local (fun e => sigTxIn (Elements.envTx e))
    (fun txi => utxoAsset (sigTxiTxo txi)) (fun txi => utxoAmount (sigTxiTxo txi))
    _numInputs _input _sigInput 696 0 544 168 208
    elements_input_amount_pexpr1 elements_input_amount_pexpr2 f_simplicity_input_amount
    ltac:(reflexivity) ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ elements_input_amount_shape _ elements_input_amount_sem).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_input_amount_pexpr1.
    pose proof (eval_elements_elem_nested_field_addr e le' m' _t'6 _i _sigInput 544 _txo 136 _utxo
      _asset 32 _confidential bin inbase r elements_sizeof_sigInput elements_sigInput_txo
      elements_utxo_asset H4 HI Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)) as H.
    exact H.
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_input_amount_pexpr2.
    pose proof (eval_elements_elem_nested_field_addr e le' m' _t'4 _i _sigInput 544 _txo 136 _utxo
      _amt 72 _confAmount bin inbase r elements_sizeof_sigInput elements_sigInput_txo
      elements_utxo_amt H4 HI Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)) as H.
    exact H.
Qed.

(** * output_amount *)

Definition elements_output_amount_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64))) :=
  elements_amount_pair_spec (Primitive.Combinators.prim Elements.OutputAmount)
    (Primitive.Combinators.prim Elements.OutputAsset).

Lemma elements_output_amount_sem a environment :
  @elements_output_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (amount_pair_result (sigTxOut (Elements.envTx environment))
      (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo)) a).
Proof.
  assert (H : @elements_output_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    @elements_amount_pair_spec (PrimitivePrimSem option_Monad_Zero) _ _ _
      (fun a e => Elements.sem Elements.OutputAmount a e) (fun a e => Elements.sem Elements.OutputAsset a e)
      a environment) by reflexivity.
  rewrite H, elements_amount_pair_sem. unfold Elements.sem, amount_pair_result. cbv zeta.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|]; [|reflexivity].
  unfold Datatypes.option_map.
  destruct (txoAsset txo) as [h|[odd x] p]; destruct (txoAmount txo) as [v|[odd' x'] p'];
    reflexivity.
Qed.

Definition elements_output_amount_pexpr1 : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'6 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _asset
    (Tstruct _confidential noattr)) (tptr (Tstruct _confidential noattr)).

Definition elements_output_amount_pexpr2 : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _amt
    (Tstruct _confAmount noattr)) (tptr (Tstruct _confAmount noattr)).

Lemma elements_output_amount_shape :
  elements_wrapper_shape f_simplicity_output_amount
    (elements_indexed_rest _t'7 _t'8 _numOutputs
      (elements_indexed_then_ptr2 _t'5 _t'6 _t'3 _t'4 _output _sigOutput elements_output_amount_pexpr1 _asset
        (Tstruct _confidential noattr) elements_output_amount_pexpr2 _amt (Tstruct _confAmount noattr))
      (elements_skip_stmt 516)).
Proof. repeat split; try reflexivity. apply elements_amount_disjoint. Qed.

Theorem elements_output_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_output_amount elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64)))
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => asset_rep m b (ofs + 0) (clearPrf (txoAsset txo)) /\
        amount_rep m b (ofs + 104) (clearPrf (txoAmount txo))) 248 0 8 704)
    (fun a environment => @elements_output_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_asset_amount_local (fun e => sigTxOut (Elements.envTx e))
    (fun txo => clearPrf (txoAsset txo)) (fun txo => clearPrf (txoAmount txo))
    _numOutputs _output _sigOutput 704 8 248 0 104
    elements_output_amount_pexpr1 elements_output_amount_pexpr2 f_simplicity_output_amount
    ltac:(reflexivity) ltac:(reflexivity)
    elements_elementsTransaction_numOutputs elements_elementsTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ elements_output_amount_shape _ elements_output_amount_sem).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_output_amount_pexpr1.
    exact (eval_elements_elem_field_addr e le' m' _t'6 _i _sigOutput 248 _asset 0 _confidential bin inbase r
      elements_sizeof_sigOutput elements_sigOutput_asset H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_output_amount_pexpr2.
    exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigOutput 248 _amt 104 _confAmount bin inbase r
      elements_sizeof_sigOutput elements_sigOutput_amt H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
Qed.
