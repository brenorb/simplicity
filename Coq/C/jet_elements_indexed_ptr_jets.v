(** Actual Elements output_script_hash and input_prev_outpoint jets against the
    literal canonical primitives OutputScriptHash / InputPrevOutpoint.  The
    environment representation asserts that the stored hash words are the
    digest of the abstract script, resp. the outpoint's hash and index. *)
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
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Lemma elements_ptr_disjoint :
  list_disjoint [_dst; _src; _env] [_i; _t'2; _t'1; _t'6; _t'5; _t'4; _t'3].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma uint32_array_at_mono (xs : list int) m1 m2 b ofs :
  length xs = 8%nat -> uint32_array_at m1 b ofs xs ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 32 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) ->
  uint32_array_at m2 b ofs xs.
Proof.
  intros HL HA HP i w Hi.
  assert (Hi8 : (i < 8)%nat) by (rewrite <- HL; apply nth_error_Some; rewrite Hi; discriminate).
  apply HP; [lia|change (size_chunk Mint32) with 4; lia|exact (HA i w Hi)].
Qed.

Lemma encode_sum_inr_hash (w : Ty.tySem Word256) :
  @encode (Ty.Sum Ty.Unit Word256) (inr w) = Some true :: @encode Word256 w.
Proof. reflexivity. Qed.

(** * output_script_hash *)

Definition elements_output_script_hash_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word256) :=
  Primitive.Combinators.prim Elements.OutputScriptHash.

Definition script_hash_words (txo : txOutput) : list int :=
  hash256_reg (byteStringHash (txoScript txo)).

Definition elements_output_script_hash_result (environment : Elements.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txo => inr (from_hash256 (byteStringHash (txoScript txo)))
  | None => inl tt
  end.

Lemma elements_output_script_hash_sem environment a :
  @elements_output_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (elements_output_script_hash_result environment a).
Proof.
  assert (H : @elements_output_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.OutputScriptHash a environment) by reflexivity.
  rewrite H. unfold Elements.sem, elements_output_script_hash_result. cbv zeta.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition elements_output_script_hash_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _scriptPubKey
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma elements_output_script_hash_shape :
  elements_wrapper_shape f_simplicity_output_script_hash
    (elements_indexed_rest _t'5 _t'6 _numOutputs
      (elements_indexed_then_ptr _t'3 _t'4 _output _sigOutput elements_output_script_hash_pexpr
        _writeHash (Tstruct _sha256_midstate noattr)) (elements_skip_stmt 256)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_output_script_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_output_script_hash elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) 248 180 8 704)
    (fun a environment => @elements_output_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxOut (Elements.envTx e)) 256
    (fun txo => hash_cells (script_hash_words txo))
    (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) Word256
    _t'5 _t'6 _t'3 _t'4 _numOutputs _output _sigOutput _writeHash (Tstruct _sha256_midstate noattr)
    704 8 248 180 32 elements_output_script_hash_pexpr f_writeHash f_simplicity_output_script_hash
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) _ ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_writeHash_symbol elements_writeHash_funct ltac:(reflexivity)
    elements_elementsTransaction_numOutputs elements_elementsTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_output_script_hash_shape ltac:(reflexivity) _ _).
  - intros x. unfold script_hash_words. rewrite hash_cells_length. rewrite (hash256_len (byteStringHash (txoScript x))).
    reflexivity.
  - intros m1 m2 b ofs x Hr Hl. eapply uint32_array_at_mono; [|exact Hr|exact Hl].
    unfold script_hash_words. exact (hash256_len _).
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    destruct (eval_elements_writeHash_layout m' bin ofs bd dbase bw outedge cur (script_hash_words x)
      ltac:(unfold script_hash_words; exact (hash256_len _)) H0 ltac:(lia) HSep Hr HF) as (me & HC & HE).
    exists me. split; [exact HC|exact HE].
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_output_script_hash_pexpr.
    exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigOutput 248 _scriptPubKey 180 _sha256_midstate bin inbase r
      elements_sizeof_sigOutput elements_sigOutput_scriptPubKey H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (elements_output_script_hash_result environment a). split.
    + apply elements_output_script_hash_sem.
    + unfold elements_output_script_hash_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|].
      * rewrite encode_sum_inr_hash. unfold script_hash_words. rewrite encode_from_hash256. reflexivity.
      * vm_compute. reflexivity.
Qed.

(** * input_prev_outpoint *)

Lemma encode_inr_prod_word (w : Ty.tySem Word256) (ix : Ty.tySem Word32) :
  @encode (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32)) (inr (w, ix)) =
    Some true :: (@encode Word256 w ++ @encode Word32 ix).
Proof. reflexivity. Qed.

Lemma elements_prevOutpoint_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) _prevOutpoint = Some (elements_symbol_block _prevOutpoint).
Proof. vm_compute; reflexivity. Qed.
Lemma elements_prevOutpoint_funct :
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _prevOutpoint) Ptrofs.zero) = Some (Internal f_prevOutpoint).
Proof. vm_compute; reflexivity. Qed.

Definition elements_input_prev_outpoint_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32)) :=
  Primitive.Combinators.prim Elements.InputPrevOutpoint.

Definition outpoint_ix (op : outpoint) : int64 := Int64.repr (Int.unsigned (opIndex op)).

Definition elements_input_prev_outpoint_result (environment : Elements.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32)) :=
  match nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txi => inr (from_hash256 (opHash (sigTxiPreviousOutpoint txi)),
      @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi))))
  | None => inl tt
  end.

Lemma elements_input_prev_outpoint_sem environment a :
  @elements_input_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (elements_input_prev_outpoint_result environment a).
Proof.
  assert (H : @elements_input_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.InputPrevOutpoint a environment) by reflexivity.
  rewrite H. unfold Elements.sem, elements_input_prev_outpoint_result. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition elements_input_prev_outpoint_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _prevOutpoint
    (Tstruct _outpoint noattr)) (tptr (Tstruct _outpoint noattr)).

Lemma elements_input_prev_outpoint_shape :
  elements_wrapper_shape f_simplicity_input_prev_outpoint
    (elements_indexed_rest _t'5 _t'6 _numInputs
      (elements_indexed_then_ptr _t'3 _t'4 _input _sigInput elements_input_prev_outpoint_pexpr
        _prevOutpoint (Tstruct _outpoint noattr)) (elements_skip_stmt 288)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Definition outpoint_words (txi : sigTxInput) : list int := hash256_reg (opHash (sigTxiPreviousOutpoint txi)).

Definition outpoint_rep (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  uint32_array_at m b ofs (outpoint_words txi) /\
  Mem.load Mint64 m b (ofs + 32) = Some (Vlong (outpoint_ix (sigTxiPreviousOutpoint txi))).

Definition outpoint_pcells (txi : sigTxInput) : list Cell :=
  elements_outpoint_cells (outpoint_words txi) (outpoint_ix (sigTxiPreviousOutpoint txi)).

Lemma outpoint_pcells_length txi : Z.of_nat (length (outpoint_pcells txi)) = 288.
Proof.
  unfold outpoint_pcells, elements_outpoint_cells. rewrite app_length, Nat2Z.inj_add.
  rewrite (hash_cells_length_Z (outpoint_words txi) (hash256_len (opHash (sigTxiPreviousOutpoint txi)))).
  rewrite encode_length. reflexivity.
Qed.

Theorem elements_input_prev_outpoint_local_spec :
  application_jet_local_spec_sep f_simplicity_input_prev_outpoint elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32))
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) outpoint_rep 544 96 0 696)
    (fun a environment => @elements_input_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxIn (Elements.envTx e)) 288 outpoint_pcells outpoint_rep
    (Ty.Prod Word256 Word32)
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _prevOutpoint (Tstruct _outpoint noattr)
    696 0 544 96 40 elements_input_prev_outpoint_pexpr f_prevOutpoint f_simplicity_input_prev_outpoint
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) outpoint_pcells_length ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_prevOutpoint_symbol elements_prevOutpoint_funct ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_input_prev_outpoint_shape ltac:(reflexivity) _ _).
  - intros m1 m2 b ofs x [Hr Hix] Hl. split.
    + eapply uint32_array_at_mono; [unfold outpoint_words; exact (hash256_len _)|exact Hr|].
      intros chunk o v H1 H2. apply Hl; [exact H1|lia].
    + apply (Hl Mint64 (ofs + 32) _); [lia|change (size_chunk Mint64) with 8; lia|exact Hix].
  - intros bd dbase bw outedge m' bin ofs x cur [Hr Hix] H0 HM HSep HF.
    destruct (eval_elements_prevOutpoint_layout m' bin ofs bd dbase bw outedge cur (outpoint_words x)
      (outpoint_ix (sigTxiPreviousOutpoint x))
      ltac:(unfold outpoint_words; exact (hash256_len _)) H0 ltac:(lia) HSep Hr Hix HF) as (me & HC & HE).
    exists me. split; [exact HC|exact HE].
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_input_prev_outpoint_pexpr.
    exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigInput 544 _prevOutpoint 96 _outpoint bin inbase r
      elements_sizeof_sigInput elements_sigInput_prevOutpoint H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (elements_input_prev_outpoint_result environment a). split.
    + apply elements_input_prev_outpoint_sem.
    + unfold elements_input_prev_outpoint_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi|].
      * unfold outpoint_pcells, elements_outpoint_cells, outpoint_words, outpoint_ix.
        rewrite encode_inr_prod_word. f_equal.
        rewrite encode_from_hash256. f_equal.
        rewrite decode_wide32_unsigned.
        -- reflexivity.
        -- pose proof (Int.unsigned_range (opIndex (sigTxiPreviousOutpoint txi))) as H.
           change Int.modulus with 4294967296 in H. exact H.
      * vm_compute. reflexivity.
Qed.
