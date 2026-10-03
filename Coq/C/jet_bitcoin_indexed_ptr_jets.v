(** Actual Bitcoin output_script_hash and input_prev_outpoint jets against the
    literal canonical primitives OutputScriptHash / InputPrevOutpoint.  The
    environment representation asserts that the stored hash words are the
    digest of the abstract script, resp. the outpoint's hash and index. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_version_exec C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_effects.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_index_eval.
Require Import C.jet_bitcoin_indexed_exec C.jet_bitcoin_indexed_ptr_then C.jet_bitcoin_indexed_scalar.
Require Import C.jet_bitcoin_hash_write C.jet_bitcoin_hash_helpers C.jet_bitcoin_indexed_ptr.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_indexed_scalar_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Lemma bitcoin_ptr_disjoint :
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

Definition bitcoin_output_script_hash_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word256) :=
  Primitive.Combinators.prim Bitcoin.OutputScriptHash.

Definition script_hash_words (txo : txOutput) : list int :=
  hash256_reg (byteStringHash (txoScript txo)).

Definition bitcoin_output_script_hash_result (environment : Bitcoin.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxOut (Bitcoin.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txo => inr (from_hash256 (byteStringHash (txoScript txo)))
  | None => inl tt
  end.

Lemma bitcoin_output_script_hash_sem environment a :
  @bitcoin_output_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (bitcoin_output_script_hash_result environment a).
Proof.
  assert (H : @bitcoin_output_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Bitcoin.sem Bitcoin.OutputScriptHash a environment) by reflexivity.
  rewrite H. unfold Bitcoin.sem, bitcoin_output_script_hash_result. cbv zeta.
  destruct (nth_error (sigTxOut (Bitcoin.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition bitcoin_output_script_hash_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _scriptPubKey
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma bitcoin_output_script_hash_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_output_script_hash
    (bitcoin_indexed_rest _t'5 _t'6 _numOutputs
      (bitcoin_indexed_then_ptr _t'3 _t'4 _output _sigOutput bitcoin_output_script_hash_pexpr
        _writeHash (Tstruct _sha256_midstate noattr)) (bitcoin_skip_stmt 256)).
Proof. repeat split; try reflexivity. apply bitcoin_ptr_disjoint. Qed.

Theorem bitcoin_output_script_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_output_script_hash bitcoin_ge Bitcoin.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxOut (Bitcoin.envTx e))
      (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) 40 8 8 456)
    (fun a environment => @bitcoin_output_script_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_indexed_ptr_local (fun e => sigTxOut (Bitcoin.envTx e)) 256
    (fun txo => hash_cells (script_hash_words txo))
    (fun m b ofs txo => uint32_array_at m b ofs (script_hash_words txo)) Word256
    _t'5 _t'6 _t'3 _t'4 _numOutputs _output _sigOutput _writeHash (Tstruct _sha256_midstate noattr)
    456 8 40 8 32 bitcoin_output_script_hash_pexpr f_writeHash f_simplicity_bitcoin_output_script_hash
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) _ ltac:(reflexivity) ltac:(intros bl; reflexivity)
    bitcoin_writeHash_symbol bitcoin_writeHash_funct ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numOutputs bitcoin_bitcoinTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ bitcoin_output_script_hash_shape ltac:(reflexivity) _ _).
  - intros x. unfold script_hash_words. rewrite hash_cells_length. rewrite (hash256_len (byteStringHash (txoScript x))).
    reflexivity.
  - intros m1 m2 b ofs x Hr Hl. eapply uint32_array_at_mono; [|exact Hr|exact Hl].
    unfold script_hash_words. exact (hash256_len _).
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    destruct (eval_bitcoin_writeHash_layout m' bin ofs bd dbase bw outedge cur (script_hash_words x)
      ltac:(unfold script_hash_words; exact (hash256_len _)) H0 ltac:(lia) HSep Hr HF) as (me & HC & HE).
    exists me. split; [exact HC|exact HE].
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold bitcoin_output_script_hash_pexpr.
    exact (eval_bitcoin_elem_field_addr e le' m' _t'4 _i _sigOutput 40 _scriptPubKey 8 _sha256_midstate bin inbase r
      bitcoin_sizeof_sigOutput bitcoin_sigOutput_scriptPubKey H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (bitcoin_output_script_hash_result environment a). split.
    + apply bitcoin_output_script_hash_sem.
    + unfold bitcoin_output_script_hash_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxOut (Bitcoin.envTx environment)) (Z.to_nat (toZ a))) as [txo|].
      * rewrite encode_sum_inr_hash. unfold script_hash_words. rewrite encode_from_hash256. reflexivity.
      * vm_compute. reflexivity.
Qed.

(** * input_prev_outpoint *)

Lemma encode_inr_prod_word (w : Ty.tySem Word256) (ix : Ty.tySem Word32) :
  @encode (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32)) (inr (w, ix)) =
    Some true :: (@encode Word256 w ++ @encode Word32 ix).
Proof. reflexivity. Qed.

Lemma bitcoin_prevOutpoint_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _prevOutpoint = Some (bitcoin_symbol_block _prevOutpoint).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_prevOutpoint_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Vptr (bitcoin_symbol_block _prevOutpoint) Ptrofs.zero) = Some (Internal f_prevOutpoint).
Proof. vm_compute; reflexivity. Qed.

Definition bitcoin_input_prev_outpoint_spec {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32)) :=
  Primitive.Combinators.prim Bitcoin.InputPrevOutpoint.

Definition outpoint_ix (op : outpoint) : int64 := Int64.repr (Int.unsigned (opIndex op)).

Definition bitcoin_input_prev_outpoint_result (environment : Bitcoin.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32)) :=
  match nth_error (sigTxIn (Bitcoin.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txi => inr (from_hash256 (opHash (sigTxiPreviousOutpoint txi)),
      @fromZ (WordToZ 5) (Int.unsigned (opIndex (sigTxiPreviousOutpoint txi))))
  | None => inl tt
  end.

Lemma bitcoin_input_prev_outpoint_sem environment a :
  @bitcoin_input_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (bitcoin_input_prev_outpoint_result environment a).
Proof.
  assert (H : @bitcoin_input_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Bitcoin.sem Bitcoin.InputPrevOutpoint a environment) by reflexivity.
  rewrite H. unfold Bitcoin.sem, bitcoin_input_prev_outpoint_result. cbv zeta.
  destruct (nth_error (sigTxIn (Bitcoin.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition bitcoin_input_prev_outpoint_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _prevOutpoint
    (Tstruct _outpoint noattr)) (tptr (Tstruct _outpoint noattr)).

Lemma bitcoin_input_prev_outpoint_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_input_prev_outpoint
    (bitcoin_indexed_rest _t'5 _t'6 _numInputs
      (bitcoin_indexed_then_ptr _t'3 _t'4 _input _sigInput bitcoin_input_prev_outpoint_pexpr
        _prevOutpoint (Tstruct _outpoint noattr)) (bitcoin_skip_stmt 288)).
Proof. repeat split; try reflexivity. apply bitcoin_ptr_disjoint. Qed.

Definition outpoint_words (txi : sigTxInput) : list int := hash256_reg (opHash (sigTxiPreviousOutpoint txi)).

Definition outpoint_rep (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  uint32_array_at m b ofs (outpoint_words txi) /\
  Mem.load Mint64 m b (ofs + 32) = Some (Vlong (outpoint_ix (sigTxiPreviousOutpoint txi))).

Definition outpoint_pcells (txi : sigTxInput) : list Cell :=
  bitcoin_outpoint_cells (outpoint_words txi) (outpoint_ix (sigTxiPreviousOutpoint txi)).

Lemma outpoint_pcells_length txi : Z.of_nat (length (outpoint_pcells txi)) = 288.
Proof.
  unfold outpoint_pcells, bitcoin_outpoint_cells. rewrite app_length, Nat2Z.inj_add.
  rewrite (hash_cells_length_Z (outpoint_words txi) (hash256_len (opHash (sigTxiPreviousOutpoint txi)))).
  rewrite encode_length. reflexivity.
Qed.

Theorem bitcoin_input_prev_outpoint_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_prev_outpoint bitcoin_ge Bitcoin.env Word32
    (Ty.Sum Ty.Unit (Ty.Prod Word256 Word32))
    (indexed_ptr_rep (fun e => sigTxIn (Bitcoin.envTx e)) outpoint_rep 160 64 0 448)
    (fun a environment => @bitcoin_input_prev_outpoint_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_indexed_ptr_local (fun e => sigTxIn (Bitcoin.envTx e)) 288 outpoint_pcells outpoint_rep
    (Ty.Prod Word256 Word32)
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _prevOutpoint (Tstruct _outpoint noattr)
    448 0 160 64 40 bitcoin_input_prev_outpoint_pexpr f_prevOutpoint f_simplicity_bitcoin_input_prev_outpoint
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) outpoint_pcells_length ltac:(reflexivity) ltac:(intros bl; reflexivity)
    bitcoin_prevOutpoint_symbol bitcoin_prevOutpoint_funct ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numInputs bitcoin_bitcoinTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ bitcoin_input_prev_outpoint_shape ltac:(reflexivity) _ _).
  - intros m1 m2 b ofs x [Hr Hix] Hl. split.
    + eapply uint32_array_at_mono; [unfold outpoint_words; exact (hash256_len _)|exact Hr|].
      intros chunk o v H1 H2. apply Hl; [exact H1|lia].
    + apply (Hl Mint64 (ofs + 32) _); [lia|change (size_chunk Mint64) with 8; lia|exact Hix].
  - intros bd dbase bw outedge m' bin ofs x cur [Hr Hix] H0 HM HSep HF.
    destruct (eval_bitcoin_prevOutpoint_layout m' bin ofs bd dbase bw outedge cur (outpoint_words x)
      (outpoint_ix (sigTxiPreviousOutpoint x))
      ltac:(unfold outpoint_words; exact (hash256_len _)) H0 ltac:(lia) HSep Hr Hix HF) as (me & HC & HE).
    exists me. split; [exact HC|exact HE].
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold bitcoin_input_prev_outpoint_pexpr.
    exact (eval_bitcoin_elem_field_addr e le' m' _t'4 _i _sigInput 160 _prevOutpoint 64 _outpoint bin inbase r
      bitcoin_sizeof_sigInput bitcoin_sigInput_prevOutpoint H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (bitcoin_input_prev_outpoint_result environment a). split.
    + apply bitcoin_input_prev_outpoint_sem.
    + unfold bitcoin_input_prev_outpoint_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxIn (Bitcoin.envTx environment)) (Z.to_nat (toZ a))) as [txi|].
      * unfold outpoint_pcells, bitcoin_outpoint_cells, outpoint_words, outpoint_ix.
        rewrite encode_inr_prod_word. f_equal.
        rewrite encode_from_hash256. f_equal.
        rewrite decode_wide32_unsigned.
        -- reflexivity.
        -- pose proof (Int.unsigned_range (opIndex (sigTxiPreviousOutpoint txi))) as H.
           change Int.modulus with 4294967296 in H. exact H.
      * vm_compute. reflexivity.
Qed.
