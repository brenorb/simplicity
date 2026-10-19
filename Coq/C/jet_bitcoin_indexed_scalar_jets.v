(** Actual Bitcoin input_sequence and output_value jets against the literal
    canonical primitives InputSequence / OutputValue, from the generic
    indexed-scalar proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_encoding C.jet_input_layout C.jets_bitcoin C.jet_bitcoin_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_version_exec C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_index_eval.
Require Import C.jet_bitcoin_indexed_exec C.jet_bitcoin_indexed_then C.jet_bitcoin_indexed_scalar.
Require Import C.jet_bitcoin_input_value_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Definition bitcoin_elem_expr (sid field : ident) : expr :=
  Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct sid noattr))) (Etempvar _i tulong)
    (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) field tulong.

Definition bitcoin_scalar_rest arr sid field wid nb : statement :=
  bitcoin_indexed_rest _t'6 _t'7 (if Pos.eqb arr _input then _numInputs else _numOutputs)
    (bitcoin_indexed_then _t'3 _t'4 _t'5 arr sid (bitcoin_elem_expr sid field) wid)
    (bitcoin_skip_stmt nb).

Lemma bitcoin_scalar_disjoint : list_disjoint [_dst; _src; _env] [_i; _t'2; _t'1; _t'7; _t'6; _t'5; _t'4; _t'3].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma bitcoin_input_sequence_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_input_sequence
    (bitcoin_scalar_rest _input _sigInput _sequence _simplicity_write32 32).
Proof. repeat split; try reflexivity. apply bitcoin_scalar_disjoint. Qed.

Lemma bitcoin_output_value_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_output_value
    (bitcoin_scalar_rest _output _sigOutput _value _simplicity_write64 64).
Proof. repeat split; try reflexivity. apply bitcoin_scalar_disjoint. Qed.

(** * input_sequence *)

Definition bitcoin_input_sequence_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word32) :=
  Primitive.Combinators.prim Bitcoin.InputSequence.

Lemma bitcoin_input_sequence_spec_parametric : Primitive.Parametric (@bitcoin_input_sequence_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Definition bitcoin_input_sequence_specv (txi : sigTxInput) : Ty.tySem (Word (wide_log W32)) :=
  @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence txi)).

Lemma bitcoin_input_sequence_sem environment a :
  @bitcoin_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (indexed_scalar_result W32 (sigTxIn (Bitcoin.envTx environment))
      bitcoin_input_sequence_specv a).
Proof.
  assert (H : @bitcoin_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Bitcoin.sem Bitcoin.InputSequence a environment) by reflexivity.
  rewrite H. unfold Bitcoin.sem, indexed_scalar_result, bitcoin_input_sequence_specv. cbv zeta.
  destruct (nth_error (sigTxIn (Bitcoin.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Lemma decode_wide32_unsigned z :
  0 <= z < 4294967296 ->
  decode_wide W32 (Int64.zero_ext (wide_bits W32) (Int64.repr z)) = @fromZ (WordToZ 5) z.
Proof.
  intros Hz. unfold decode_wide. change (wide_log W32) with 5%nat. change (wide_bits W32) with 32.
  rewrite Int64.zero_ext_mod by (change Int64.zwordsize with 64; lia).
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  change (two_p 32) with 4294967296. rewrite Z.mod_small by lia. reflexivity.
Qed.

Theorem bitcoin_input_sequence_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_sequence bitcoin_ge Bitcoin.env Word32
    (Ty.Sum Ty.Unit Word32)
    (indexed_scalar_rep (fun e => sigTxIn (Bitcoin.envTx e)) (fun txi => Int.unsigned (sigTxiSequence txi))
      160 144 0 448)
    (fun a environment => @bitcoin_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_indexed_scalar_local W32 (fun e => sigTxIn (Bitcoin.envTx e))
    (fun txi => Int.unsigned (sigTxiSequence txi)) bitcoin_input_sequence_specv
    _t'6 _t'7 _t'3 _t'4 _t'5 _numInputs _input _sigInput _simplicity_write32 448 0 160 144
    (bitcoin_elem_expr _sigInput _sequence) jets.f_simplicity_write32 f_simplicity_bitcoin_input_sequence
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(helper_in) ltac:(reflexivity) ltac:(intros bl; reflexivity) ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numInputs bitcoin_bitcoinTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ bitcoin_input_sequence_shape _ _).
  - intros x. unfold bitcoin_input_sequence_specv. apply decode_wide32_unsigned.
    pose proof (Int.unsigned_range (sigTxiSequence x)) as H. change Int.modulus with 4294967296 in H. exact H.
  - intros e le' m' bin inbase r v H4 HI Hi0 HM HL. unfold bitcoin_elem_expr.
    exact (eval_bitcoin_elem_field e le' m' _t'4 _sigInput 160 _sequence 144 bin inbase r v
      bitcoin_sizeof_sigInput bitcoin_sigInput_sequence H4 HI Hi0 ltac:(split; lia) ltac:(lia) HM HL).
  - intros a environment. apply bitcoin_input_sequence_sem.
Qed.

(** * output_value *)

Definition bitcoin_output_value_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word64) :=
  Primitive.Combinators.prim Bitcoin.OutputValue.

Lemma bitcoin_output_value_spec_parametric : Primitive.Parametric (@bitcoin_output_value_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Definition bitcoin_output_value_specv (txo : txOutput) : Ty.tySem (Word (wide_log W64)) :=
  @fromZ (WordToZ 6) (Int64.signed (txoValue txo)).

Lemma bitcoin_output_value_sem environment a :
  @bitcoin_output_value_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (indexed_scalar_result W64 (sigTxOut (Bitcoin.envTx environment))
      bitcoin_output_value_specv a).
Proof.
  assert (H : @bitcoin_output_value_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Bitcoin.sem Bitcoin.OutputValue a environment) by reflexivity.
  rewrite H. unfold Bitcoin.sem, indexed_scalar_result, bitcoin_output_value_specv. cbv zeta.
  destruct (nth_error (sigTxOut (Bitcoin.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Theorem bitcoin_output_value_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_output_value bitcoin_ge Bitcoin.env Word32
    (Ty.Sum Ty.Unit Word64)
    (indexed_scalar_rep (fun e => sigTxOut (Bitcoin.envTx e)) (fun txo => Int64.signed (txoValue txo))
      40 0 8 456)
    (fun a environment => @bitcoin_output_value_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_indexed_scalar_local W64 (fun e => sigTxOut (Bitcoin.envTx e))
    (fun txo => Int64.signed (txoValue txo)) bitcoin_output_value_specv
    _t'6 _t'7 _t'3 _t'4 _t'5 _numOutputs _output _sigOutput _simplicity_write64 456 8 40 0
    (bitcoin_elem_expr _sigOutput _value) jets.f_simplicity_write64 f_simplicity_bitcoin_output_value
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(helper_in) ltac:(reflexivity) ltac:(intros bl; reflexivity) ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numOutputs bitcoin_bitcoinTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ bitcoin_output_value_shape _ _).
  - intros x. unfold bitcoin_output_value_specv. rewrite Int64.repr_signed.
    apply decode_wide64_money.
    pose proof (txoValue_bound x) as HB0. unfold MAX_MONEY in HB0. lia.
  - intros e le' m' bin inbase r v H4 HI Hi0 HM HL. unfold bitcoin_elem_expr.
    exact (eval_bitcoin_elem_field e le' m' _t'4 _sigOutput 40 _value 0 bin inbase r v
      bitcoin_sizeof_sigOutput bitcoin_sigOutput_value H4 HI Hi0 ltac:(split; lia) ltac:(lia) HM HL).
  - intros a environment. apply bitcoin_output_value_sem.
Qed.
