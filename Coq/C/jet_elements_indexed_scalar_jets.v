(** Actual Elements input_sequence jet against primitive InputSequence, from
    the generic indexed-scalar proof (ported from the Bitcoin unit). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_encoding C.jet_input_layout C.jets_elements C.jet_elements_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_elements_version_exec C.jet_elements_field_eval C.jet_elements_wrapper.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_index_eval.
Require Import C.jet_elements_indexed_exec C.jet_elements_indexed_then C.jet_elements_indexed_scalar.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Definition elements_elem_expr (sid field : ident) : expr :=
  Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct sid noattr))) (Etempvar _i tulong)
    (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) field tulong.

Definition elements_scalar_rest arr sid field wid nb : statement :=
  elements_indexed_rest _t'6 _t'7 (if Pos.eqb arr _input then _numInputs else _numOutputs)
    (elements_indexed_then _t'3 _t'4 _t'5 arr sid (elements_elem_expr sid field) wid)
    (elements_skip_stmt nb).

Lemma elements_scalar_disjoint : list_disjoint [_dst; _src; _env] [_i; _t'2; _t'1; _t'7; _t'6; _t'5; _t'4; _t'3].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma elements_input_sequence_shape :
  elements_wrapper_shape f_simplicity_input_sequence
    (elements_scalar_rest _input _sigInput _sequence _simplicity_write32 32).
Proof. repeat split; try reflexivity. apply elements_scalar_disjoint. Qed.

(** * input_sequence *)

Definition elements_input_sequence_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word32) :=
  Primitive.Combinators.prim Elements.InputSequence.

Lemma elements_input_sequence_spec_parametric : Primitive.Parametric (@elements_input_sequence_spec).
Proof. intros alg1 alg2 R. apply prim_Parametric. Qed.

Definition elements_input_sequence_specv (txi : sigTxInput) : Ty.tySem (Word (wide_log W32)) :=
  @fromZ (WordToZ 5) (Int.unsigned (sigTxiSequence txi)).

Lemma elements_input_sequence_sem environment a :
  @elements_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (indexed_scalar_result W32 (sigTxIn (Elements.envTx environment))
      elements_input_sequence_specv a).
Proof.
  assert (H : @elements_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.InputSequence a environment) by reflexivity.
  rewrite H. unfold Elements.sem, indexed_scalar_result, elements_input_sequence_specv. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
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

Theorem elements_input_sequence_local_spec :
  application_jet_local_spec_sep f_simplicity_input_sequence elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word32)
    (indexed_scalar_rep (fun e => sigTxIn (Elements.envTx e)) (fun txi => Int.unsigned (sigTxiSequence txi))
      544 248 0 696)
    (fun a environment => @elements_input_sequence_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_scalar_local W32 (fun e => sigTxIn (Elements.envTx e))
    (fun txi => Int.unsigned (sigTxiSequence txi)) elements_input_sequence_specv
    _t'6 _t'7 _t'3 _t'4 _t'5 _numInputs _input _sigInput _simplicity_write32 696 0 544 248
    (elements_elem_expr _sigInput _sequence) jets.f_simplicity_write32 f_simplicity_input_sequence
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(helper_in) ltac:(reflexivity) ltac:(intros bl; reflexivity) ltac:(reflexivity)
    elements_elementsTransaction_numInputs elements_elementsTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ elements_input_sequence_shape _ _).
  - intros x. unfold elements_input_sequence_specv. apply decode_wide32_unsigned.
    pose proof (Int.unsigned_range (sigTxiSequence x)) as H. change Int.modulus with 4294967296 in H. exact H.
  - intros e le' m' bin inbase r v H4 HI Hi0 HM HL. unfold elements_elem_expr.
    exact (eval_elements_elem_field e le' m' _t'4 _sigInput 544 _sequence 248 bin inbase r v
      elements_sizeof_sigInput elements_sigInput_sequence H4 HI Hi0 ltac:(split; lia) ltac:(lia) HM HL).
  - intros a environment. apply elements_input_sequence_sem.
Qed.
