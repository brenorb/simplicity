(** Elements per-output proof-hash getters ([output_surjection_proof],
    [output_range_proof]) against primitives OutputSurjectionProof and
    OutputRangeProof: SHA-256 of the asset surjection proof / amount range
    proof (the empty string for an explicit value).  Instances of the generic
    indexed-pointer proof; the element relation is an initial representation
    requirement on the environment. *)
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
Require Import C.jet_elements_indexed_ptr_jets.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Lemma elements_sigOutput_surjectionProofHash : elements_field_at _sigOutput _surjectionProofHash 36.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_sigOutput_rangeProofHash : elements_field_at _sigOutput _rangeProofHash 68.
Proof. vm_compute; reflexivity. Qed.

(** * output_surjection_proof *)

Definition elements_output_surjection_proof_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word256) :=
  Primitive.Combinators.prim Elements.OutputSurjectionProof.

Definition surjection_proof_hash_words (txo : txOutput) : list int :=
  hash256_reg (byteStringHash (viewPrf (txoAsset txo))).

Definition elements_output_surjection_proof_result (environment : Elements.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txo => inr (from_hash256 (byteStringHash (viewPrf (txoAsset txo))))
  | None => inl tt
  end.

Lemma elements_output_surjection_proof_sem environment a :
  @elements_output_surjection_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (elements_output_surjection_proof_result environment a).
Proof.
  assert (H : @elements_output_surjection_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.OutputSurjectionProof a environment) by reflexivity.
  rewrite H. unfold Elements.sem, elements_output_surjection_proof_result. cbv zeta.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition elements_output_surjection_proof_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _surjectionProofHash
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma elements_output_surjection_proof_shape :
  elements_wrapper_shape f_simplicity_output_surjection_proof
    (elements_indexed_rest _t'5 _t'6 _numOutputs
      (elements_indexed_then_ptr _t'3 _t'4 _output _sigOutput elements_output_surjection_proof_pexpr
        _writeHash (Tstruct _sha256_midstate noattr)) (elements_skip_stmt 256)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_output_surjection_proof_local_spec :
  application_jet_local_spec_sep f_simplicity_output_surjection_proof elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => uint32_array_at m b ofs (surjection_proof_hash_words txo)) 248 36 8 704)
    (fun a environment => @elements_output_surjection_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxOut (Elements.envTx e)) 256
    (fun txo => hash_cells (surjection_proof_hash_words txo))
    (fun m b ofs txo => uint32_array_at m b ofs (surjection_proof_hash_words txo)) Word256
    _t'5 _t'6 _t'3 _t'4 _numOutputs _output _sigOutput _writeHash (Tstruct _sha256_midstate noattr)
    704 8 248 36 32 elements_output_surjection_proof_pexpr f_writeHash f_simplicity_output_surjection_proof
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) _ ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_writeHash_symbol elements_writeHash_funct ltac:(reflexivity)
    elements_elementsTransaction_numOutputs elements_elementsTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_output_surjection_proof_shape ltac:(reflexivity) _ _).
  - intros x. unfold surjection_proof_hash_words. rewrite hash_cells_length. rewrite (hash256_len (byteStringHash (viewPrf (txoAsset x)))).
    reflexivity.
  - intros m1 m2 b ofs x Hr Hl. eapply uint32_array_at_mono; [|exact Hr|exact Hl].
    unfold surjection_proof_hash_words. exact (hash256_len _).
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    destruct (eval_elements_writeHash_layout m' bin ofs bd dbase bw outedge cur (surjection_proof_hash_words x)
      ltac:(unfold surjection_proof_hash_words; exact (hash256_len _)) H0 ltac:(lia) HSep Hr HF) as (me & HC & HE).
    exists me. split; [exact HC|exact HE].
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_output_surjection_proof_pexpr.
    exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigOutput 248 _surjectionProofHash 36 _sha256_midstate bin inbase r
      elements_sizeof_sigOutput elements_sigOutput_surjectionProofHash H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (elements_output_surjection_proof_result environment a). split.
    + apply elements_output_surjection_proof_sem.
    + unfold elements_output_surjection_proof_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|].
      * rewrite encode_sum_inr_hash. unfold surjection_proof_hash_words. rewrite encode_from_hash256. reflexivity.
      * vm_compute. reflexivity.
Qed.


(** * output_range_proof *)

Definition elements_output_range_proof_spec {alg : Primitive.Algebra} : alg Word32 (Ty.Sum Ty.Unit Word256) :=
  Primitive.Combinators.prim Elements.OutputRangeProof.

Definition range_proof_hash_words (txo : txOutput) : list int :=
  hash256_reg (byteStringHash (viewPrf (txoAmount txo))).

Definition elements_output_range_proof_result (environment : Elements.env) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
  | Some txo => inr (from_hash256 (byteStringHash (viewPrf (txoAmount txo))))
  | None => inl tt
  end.

Lemma elements_output_range_proof_sem environment a :
  @elements_output_range_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Some (elements_output_range_proof_result environment a).
Proof.
  assert (H : @elements_output_range_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment =
    Elements.sem Elements.OutputRangeProof a environment) by reflexivity.
  rewrite H. unfold Elements.sem, elements_output_range_proof_result. cbv zeta.
  destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition elements_output_range_proof_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigOutput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _rangeProofHash
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma elements_output_range_proof_shape :
  elements_wrapper_shape f_simplicity_output_range_proof
    (elements_indexed_rest _t'5 _t'6 _numOutputs
      (elements_indexed_then_ptr _t'3 _t'4 _output _sigOutput elements_output_range_proof_pexpr
        _writeHash (Tstruct _sha256_midstate noattr)) (elements_skip_stmt 256)).
Proof. repeat split; try reflexivity. apply elements_ptr_disjoint. Qed.

Theorem elements_output_range_proof_local_spec :
  application_jet_local_spec_sep f_simplicity_output_range_proof elements_ge Elements.env Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep (fun e => sigTxOut (Elements.envTx e))
      (fun m b ofs txo => uint32_array_at m b ofs (range_proof_hash_words txo)) 248 68 8 704)
    (fun a environment => @elements_output_range_proof_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_ptr_local (fun e => sigTxOut (Elements.envTx e)) 256
    (fun txo => hash_cells (range_proof_hash_words txo))
    (fun m b ofs txo => uint32_array_at m b ofs (range_proof_hash_words txo)) Word256
    _t'5 _t'6 _t'3 _t'4 _numOutputs _output _sigOutput _writeHash (Tstruct _sha256_midstate noattr)
    704 8 248 68 32 elements_output_range_proof_pexpr f_writeHash f_simplicity_output_range_proof
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) _ ltac:(reflexivity) ltac:(intros bl; reflexivity)
    elements_writeHash_symbol elements_writeHash_funct ltac:(reflexivity)
    elements_elementsTransaction_numOutputs elements_elementsTransaction_output
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ elements_output_range_proof_shape ltac:(reflexivity) _ _).
  - intros x. unfold range_proof_hash_words. rewrite hash_cells_length. rewrite (hash256_len (byteStringHash (viewPrf (txoAmount x)))).
    reflexivity.
  - intros m1 m2 b ofs x Hr Hl. eapply uint32_array_at_mono; [|exact Hr|exact Hl].
    unfold range_proof_hash_words. exact (hash256_len _).
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    destruct (eval_elements_writeHash_layout m' bin ofs bd dbase bw outedge cur (range_proof_hash_words x)
      ltac:(unfold range_proof_hash_words; exact (hash256_len _)) H0 ltac:(lia) HSep Hr HF) as (me & HC & HE).
    exists me. split; [exact HC|exact HE].
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold elements_output_range_proof_pexpr.
    exact (eval_elements_elem_field_addr e le' m' _t'4 _i _sigOutput 248 _rangeProofHash 68 _sha256_midstate bin inbase r
      elements_sizeof_sigOutput elements_sigOutput_rangeProofHash H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (elements_output_range_proof_result environment a). split.
    + apply elements_output_range_proof_sem.
    + unfold elements_output_range_proof_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txo|].
      * rewrite encode_sum_inr_hash. unfold range_proof_hash_words. rewrite encode_from_hash256. reflexivity.
      * vm_compute. reflexivity.
Qed.

