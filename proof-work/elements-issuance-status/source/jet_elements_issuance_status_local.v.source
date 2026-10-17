(** Original simplicity_issuance -> literal primitive-based issuance program.
    Initial enum, pointer/count and valid separated frames are represented;
    no execution, result, cached hash or nonzero-issuance premise is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_elements_issuance_status_spec C.jet_elements_issuance_status_exec.
Require Import C.jet_elements_indexed_tag3_exec C.jet_elements_indexed_tag3_gen.
Require Import C.jet_elements_indexed_ptr C.jet_elements_index_eval C.jet_elements_wrapper.
Require Import C.jet_elements_linkage C.jets_elements C.jet_word_repr C.jet_encoding.
Require Import C.jet_elements_indexed_scalar.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Lemma elements_issuance_status_shape :
  elements_wrapper_shape f_simplicity_issuance
    (elements_indexed_rest_tag3 _t'8 _t'9 _numInputs issuance_status_then_stmt (elements_skip_stmt 2)).
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma elements_issuance_status_encoding a environment :
  @encode issuance_status_type (issuance_status_result (sigTxIn (Elements.envTx environment)) a) =
    indexed_ptr_cells (sigTxIn (Elements.envTx environment)) 2 issuance_status_pcells a.
Proof.
  unfold issuance_status_result, indexed_ptr_cells. change (toZ32 a) with (toZ a).
  destruct (nth_error (sigTxIn (Elements.envTx environment)) (Z.to_nat (toZ a))) as [txi | ].
  - unfold issuance_status_pcells, issuance_status_of_input.
    destruct (sigTxiIssuance txi) as [[n | r] | ]; reflexivity.
  - reflexivity.
Qed.

Theorem elements_issuance_status_local_spec :
  application_jet_local_spec_sep f_simplicity_issuance elements_ge Elements.env Word32 issuance_status_type
    (indexed_ptr_rep (fun e => sigTxIn (Elements.envTx e)) issuance_status_enum_rep 544 0 0 696)
    (fun a environment => @elements_issuance_status_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_indexed_gen_local_tag3 (fun e => sigTxIn (Elements.envTx e)) 2 issuance_status_pcells
    issuance_status_enum_rep issuance_status_payload _t'8 _t'9 _numInputs 696 0 544
    issuance_status_then_stmt f_simplicity_issuance
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate) ltac:(lia)
    issuance_status_pcells_length elements_elementsTransaction_numInputs
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ elements_issuance_status_shape ltac:(reflexivity) _ _).
  - intros m1 m2 b ofs x HT HLoads. unfold issuance_status_enum_rep in *.
    apply (HLoads Mint32 (ofs + 528) _); [lia|change (size_chunk Mint32) with 4; lia|exact HT].
  - intros bd dbase bw edge bl le m x be ebase bt txbase bin inbase r cur
      HI HD HE He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HT S1 S2 S3 HF.
    exact (exec_issuance_status_then bl le m x be ebase bt txbase bin inbase r bd dbase bw edge cur
      HI HD HE He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HT S3 HF).
  - intros a environment.
    exists (issuance_status_result (sigTxIn (Elements.envTx environment)) a).
    split; [apply elements_issuance_status_sem|apply elements_issuance_status_encoding].
Qed.
