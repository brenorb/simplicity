(** Actual Bitcoin current_script_hash and current_script_sig_hash jets against
    the literal canonical [CurrentIndex >>> assert InputScriptHash] (resp.
    InputScriptSigHash) over the extended primitive signature. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_encoding C.jet_input_layout C.jet_uint32_array_init C.jets_bitcoin C.jet_bitcoin_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_version_exec C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_effects.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_index_eval C.jet_bitcoin_indexed_exec.
Require Import C.jet_bitcoin_current_exec C.jet_bitcoin_current_spec C.jet_bitcoin_current_ptr.
Require Import C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_ptr C.jet_bitcoin_hash_write C.jet_bitcoin_hash_helpers.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_indexed_scalar_jets C.jet_bitcoin_indexed_ptr_jets C.jet_bitcoin_current_ptr_jets.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_ext_ptr_jets C.jet_bitcoin_ext_current_spec.

Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Set Default Timeout 60.


Definition bitcoin_current_script_hash_pexpr : expr :=
  Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _sigInput noattr))) (Etempvar _t'3 tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _txo (Tstruct _sigOutput noattr))
    _scriptPubKey (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma bitcoin_current_script_hash_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_current_script_hash
    (bitcoin_current_ptr_rest _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput
      bitcoin_current_script_hash_pexpr _writeHash (Tstruct _sha256_midstate noattr)).
Proof. repeat split; try reflexivity. apply bitcoin_current_ptr_disjoint. Qed.

Theorem bitcoin_current_script_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_current_script_hash bitcoin_ge ext_environment Ty.Unit
    Word256
    (current_ptr_rep extInScriptHash ext_ix hash_elem_rep 160 112 0 448)
    (fun a environment => @bitcoin_current_script_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_current_ptr_local extInScriptHash ext_ix 256
    (fun h => hash_cells (hash256_reg h)) hash_elem_rep Word256
    _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput _writeHash (Tstruct _sha256_midstate noattr)
    448 0 160 112 32 bitcoin_current_script_hash_pexpr f_writeHash f_simplicity_bitcoin_current_script_hash
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) ltac:(reflexivity) ltac:(intros bl; reflexivity)
    bitcoin_writeHash_symbol bitcoin_writeHash_funct ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numInputs bitcoin_bitcoinTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ bitcoin_current_script_hash_shape ltac:(reflexivity) _ _ hash_cells_len_256).
  - intros m1 m2 b ofs x Hr Hl. eapply hash_elem_rep_mono; [exact Hr|exact Hl].
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    exact (hash_elem_pay bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF).
  - intros e le' m' bin inbase ixv H2 H3 Hi0 HM. unfold bitcoin_current_script_hash_pexpr.
    exact (eval_bitcoin_elem_nested_field_addr e le' m' _t'2 _t'3 _sigInput 160 _txo 104 _sigOutput
      _scriptPubKey 8 _sha256_midstate bin inbase ixv bitcoin_sizeof_sigInput bitcoin_sigInput_txo
      bitcoin_sigOutput_scriptPubKey H2 H3 Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros environment. destruct (bitcoin_current_script_hash_sem environment) as (h & Hn & Hs).
    exists h. eexists. split; [exact Hn|]. split; [exact Hs|].
    rewrite encode_from_hash256. reflexivity.
Qed.

Definition bitcoin_current_script_sig_hash_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _sigInput noattr))) (Etempvar _t'3 tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _scriptSigHash
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma bitcoin_current_script_sig_hash_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_current_script_sig_hash
    (bitcoin_current_ptr_rest _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput
      bitcoin_current_script_sig_hash_pexpr _writeHash (Tstruct _sha256_midstate noattr)).
Proof. repeat split; try reflexivity. apply bitcoin_current_ptr_disjoint. Qed.

Theorem bitcoin_current_script_sig_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_current_script_sig_hash bitcoin_ge ext_environment Ty.Unit
    Word256
    (current_ptr_rep extInScriptSigHash ext_ix hash_elem_rep 160 32 0 448)
    (fun a environment => @bitcoin_current_script_sig_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_current_ptr_local extInScriptSigHash ext_ix 256
    (fun h => hash_cells (hash256_reg h)) hash_elem_rep Word256
    _t'1 _t'2 _t'3 _t'4 _t'5 _t'6 _input _numInputs _sigInput _writeHash (Tstruct _sha256_midstate noattr)
    448 0 160 32 32 bitcoin_current_script_sig_hash_pexpr f_writeHash f_simplicity_bitcoin_current_script_sig_hash
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) ltac:(reflexivity) ltac:(intros bl; reflexivity)
    bitcoin_writeHash_symbol bitcoin_writeHash_funct ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numInputs bitcoin_bitcoinTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ bitcoin_current_script_sig_hash_shape ltac:(reflexivity) _ _ hash_cells_len_256).
  - intros m1 m2 b ofs x Hr Hl. eapply hash_elem_rep_mono; [exact Hr|exact Hl].
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    exact (hash_elem_pay bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF).
  - intros e le' m' bin inbase ixv H2 H3 Hi0 HM. unfold bitcoin_current_script_sig_hash_pexpr.
    exact (eval_bitcoin_elem_field_addr e le' m' _t'2 _t'3 _sigInput 160 _scriptSigHash 32 _sha256_midstate bin inbase ixv
      bitcoin_sizeof_sigInput bitcoin_sigInput_scriptSigHash H2 H3 Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros environment. destruct (bitcoin_current_script_sig_hash_sem environment) as (h & Hn & Hs).
    exists h. eexists. split; [exact Hn|]. split; [exact Hs|].
    rewrite encode_from_hash256. reflexivity.
Qed.
