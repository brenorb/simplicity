(** Full original public SWU initialized-frame contract. This is conditional
    on the deferred original CTZ contract, not accepted coverage yet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
  C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
  C.jet_secp_swu_literal C.jet_secp_swu_startup C.jet_secp_swu_public_call C.jet_secp_initialized_contract.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_swu encode.

Theorem swu_initialized_local_spec_from_count_calls :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  secp_jet_initialized_local_spec swu_startup f_simplicity_swu (Word 8)
    (Ty.Prod (Word 8) (Word 8)) (@literal_swu Alg.CoreFunSem).
Proof.
  intros Count env m bd base bs sbase bi bw edge outedge cursor rc t
    Ready Base Align Source RC Max Input Output.
  change (rc+256<=Int64.max_unsigned) in Max.
  change (write_frame_at m bd base bw outedge cursor 512) in Output.
  rewrite encode_word in Input.
  destruct (eval_swu_literal_public env m bd base bs sbase bw outedge cursor 512 bi edge rc t
    Count Ready Output ltac:(lia) Base Align Source Input RC Max)
    as (mf & Call & Final & Frame & ReadyF & ReadOnly).
  destruct Final as (Valid & Forward & Length & (Cells & Prefix & Fields & Loads & Perms) & Written).
  rewrite encode_length in Fields,Loads.
  exists mf;split;[exact Call|];split;[exact Cells|];split;[exact Prefix|];split;[exact Fields|];split;[|exact ReadyF].
  intros chunk b ofs ValidB FrameOther OutputOther.
  destruct (Pos.eq_dec b bd) as [D|D];
    [apply Loads;[split;[left;exact D|exact ValidB]|assumption|assumption]|].
  destruct (Pos.eq_dec b bw) as [W|W];
    [apply Loads;[split;[right;left;exact W|exact ValidB]|assumption|assumption]|].
  destruct (Pos.eq_dec b bi) as [I|I];
    [apply Loads;[split;[right;right;exact I|exact ValidB]|assumption|assumption]|].
  apply (proj1 Frame);[exact ValidB|];intros pos Range.
  unfold extA,fext;intros [[Same | [Same | Same] ] _];contradiction.
Qed.
