(** Existing full initialized local contract for the original public fe_invert
    jet. CTZ remains explicit; this is not an accepted coverage row yet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
 C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_invert_literal C.jet_secp_modinfo_fe_caller C.jet_secp_fe_invert_lifecycle C.jet_secp_initialized_contract.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_invert encode.

Theorem fe_invert_initialized_local_spec_from_count_calls :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong x]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 secp_jet_initialized_local_spec modinfo_fe_state f_simplicity_fe_invert
  (Word 8)(Word 8)(@literal_fe_invert Alg.CoreFunSem).
Proof.
 intros CountCall env m bd dbase bs sbase bi bw edge outedge cursor rc a
  Ready Base Align Source Cursor Max Input Output.
 change(rc+256<=Int64.max_unsigned) in Max.
 change(write_frame_at m bd dbase bw outedge cursor 256) in Output.
 rewrite encode_word in Input.
 destruct(eval_secp_fe_invert_initialized env m bd dbase bs sbase bw outedge cursor 256 bi edge rc a
  CountCall Ready Output ltac:(lia) Base Align Source Input Cursor Max)
  as(mf & Call & Final & Frame & ReadyF & Preserved).
 destruct Final as[HV [HF [HN [[Cells [Prefix [Fields [Loads Perms]]]] Written]]]].
 rewrite encode_length in Fields,Loads.
 exists mf;split;[exact Call|];split;[exact Cells|];split;[exact Prefix|];split;[exact Fields|];split;[|exact ReadyF].
 intros chunk b ofs Valid FrameOther OutputOther.
 destruct(Pos.eq_dec b bd) as[HD|HD];
  [apply Loads;[split;[left;exact HD|exact Valid]|assumption|assumption]|].
 destruct(Pos.eq_dec b bw) as[HW|HW];
  [apply Loads;[split;[right;left;exact HW|exact Valid]|assumption|assumption]|].
 destruct(Pos.eq_dec b bi) as[HI|HI];
  [apply Loads;[split;[right;right;exact HI|exact Valid]|assumption|assumption]|].
 apply(proj1 Frame);[exact Valid|];intros pos Range.
 unfold extA,fext;intros[[H|[H|H]] _];contradiction.
Qed.
