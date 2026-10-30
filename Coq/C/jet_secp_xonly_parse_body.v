(** Complete original x-only key parser body, for every input word. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_read8s_layout C.jet_sx_mem C.jet_memcpy_model C.jet_memset_model
 C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_statement_prefix
 C.jet_secp_root_chain_owned C.jet_secp_xonly_parse_field C.jet_clight_internal_preserve.
Require Import C.jet_secp_xonly_parse_start.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Theorem exec_xonly_parse_body (Copy:memcpy_model) (Clear:memset_model) pk e le m bp bx bout bin:
 e!_pk=Some (bp,curve_ge_type) ->e!_x=Some (bx,curve_fe_type) ->e!_memset=None ->
 e!_secp256k1_fe_set_b32=None ->e!_secp256k1_ge_set_xo_var=None ->
 e!_secp256k1_ge_is_in_correct_subgroup=None ->e!_secp256k1_xonly_pubkey_save=None ->
 le!_pubkey=Some (Vptr bout Ptrofs.zero) ->le!_input32=Some (Vptr bin Ptrofs.zero) ->
 NoDup [bp;bx;bout;bin] ->
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf lef,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_xonly_pubkey_parse) E0 lef mf
 (Out_return (Some (Vint (xonly_parse_result pk),tint))) /\
 xonly_parsed_result pk mf bout /\
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>b<>bp /\b<>bx /\b<>bout /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros P X ClearSym ReadSym DecodeSym SubgroupSym SaveSym Key InputPtr Separate Owned Input.
 assert (IO:bin<>bout).
 { clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;intuition congruence. }
 assert (FreeIn:Mem.range_perm m bin 0 32 Cur Freeable) by (apply Owned;clear;cbn [In];tauto).
 assert (Valid:Mem.valid_block m bin) by (eapply Mem.perm_valid_block;apply (FreeIn 0);lia).
 assert (Weak:Mem.weak_valid_pointer m bin (Ptrofs.unsigned Ptrofs.zero)=true).
 { apply Mem.valid_pointer_implies;apply Mem.valid_pointer_nonempty_perm.
   eapply Mem.perm_implies;[apply (FreeIn 0);change (0<=0<32);lia|apply perm_any_N]. }
 destruct (exec_xonly_parse_start Clear e le m bout bin Ptrofs.zero ClearSym Key InputPtr
  (Owned bout 64 ltac:(clear;cbn [In];tauto)) Weak)
 as (mz & Start & FreeOut & KeepZ & FrameZ & ReadZ).
 assert (OwnedZ:forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mz b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepZ;exact (Owned b hi Slot pos Range). }
 assert (InputZ:uint8_array_at mz bin 0 (map Int.repr (xonly_input_bytes pk))).
 { intros i x Nth;rewrite (proj1 FrameZ Mint8unsigned bin (0+Z.of_nat i) Valid);
   [apply Input;exact Nth|intros;exact IO]. }
 destruct (exec_xonly_parse_field Copy pk e le mz bp bx bout bin P X ReadSym DecodeSym SubgroupSym SaveSym
  Key InputPtr Separate OwnedZ InputZ) as (mf & lef & Tail & Parsed & OwnedF & FrameF & ReadF).
 exists mf,lef;split.
 - rewrite <-xonly_parse_start_source,xonly_parse_field_return_source.
   eapply exec_statement_prefix_then_last;[exact Start|exact Tail].
 - split;[exact Parsed|];split;[exact OwnedF|];split.
   + eapply lframe_trans;[|exact FrameF].
     eapply lframe_implies;[exact FrameZ|];intros b pos (_ & _ & Outside & _) _;exact Outside.
   + eapply preserved_trans;[exact ReadZ|exact ReadF].
Qed.
