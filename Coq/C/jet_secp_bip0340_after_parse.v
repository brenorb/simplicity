(** Original public message/signature readers through the canonical verifier return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_encoding C.jet_input_layout C.jet_frame_layout C.jet_readBit_layout C.jet_sx_mem
 C.jet_secp_linkage C.jets_secp C.jet_secp_curve_frame C.jet_secp_root_chain_owned C.jet_secp_statement_prefix
 C.jet_memcpy_model C.jet_memset_model C.jet_ctz_model C.jet_clight_forward C.jet_clight_internal_preserve
 C.jet_secp_schnorr_verify_literal C.jet_secp_schnorr_startup C.jet_secp_linear_startup
 C.jet_secp_sha_startup C.jet_secp_modinfo_fe_caller C.jet_secp_xonly_parse_control C.jet_secp_xonly_parse_field
 C.jet_secp_bip0340_public_entry C.jet_secp_bip0340_data_reads C.jet_secp_bip0340_verifier_return.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_bip0340_check.
Theorem exec_bip0340_after_parse (Copy:memcpy_model) (Clear:memset_model) (Count:ctz_model)
 (pk msg r s:Ty.tySem (Word 8)) le m bl bb bkey bmsg bsig bi edge cursor:
 NoDup (bip0340_public_locals bl bb bkey bmsg bsig) ->bl<>bi ->bmsg<>bi ->bsig<>bi ->
 0<=cursor ->cursor+1024<=Int64.max_unsigned ->
 (forall b hi,In (b,hi) (bip0340_public_storage bl bb bkey bmsg bsig) ->Mem.range_perm m b 0 hi Cur Freeable) ->
 frame_fields_at m bl 0 bi edge (cursor+256) ->
 frame_input_cells_at m bi edge (cursor+256) (Simplicity.Translate.encode msg) ->
 frame_input_cells_at m bi edge (cursor+512) (@Simplicity.Translate.encode (Ty.Prod (Word 8) (Word 8)) (r,s)) ->
 xonly_parse_result pk=Int.one ->xonly_parsed_result pk m bkey ->schnorr_startup m ->exists mf lef,
 Clight2.exec_stmt secp_ge (bip0340_public_env bl bb bkey bmsg bsig) le m
 (root_drop_statements 3 (fn_body f_simplicity_bip_0340_verify)) E0 lef mf
 (Out_return (Some (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s))))),tint))) /\
 (forall b hi,In (b,hi) (bip0340_public_storage bl bb bkey bmsg bsig) ->Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun b _=>~In b (bip0340_public_locals bl bb bkey bmsg bsig)) m mf /\
 mem_forward m mf /\schnorr_startup mf.
Proof.
 intros Separate LI MI SI Cursor Max Owned Source MsgInput SigInput Success Parsed Ready.
 assert (Slots:forall b hi,In (b,hi) (bip0340_public_storage bl bb bkey bmsg bsig) ->
  0<hi /\Mem.range_perm m b 0 hi Cur Freeable).
 { intros b hi Slot;split;[clear -Slot;cbn [bip0340_public_storage In] in Slot;
   repeat destruct Slot as [Slot|Slot];try contradiction;inversion Slot;lia|exact (Owned b hi Slot)]. }
 destruct (exec_bip0340_data_reads pk msg r s le m bl bb bkey bmsg bsig bi edge cursor
  Separate LI MI SI Cursor Max Owned Source MsgInput SigInput Parsed)
 as (md & Reads & MsgBytes & RBytes & SBytes & ParsedD & FieldsD & OwnedD & FrameD & ReadD).
 assert (FrameDAll:lframe (fun b _=>~In b (bip0340_public_locals bl bb bkey bmsg bsig)) m md).
 { eapply lframe_implies;[exact FrameD|];intros b pos Outside _;
   clear -Outside;cbn [bip0340_public_locals In] in *;intuition congruence. }
 assert (ReadyD:schnorr_startup md).
 { eapply schnorr_startup_owned_forward;[exact Ready|exact (proj1 ReadD)|exact Slots|exact FrameDAll]. }
 assert (Pairs:bsig<>bmsg /\bsig<>bkey).
 { clear -Separate;unfold bip0340_public_locals in Separate;repeat rewrite NoDup_cons_iff in Separate;
   cbn [In] in *;intuition congruence. }
 destruct ReadyD as ([Split [Beta Tables]] & Modulus & SHA).
 destruct (exec_bip0340_verifier_return Copy Clear Count pk msg r s
  (bip0340_public_env bl bb bkey bmsg bsig) le md bsig bmsg bkey
  eq_refl eq_refl eq_refl eq_refl (proj1 Pairs) (proj2 Pairs)
  (OwnedD bsig 64 ltac:(clear;cbn [bip0340_public_storage In];tauto)) RBytes SBytes MsgBytes Success ParsedD
  SHA Tables Split Beta Modulus)
 as (mf & Return & SigFree & FrameF & ForwardF).
 assert (Frame:lframe (fun b _=>~In b (bip0340_public_locals bl bb bkey bmsg bsig)) m mf).
 { eapply lframe_trans;[exact FrameDAll|];eapply lframe_implies;[exact FrameF|].
   intros b pos Outside _;clear -Outside;cbn [bip0340_public_locals In] in *;intuition congruence. }
 assert (Forward:mem_forward m mf) by (eapply mem_forward_trans;[exact (proj1 ReadD)|exact ForwardF]).
 exists mf,(PTree.set _t'2 (Vint (bit_int (Simplicity.Bit.toBool
  (@literal_bip0340_check Simplicity.Alg.CoreFunSem ((pk,msg),(r,s)))))) le);split.
 - rewrite bip0340_data_reads_source;eapply exec_statement_prefix_then_last;[exact Reads|exact Return].
 - split.
   + intros b hi Slot;destruct (Pos.eq_dec b bsig) as [Same|Other].
     * subst b;assert (Size:hi=64).
       { clear -Slot Separate;unfold bip0340_public_locals in Separate;repeat rewrite NoDup_cons_iff in Separate;
         cbn [bip0340_public_storage In] in *;intuition congruence. }
       subst hi;exact SigFree.
     * eapply curve_keep_free;[|exact (OwnedD b hi Slot)|exact FrameF|intros;exact Other].
       exact (proj1 (Slots b hi Slot)).
   + split;[exact Frame|];split;[exact Forward|].
     eapply schnorr_startup_owned_forward;[exact Ready|exact Forward|exact Slots|exact Frame].
Qed.
