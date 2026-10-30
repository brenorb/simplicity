(** Entire original x-only key parser on its caller's owned input/output buffers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_read8s_layout C.jet_sx_mem C.jet_memcpy_model C.jet_memset_model
 C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_xonly_parse_field C.jet_secp_affine_storage C.jet_secp_table_decode
 C.jet_secp_xonly_parse_control C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require Import C.jet_secp_xonly_parse_entry C.jet_secp_xonly_parse_body.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Theorem eval_xonly_pubkey_parse_owned (Copy:memcpy_model) (Clear:memset_model) pk m bout bin:
 bout<>bin ->Mem.range_perm m bout 0 64 Cur Freeable ->Mem.range_perm m bin 0 32 Cur Freeable ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_xonly_pubkey_parse)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf (Vint (xonly_parse_result pk)) /\
 xonly_parsed_result pk mf bout /\Mem.range_perm mf bout 0 64 Cur Freeable /\
 Mem.range_perm mf bin 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bout /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros OI FreeOut FreeIn Input.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (FreeOut 0);lia).
 assert (VI:Mem.valid_block m bin) by (eapply Mem.perm_valid_block;apply (FreeIn 0);lia).
 destruct (xonly_parse_entry_owned m (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero))
 as (mi & bp & bx & Entry & Separate & Fresh & FreeP & FreeX & FrameI & KeepI & ReadI).
 assert (OutFresh:~In bout [bp;bx]) by (apply Fresh;exact VO).
 assert (InFresh:~In bin [bp;bx]) by (apply Fresh;exact VI).
 assert (AllSeparate:NoDup [bp;bx;bout;bin]).
 { clear -Separate OutFresh InFresh OI;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;
   repeat constructor;cbn [In];intuition congruence. }
 assert (OwnedAll:forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mi b 0 hi Cur Freeable).
 { intros b hi [Same|[Same|[Same|[Same|[]]]]];inversion Same;subst b hi.
   - exact FreeP.
   - exact FreeX.
   - intros pos Range;apply KeepI,FreeOut;exact Range.
   - intros pos Range;apply KeepI,FreeIn;exact Range. }
 assert (InputI:uint8_array_at mi bin 0 (map Int.repr (xonly_input_bytes pk))).
 { intros i x Nth;rewrite (proj1 FrameI Mint8unsigned bin (0+Z.of_nat i) VI);
   [apply Input;exact Nth|intros;exact I]. }
 pose (e:=xonly_parse_env bp bx).
 pose (le:=xonly_parse_temps (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero)).
 destruct (exec_xonly_parse_body Copy Clear pk e le mi bp bx bout bin
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl AllSeparate OwnedAll InputI)
 as (mb & lef & Body & Parsed & OwnedB & FrameB & ReadB).
 destruct (free_list_exists [(bx,0,40);(bp,0,88)] mb) as (mf & Frees & UnchangedF).
 - clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in *;
   repeat constructor;cbn;intuition congruence.
 - intros b lo hi Slot;cbn [In] in Slot;repeat destruct Slot as [Slot|Slot];
   try contradiction;inversion Slot;subst b lo hi;apply OwnedB;clear;cbn [In];tauto.
 - assert (FrameF:lframe (fun b _=>~In b [bp;bx]) mb mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact UnchangedF|].
     intros b pos Outside _;clear -Outside;cbn [map fst In] in *;tauto. }
   assert (ParsedF:xonly_parsed_result pk mf bout).
   { intros Bound ax ay Literal;destruct (Parsed Bound ax ay Literal) as (storage & Storage & VX & VY).
     exists storage;split;[|split;assumption].
     eapply affine_storage_readable_lframe;[exact Storage|exact FrameF|intros;exact OutFresh]. }
   assert (FreeOF:Mem.range_perm mf bout 0 64 Cur Freeable).
   { eapply curve_keep_free;[lia|apply OwnedB;clear;cbn [In];tauto|exact FrameF|intros;exact OutFresh]. }
   assert (FreeIF:Mem.range_perm mf bin 0 32 Cur Freeable).
   { eapply curve_keep_free;[lia|apply OwnedB;clear;cbn [In];tauto|exact FrameF|intros;exact InFresh]. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mb)
     (out:=Out_return (Some (Vint (xonly_parse_result pk),tint))).
     * exact Entry.
     * exact Body.
     * split;[discriminate|reflexivity].
     * unfold e;rewrite xonly_parse_blocks;exact Frees.
   + split;[exact ParsedF|];split;[exact FreeOF|];split;[exact FreeIF|];split.
     * eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\b<>bout /\b<>bin).
       { eapply lframe_trans.
         - eapply lframe_implies;[exact FrameI|intros;exact I].
         - eapply lframe_trans.
           + eapply lframe_implies;[exact FrameB|].
             intros b pos (Valid & NO & NI) _;split;[|split;[|split;assumption]];
             intro Same;apply (Fresh b Valid);rewrite Same;cbn [In];tauto.
           + eapply lframe_implies;[exact FrameF|].
             intros b pos (Valid & _ & _) _;apply Fresh;exact Valid. }
       intros b pos [NO NI] Valid;repeat split;assumption.
     * eapply preserved_trans;[exact ReadI|];eapply preserved_trans;[exact ReadB|].
       eapply freelist_preserved;exact Frees.
Qed.
