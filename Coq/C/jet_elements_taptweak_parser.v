(** Whole original x-only parser in the linked Elements program, for every
    input word, deriving both private allocations, all branches and both frees. *)
(** Entire original x-only key parser on its caller's owned input/output buffers. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_read8s_layout C.jet_sx_mem C.jet_memcpy_model C.jet_memset_model
 C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_xonly_parse_field C.jet_secp_affine_storage C.jet_secp_table_decode
 C.jet_secp_xonly_parse_control C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Require Import C.jet_secp_xonly_parse_entry C.jet_secp_xonly_parse_body.

Require Import C.jet_secp_xonly_parse_function C.jet_secp_xonly_parse_start
 C.jet_secp_xonly_parse_body C.jet_secp_xonly_parse_entry C.jet_secp_statement_prefix C.jet_transport
 C.jet_elements_taptweak_parse_start C.jet_elements_taptweak_parse_field C.jet_elements_taptweak_pure.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_parser_vars_checked:
 vars_okb secp_ge elements_taptweak_ge (fn_vars f_secp256k1_xonly_pubkey_parse)=true.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_parser_sizes:
 sizeof (genv_cenv elements_taptweak_ge) curve_fe_type=40 /\
 sizeof (genv_cenv elements_taptweak_ge) curve_ge_type=88.
Proof. vm_compute;split;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge.
Lemma elements_taptweak_parser_blocks bp bx:
 blocks_of_env elements_taptweak_ge (xonly_parse_env bp bx)=[(bx,0,40);(bp,0,88)].
Proof.
 change ([(bx,0,sizeof (genv_cenv elements_taptweak_ge) curve_fe_type);
 (bp,0,sizeof (genv_cenv elements_taptweak_ge) curve_ge_type)]=[(bx,0,40);(bp,0,88)]).
 rewrite (proj1 elements_taptweak_parser_sizes),(proj2 elements_taptweak_parser_sizes);reflexivity.
Qed.
Theorem elements_taptweak_parser_entry_owned m key input:exists mi bp bx,
 function_entry2 elements_taptweak_ge f_secp256k1_xonly_pubkey_parse [key;input] m
 (xonly_parse_env bp bx) (xonly_parse_temps key input) mi /\NoDup [bp;bx] /\
 (forall b,Mem.valid_block m b ->~In b [bp;bx]) /\
 Mem.range_perm mi bp 0 88 Cur Freeable /\Mem.range_perm mi bx 0 40 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (xonly_parse_entry_owned m key input) as (mi & bp & bx & Entry & Memory).
 exists mi,bp,bx;split;[|exact Memory].
 inversion Entry as [Vars Params Disjoint Alloc Bind];subst.
 constructor;[exact Vars|exact Params|exact Disjoint| |exact Bind].
 eapply (alloc_variables_transport secp_ge elements_taptweak_ge);[exact Alloc|exact elements_taptweak_parser_vars_checked].
Qed.
Theorem exec_elements_taptweak_parser_body (Copy:memcpy_model) (Clear:memset_model) pk e le m bp bx bout bin:
 e!_pk=Some (bp,curve_ge_type) ->e!_x=Some (bx,curve_fe_type) ->e!_memset=None ->
 e!_secp256k1_fe_set_b32=None ->e!_secp256k1_ge_set_xo_var=None ->
 e!_secp256k1_ge_is_in_correct_subgroup=None ->e!_secp256k1_xonly_pubkey_save=None ->
 le!_pubkey=Some (Vptr bout Ptrofs.zero) ->le!_input32=Some (Vptr bin Ptrofs.zero) ->
 NoDup [bp;bx;bout;bin] ->
 (forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm m b 0 hi Cur Freeable) ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf lef,
 Clight2.exec_stmt elements_taptweak_ge e le m (fn_body f_secp256k1_xonly_pubkey_parse) E0 lef mf
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
 destruct (exec_elements_taptweak_xonly_parse_start Clear e le m bout bin Ptrofs.zero ClearSym Key InputPtr
  (Owned bout 64 ltac:(clear;cbn [In];tauto)) Weak)
 as (mz & Start & FreeOut & KeepZ & FrameZ & ReadZ).
 assert (OwnedZ:forall b hi,In (b,hi) [(bp,88);(bx,40);(bout,64);(bin,32)] ->Mem.range_perm mz b 0 hi Cur Freeable).
 { intros b hi Slot pos Range;apply KeepZ;exact (Owned b hi Slot pos Range). }
 assert (InputZ:uint8_array_at mz bin 0 (map Int.repr (xonly_input_bytes pk))).
 { intros i x Nth;rewrite (proj1 FrameZ Mint8unsigned bin (0+Z.of_nat i) Valid);
   [apply Input;exact Nth|intros;exact IO]. }
 destruct (exec_elements_taptweak_parse_field Copy pk e le mz bp bx bout bin P X ReadSym DecodeSym SubgroupSym SaveSym
  Key InputPtr Separate OwnedZ InputZ) as (mf & lef & Tail & Parsed & OwnedF & FrameF & ReadF).
 exists mf,lef;split.
 - rewrite <-xonly_parse_start_source,xonly_parse_field_return_source.
   eapply exec_statement_prefix_then_last;[exact Start|exact Tail].
 - split;[exact Parsed|];split;[exact OwnedF|];split.
   + eapply lframe_trans;[|exact FrameF].
     eapply lframe_implies;[exact FrameZ|];intros b pos (_ & _ & Outside & _) _;exact Outside.
   + eapply preserved_trans;[exact ReadZ|exact ReadF].
Qed.

Theorem eval_elements_taptweak_xonly_pubkey_parse_owned (Copy:memcpy_model) (Clear:memset_model) pk m bout bin:
 bout<>bin ->Mem.range_perm m bout 0 64 Cur Freeable ->Mem.range_perm m bin 0 32 Cur Freeable ->
 uint8_array_at m bin 0 (map Int.repr (xonly_input_bytes pk)) ->exists mf,
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_xonly_pubkey_parse)
 [Vptr bout Ptrofs.zero;Vptr bin Ptrofs.zero] E0 mf (Vint (xonly_parse_result pk)) /\
 xonly_parsed_result pk mf bout /\Mem.range_perm mf bout 0 64 Cur Freeable /\
 Mem.range_perm mf bin 0 32 Cur Freeable /\
 lframe (fun b _=>b<>bout /\b<>bin) m mf /\readonly_preserved m mf.
Proof.
 intros OI FreeOut FreeIn Input.
 assert (VO:Mem.valid_block m bout) by (eapply Mem.perm_valid_block;apply (FreeOut 0);lia).
 assert (VI:Mem.valid_block m bin) by (eapply Mem.perm_valid_block;apply (FreeIn 0);lia).
 destruct (elements_taptweak_parser_entry_owned m (Vptr bout Ptrofs.zero) (Vptr bin Ptrofs.zero))
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
 destruct (exec_elements_taptweak_parser_body Copy Clear pk e le mi bp bx bout bin
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
     * unfold e;rewrite elements_taptweak_parser_blocks;exact Frees.
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
