(** Original Bitcoin TapTweak wrapper entry and call boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_exec C.jets_secp C.jet_secp_linkage C.jet_sx_exec C.jet_sx_mem C.jet_frame_layout C.jet_frame_inv
 C.jet_frame_copy_layout C.jet_secp_taptweak_tag C.jet_secp_taptweak_writer_state C.jet_readBit_layout
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition taptweak_public_env bf:=PTree.set _src (bf,Tstruct _frameItem noattr) empty_env.
Definition taptweak_public_temps vd vs ve:=PTree.set _env ve (PTree.set _src vs
 (PTree.set _dst vd (create_undef_temps (fn_temps f_simplicity_bitcoin_build_taptweak)))).
Lemma taptweak_public_ok:fn_okb f_simplicity_bitcoin_build_taptweak=true.
Proof. reflexivity. Qed.
Lemma taptweak_generic_symbol:Genv.find_symbol secp_ge _simplicity_generic_taptweak=Some (secp_symbol_block _simplicity_generic_taptweak).
Proof. vm_compute;reflexivity. Qed.
Lemma taptweak_generic_function:Genv.find_funct_ptr secp_ge (secp_symbol_block _simplicity_generic_taptweak)=Some (Internal f_simplicity_generic_taptweak).
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge.
Theorem taptweak_public_entry m vd vs ve:exists mi bf,
 function_entry2 secp_ge f_simplicity_bitcoin_build_taptweak [vd;vs;ve] m
 (taptweak_public_env bf) (taptweak_public_temps vd vs ve) mi /\
 (forall b,Mem.valid_block m b ->b<>bf) /\Mem.range_perm mi bf 0 16 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 16) as (mi,bf) eqn:Alloc.
 assert (Entry:function_entry2 secp_ge f_simplicity_bitcoin_build_taptweak [vd;vs;ve] m
 (taptweak_public_env bf) (taptweak_public_temps vd vs ve) mi).
 { destruct (fn_okb_true _ taptweak_public_ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bf);[exact Alloc|constructor]. }
 exists mi,bf;split;[exact Entry|];split.
 - intros b Valid Same;subst b;eapply Mem.fresh_block_alloc;[exact Alloc|exact Valid].
 - split.
   + intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range].
   + split;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc|];split.
     * eapply entry_keeps_permissions;exact Entry.
     * eapply entry_preserved;exact Entry.
Qed.
Definition taptweak_public_copy:=Sassign (Evar _src (Tstruct _frameItem noattr))
 (Etempvar _src (Tstruct _frameItem noattr)).
Definition taptweak_public_call:=Scall (Some _t'1)
 (Evar _simplicity_generic_taptweak (Tfunction
 (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr (Tstruct _frameItem noattr))
 (Tcons (tptr tuchar) (Tcons tulong Tnil)))) tbool cc_default))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));
 Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr));
 Evar _taptweak (tarray tuchar 9);
 Ebinop Osub (Esizeof (tarray tuchar 9) tulong) (Econst_int (Int.repr 1) tint) tulong].
Lemma taptweak_public_source:fn_body f_simplicity_bitcoin_build_taptweak=
 Ssequence taptweak_public_copy (Ssequence taptweak_public_call (Sreturn (Some (Etempvar _t'1 tbool)))).
Proof. reflexivity. Qed.
Lemma exec_taptweak_public_call le m mf bf bd base result:
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_generic_taptweak)
 [Vptr bd (Ptrofs.repr base);Vptr bf Ptrofs.zero;Vptr taptweak_tag_block Ptrofs.zero;Vlong (Int64.repr 8)] E0 mf (Vint (bit_int result)) ->
 Clight2.exec_stmt secp_ge (taptweak_public_env bf) le m taptweak_public_call E0
 (PTree.set _t'1 (Vint (bit_int result)) le) mf Out_normal.
Proof.
 intros Dest Call;unfold taptweak_public_call.
 eapply exec_Scall with (vf:=Vptr (secp_symbol_block _simplicity_generic_taptweak) Ptrofs.zero)
 (vargs:=[Vptr bd (Ptrofs.repr base);Vptr bf Ptrofs.zero;Vptr taptweak_tag_block Ptrofs.zero;Vlong (Int64.repr 8)])
 (f:=Internal f_simplicity_generic_taptweak) (vres:=Vint (bit_int result)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact taptweak_generic_symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Etempvar;exact Dest|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact taptweak_tag_symbol]|apply deref_loc_reference;reflexivity].
   + reflexivity.
   + eapply eval_Econs;[eapply eval_Ebinop;[apply eval_Esizeof|constructor|reflexivity]|reflexivity|constructor].
 - exact taptweak_generic_function.
 - reflexivity.
 - exact Call.
Qed.
Theorem taptweak_public_copy_from_fields m le bf bs sbase bin edge rc:
 frame_base_valid sbase ->(8|sbase) ->bf<>bs ->le!_src=Some (Vptr bs (Ptrofs.repr sbase)) ->
 frame_fields_at m bs sbase bin edge rc ->Mem.range_perm m bf 0 16 Cur Freeable ->exists mc,
 Clight2.exec_stmt secp_ge (taptweak_public_env bf) le m taptweak_public_copy E0 le mc Out_normal /\
 frame_fields_at mc bf 0 bin edge rc /\Mem.range_perm mc bf 0 16 Cur Freeable /\
 lframe (fun b _=>b<>bf) m mc /\readonly_preserved m mc.
Proof.
 intros Base Align Sep Temp [Edge Cursor] Free.
 destruct (frame_loadbytes_at m bs sbase _ _ Edge Cursor) as (bytes & Load).
 pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Length.
 assert (Writable:Mem.range_perm m bf 0 (0+Z.of_nat (length bytes)) Cur Writable).
 { rewrite Length;intros pos Range;eapply Mem.perm_implies;[exact (Free pos Range)|constructor]. }
 destruct (Mem.range_perm_storebytes m bf 0 bytes Writable) as (mc & Store).
 assert (Unsigned:Ptrofs.unsigned (Ptrofs.repr sbase)=sbase).
 { apply Ptrofs.unsigned_repr;unfold frame_base_valid in Base;lia. }
 exists mc;split.
 - unfold taptweak_public_copy;eapply exec_Sassign_copy.
   + apply eval_Evar_local;reflexivity.
   + apply eval_Etempvar;exact Temp.
   + reflexivity.
   + eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
     * reflexivity.
     * intros _;change (8|Ptrofs.unsigned (Ptrofs.repr sbase));rewrite Unsigned;exact Align.
     * intros _;change (8|0);exists 0;reflexivity.
     * left;congruence.
     * change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16=Some bytes);rewrite Unsigned;exact Load.
     * exact Store.
 - split;[eapply frame_copy_fields_at;eassumption|];split.
   + intros pos Range;eapply Mem.perm_storebytes_1;[exact Store|apply Free;exact Range].
   + split.
     * apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|intros;congruence].
     * eapply storebytes_preserved;exact Store.
Qed.
Lemma taptweak_public_blocks bf:blocks_of_env secp_ge (taptweak_public_env bf)=[(bf,0,16)].
Proof. reflexivity. Qed.
Lemma taptweak_public_free m bf:Mem.range_perm m bf 0 16 Cur Freeable ->exists mf,
 Mem.free_list m (blocks_of_env secp_ge (taptweak_public_env bf))=Some mf /\
 lframe (fun b _=>b<>bf) m mf /\readonly_preserved m mf.
Proof.
 intro Free;destruct (Mem.range_perm_free m bf 0 16 Free) as (mf & Frees).
 exists mf;split;[rewrite taptweak_public_blocks;cbn;rewrite Frees;reflexivity|];split.
 - apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Frees|intros;congruence].
 - eapply free_preserved;exact Frees.
Qed.
