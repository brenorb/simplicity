(** Frozen Elements wrapper, by-value frame entry, actual tag and generic call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require C.jets_elements.
Require Import C.jet_secp_taptweak_public_support C.jet_elements_taptweak_pure C.jet_elements_taptweak_globals C.jet_elements_taptweak_curve_transport
 C.jet_transport C.jet_transport_locals C.jet_transport_entry.
Require Import C.jet_elements_taptweak_runtime_ready.
Require Import C.jet_exec C.jets_secp C.jet_secp_linkage C.jet_sx_exec C.jet_sx_mem C.jet_frame_layout C.jet_frame_inv
 C.jet_frame_copy_layout C.jet_secp_taptweak_tag C.jet_secp_taptweak_writer_state C.jet_readBit_layout
 C.jet_clight_internal_preserve C.jet_clight_internal_permissions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Lemma elements_taptweak_public_ok:fn_okb C.jets_elements.f_simplicity_build_taptweak=true.
Proof. reflexivity. Qed.
Lemma elements_taptweak_generic_symbol:Genv.find_symbol elements_taptweak_ge _simplicity_generic_taptweak=Some (elements_taptweak_symbol_block _simplicity_generic_taptweak).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_generic_function:Genv.find_funct_ptr elements_taptweak_ge (elements_taptweak_symbol_block _simplicity_generic_taptweak)=Some (Internal f_simplicity_generic_taptweak).
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_public_tag_symbol:
 Genv.find_symbol elements_taptweak_ge _taptweak=Some elements_taptweak_runtime_tag_block.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_public_frame_size:sizeof(genv_cenv elements_taptweak_ge)(Tstruct _frameItem noattr)=16.
Proof. vm_compute;reflexivity. Qed.
Lemma elements_taptweak_public_copy_checked:
 locals_stmt_okb secp_ge elements_taptweak_ge(map fst elements_taptweak_curve_helpers)
 (map fst(fn_vars C.jets_elements.f_simplicity_build_taptweak))taptweak_public_copy=Datatypes.true.
Proof. vm_compute;reflexivity. Qed.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_runtime_tag_block elements_taptweak_curve_helpers.
Theorem elements_taptweak_public_entry m vd vs ve:exists mi bf,
 function_entry2 elements_taptweak_ge C.jets_elements.f_simplicity_build_taptweak [vd;vs;ve] m
 (taptweak_public_env bf) (taptweak_public_temps vd vs ve) mi /\
 (forall b,Mem.valid_block m b ->b<>bf) /\Mem.range_perm mi bf 0 16 Cur Freeable /\
 lframe (fun _ _=>True) m mi /\keeps_permissions m mi /\readonly_preserved m mi.
Proof.
 destruct (Mem.alloc m 0 16) as (mi,bf) eqn:Alloc.
 assert (Entry:function_entry2 elements_taptweak_ge C.jets_elements.f_simplicity_build_taptweak [vd;vs;ve] m
 (taptweak_public_env bf) (taptweak_public_temps vd vs ve) mi).
 { destruct (fn_okb_true _ elements_taptweak_public_ok) as (Vars & Params & Disjoint).
 constructor;[exact Vars|exact Params|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons with(m1:=mi)(b1:=bf).
 - change(Mem.alloc m 0(sizeof elements_taptweak_ge(Tstruct _frameItem noattr))=(mi,bf)).
   rewrite elements_taptweak_public_frame_size;exact Alloc.
 - constructor. }
 exists mi,bf;split;[exact Entry|];split.
 - intros b Valid Same;subst b;eapply Mem.fresh_block_alloc;[exact Alloc|exact Valid].
 - split.
   + intros pos Range;eapply Mem.perm_alloc_2;[exact Alloc|exact Range].
   + split;[apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc|];split.
     * eapply entry_keeps_permissions;exact Entry.
     * eapply entry_preserved;exact Entry.
Qed.
Definition elements_taptweak_public_copy:=Sassign (Evar _src (Tstruct _frameItem noattr))
 (Etempvar _src (Tstruct _frameItem noattr)).
Definition elements_taptweak_public_call:=Scall (Some _t'1)
 (Evar _simplicity_generic_taptweak (Tfunction
 (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr (Tstruct _frameItem noattr))
 (Tcons (tptr tuchar) (Tcons tulong Tnil)))) tbool cc_default))
 [Etempvar _dst (tptr (Tstruct _frameItem noattr));
 Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr));
 Evar _taptweak (tarray tuchar 18);
 Ebinop Osub (Esizeof (tarray tuchar 18) tulong) (Econst_int (Int.repr 1) tint) tulong].
Lemma elements_taptweak_public_source:fn_body C.jets_elements.f_simplicity_build_taptweak=
 Ssequence elements_taptweak_public_copy (Ssequence elements_taptweak_public_call (Sreturn (Some (Etempvar _t'1 tbool)))).
Proof. reflexivity. Qed.
Lemma exec_elements_taptweak_public_call le m mf bf bd base result:
 le!_dst=Some (Vptr bd (Ptrofs.repr base)) ->
 Clight2.eval_funcall elements_taptweak_ge m (Internal f_simplicity_generic_taptweak)
 [Vptr bd (Ptrofs.repr base);Vptr bf Ptrofs.zero;Vptr elements_taptweak_runtime_tag_block Ptrofs.zero;Vlong (Int64.repr 17)] E0 mf (Vint (bit_int result)) ->
 Clight2.exec_stmt elements_taptweak_ge (taptweak_public_env bf) le m elements_taptweak_public_call E0
 (PTree.set _t'1 (Vint (bit_int result)) le) mf Out_normal.
Proof.
 intros Dest Call;unfold elements_taptweak_public_call.
 eapply exec_Scall with (vf:=Vptr (elements_taptweak_symbol_block _simplicity_generic_taptweak) Ptrofs.zero)
 (vargs:=[Vptr bd (Ptrofs.repr base);Vptr bf Ptrofs.zero;Vptr elements_taptweak_runtime_tag_block Ptrofs.zero;Vlong (Int64.repr 17)])
 (f:=Internal f_simplicity_generic_taptweak) (vres:=Vint (bit_int result)).
 - reflexivity.
 - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact elements_taptweak_generic_symbol]|apply deref_loc_reference;reflexivity].
 - eapply eval_Econs;[apply eval_Etempvar;exact Dest|reflexivity|].
   eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|].
   eapply eval_Econs.
   + eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact elements_taptweak_public_tag_symbol]|apply deref_loc_reference;reflexivity].
   + reflexivity.
   + eapply eval_Econs;[eapply eval_Ebinop;[apply eval_Esizeof|constructor|reflexivity]|reflexivity|constructor].
 - exact elements_taptweak_generic_function.
 - reflexivity.
 - exact Call.
Qed.
Lemma elements_taptweak_public_blocks bf:blocks_of_env elements_taptweak_ge(taptweak_public_env bf)=[(bf,0,16)].
Proof. change([(bf,0,sizeof elements_taptweak_ge(Tstruct _frameItem noattr))]=[(bf,0,16)]);rewrite elements_taptweak_public_frame_size;reflexivity. Qed.
Lemma elements_taptweak_public_free m bf:Mem.range_perm m bf 0 16 Cur Freeable ->exists mf,
 Mem.free_list m (blocks_of_env elements_taptweak_ge (taptweak_public_env bf))=Some mf /\
 lframe (fun b _=>b<>bf) m mf /\readonly_preserved m mf.
Proof.
 intro Free;destruct (Mem.range_perm_free m bf 0 16 Free) as (mf & Frees).
 exists mf;split;[rewrite elements_taptweak_public_blocks;cbn;rewrite Frees;reflexivity|];split.
 - apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Frees|intros;congruence].
 - eapply free_preserved;exact Frees.
Qed.
