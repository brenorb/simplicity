(** Connect the public jet's actual entry/copy/read to the original generator
    call. Digest rejection remains an actual computed result, not an input
    restriction. The subsequent public branch/write/return is still separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.extraMath C.jet_memcpy_model C.jet_sx_mem C.jet_sx_exec C.jet_frame_layout C.jet_encoding
 C.jet_input_layout C.jet_buffer_input C.jet_read8s_layout C.jet_secp_linkage C.jets_secp
 C.jet_secp_field_cmov C.jet_secp_curve_frame C.jet_clight_internal_preserve
 C.jet_secp_sha_startup C.jet_secp_swu_startup C.jet_secp_generator_sha_absorb
 C.jet_secp_generator_hash_map C.jet_secp_hashgen_function C.jet_secp_hashgen_outer
 C.jet_secp_hash_public_entry C.jet_secp_hash_public_read.
Require Simplicity.Translate.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition hash_public_generate := Scall (Some _t'1)
 (Evar _secp256k1_generator_generate (type_of_function f_secp256k1_generator_generate))
 [Eaddrof (Evar _gen (Tstruct __6563 noattr)) (tptr (Tstruct __6563 noattr));
  Evar _key (tarray tuchar 32)].
Definition hash_public_decision := match hash_public_tail with
 | Ssequence (Ssequence _ branch) _=>branch | _=>Sskip end.
Definition hash_public_finish := match hash_public_tail with
 | Ssequence _ rest=>rest | _=>Sskip end.
Lemma hash_public_tail_source : hash_public_tail=
 Ssequence (Ssequence hash_public_generate hash_public_decision) hash_public_finish.
Proof. reflexivity. Qed.
Lemma hash_public_generator_link :
 Genv.find_symbol secp_ge _secp256k1_generator_generate=
   Some (secp_symbol_block _secp256k1_generator_generate) /\
 Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_generator_generate) Ptrofs.zero)=
   Some (Internal f_secp256k1_generator_generate).
Proof. vm_compute;split;reflexivity. Qed.

Lemma exec_hash_public_generate le m mf bl bk bg bp ret :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_generator_generate)
   [Vptr bg Ptrofs.zero;Vptr bk Ptrofs.zero] E0 mf (Vint ret) ->
 Clight2.exec_stmt secp_ge (hash_public_env bl bk bg bp) le m hash_public_generate E0
   (PTree.set _t'1 (Vint ret) le) mf Out_normal.
Proof.
 intro Call;destruct hash_public_generator_link as [Symbol Function].
 unfold hash_public_generate;eapply exec_Scall with
   (vf:=Vptr (secp_symbol_block _secp256k1_generator_generate) Ptrofs.zero)
   (vargs:=[Vptr bg Ptrofs.zero;Vptr bk Ptrofs.zero])
   (f:=Internal f_secp256k1_generator_generate) (vres:=Vint ret).
 - reflexivity.
 - eapply eval_Elvalue.
   + eapply eval_Evar_global;[reflexivity|exact Symbol].
   + apply deref_loc_reference;reflexivity.
 - eapply eval_Econs.
   + eapply eval_Eaddrof;apply eval_Evar_local;reflexivity.
   + reflexivity.
   + eapply eval_Econs.
     * eapply eval_Elvalue;[apply eval_Evar_local;reflexivity|apply deref_loc_reference;reflexivity].
     * reflexivity.
     * constructor.
 - exact Function.
 - reflexivity.
 - exact Call.
Qed.

Theorem hash_public_begin (Hmodel:memcpy_model) key v_env m0 bd base bs sbase bi edge rc :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
     E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
 secp_sha_startup m0 ->swu_startup m0 ->(forall prefix,generator_sha_prefix_state prefix m0) ->
 frame_base_valid sbase ->(8|sbase) ->frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc (Simplicity.Translate.encode (key:Ty.tySem (Word 8))) ->
 0<=rc ->rc+256<=Int64.max_unsigned ->
 exists mi bl bk bg bp mf sx sy sz sumflag ox oy,
 function_entry2 secp_ge f_simplicity_hash_to_curve
   [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] m0
   (hash_public_env bl bk bg bp) (hash_public_temps v_env bd base bs sbase) mi /\
 Clight2.exec_stmt secp_ge (hash_public_env bl bk bg bp)
   (hash_public_temps v_env bd base bs sbase) mi
   (Ssequence hash_public_prefix hash_public_generate) E0
   (PTree.set _t'1 (Vint (cmov_int (generator_hash_accepted false key && generator_hash_accepted true key)))
     (hash_public_temps v_env bd base bs sbase)) mf Out_normal /\
 hashgen_result key mf bg sx sy sz sumflag ox oy /\
 NoDup (hash_public_locals bl bk bg bp) /\
 (forall b,Mem.valid_block m0 b ->~In b (hash_public_locals bl bk bg bp)) /\
 (forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->
   Mem.range_perm mf b 0 hi Cur Freeable) /\
 lframe (fun _ _=>True) m0 mf /\readonly_preserved m0 mf /\
 secp_sha_startup mf /\swu_startup mf /\(forall prefix,generator_sha_prefix_state prefix mf).
Proof.
 intros Count SHA SWU Prefixes Base Align Source Input RC Max.
 destruct (hash_public_entry v_env m0 bd base bs sbase)
   as (mi & bl & bk & bg & bp & Entry & Distinct & Old & Free & Alloc & RO).
 destruct (hash_public_prepare key (hash_public_temps v_env bd base bs sbase)
   m0 mi bl bk bg bp bs sbase bi edge rc Distinct Old Free Alloc RO
   ltac:(unfold hash_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
   Base Align Source Input RC Max) as (md & Prepare & Key & Fields & FreeD & FrameD & ROD).
 assert (SHAD:secp_sha_startup md).
 { eapply secp_sha_startup_preserved;[exact SHA|exact ROD|exact FrameD|intros;exact I]. }
 assert (SWUD:swu_startup md) by (eapply swu_startup_preserved;[exact SWU|exact ROD]).
 assert (PrefixesD:forall prefix,generator_sha_prefix_state prefix md).
 { intro prefix;eapply generator_sha_prefix_preserved;[apply Prefixes|exact ROD]. }
 assert (KG:bk<>bg).
 { clear -Distinct;unfold hash_public_locals in Distinct;repeat rewrite NoDup_cons_iff in Distinct;
   cbn [In] in Distinct;intuition congruence. }
 destruct (eval_hashgen_generate Hmodel key md bg bk Ptrofs.zero Count KG
   ltac:(clear;change (32<=18446744073709551615);lia) SHAD SWUD PrefixesD
   ltac:(apply FreeD;clear;cbn [hash_public_storage In];tauto) Key)
   as (mf & sx & sy & sz & sumflag & ox & oy & Generate & Result & FGF & KeyF & FrameG & ROG & SHAF & SWUF & PrefixF).
 assert (FreeF:forall b hi,In (b,hi) (hash_public_storage bl bk bg bp) ->
   Mem.range_perm mf b 0 hi Cur Freeable).
 { intros b hi Slot;destruct (peq b bg) as [Same|Other].
   - subst b;assert (Hi:hi=64).
     { clear -Slot Distinct;unfold hash_public_locals in Distinct;
       repeat rewrite NoDup_cons_iff in Distinct;cbn [hash_public_storage In] in Slot;
       cbn [In] in Distinct;intuition congruence. }
     subst hi;exact FGF.
   - assert (Range:Mem.range_perm md b 0 hi Cur Freeable) by (apply FreeD;exact Slot).
     intros pos Bound;apply (proj1(proj2 FrameG));[eapply Mem.perm_valid_block;apply Range;exact Bound|exact Other|apply Range;exact Bound]. }
 assert (FinalFrame:lframe (fun _ _=>True) m0 mf).
 { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m0 b).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FrameD|];intros;exact I.
     + eapply lframe_implies;[exact FrameG|];intros b ofs Valid _ Same;subst b;
       apply (Old bg Valid);unfold hash_public_locals;cbn;tauto.
   - intros;assumption. }
 exists mi,bl,bk,bg,bp,mf,sx,sy,sz,sumflag,ox,oy;split;[exact Entry|];split.
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md)
     (le1:=hash_public_temps v_env bd base bs sbase);
     [exact Prepare|eapply exec_hash_public_generate;exact Generate].
 - split;[exact Result|];split;[exact Distinct|];split;[exact Old|];split;[exact FreeF|];
   split;[exact FinalFrame|];split;[eapply preserved_trans;[exact ROD|exact ROG]|];
   split;[exact SHAF|];split;assumption.
Qed.
