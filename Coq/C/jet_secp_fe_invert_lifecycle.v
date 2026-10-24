(** Complete original public field-invert caller, preserving the existing
    field-modulus startup state. CTZ remains the explicit deferred parameter. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_exec C.jet_frame_layout C.jet_frame_inv C.jet_encoding C.jet_input_layout
 C.jet_output_layout C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_public_lifecycle C.jet_secp_wrapper_run
 C.jet_secp_invert_literal C.jet_secp_fe_invert_rest C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_fe_invert encode.

Lemma field_invert_entry v_env m ma mb bl ba bd dbase bs sbase :
 Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 40=(mb,ba) ->
 function_entry2 secp_ge f_simplicity_fe_invert
  [Vptr bd(Ptrofs.repr dbase);Vptr bs(Ptrofs.repr sbase);v_env]m
  (secp_public_env bl ba)(secp_public_temps v_env bd dbase bs sbase)mb.
Proof.
 intros HA HB;pose proof(secp_fe_normalize_entry v_env m ma mb bl ba bd dbase bs sbase HA HB) as Entry.
 inversion Entry;subst;constructor;assumption.
Qed.
Lemma field_invert_public_body : fn_body f_simplicity_fe_invert=
 Ssequence(Sassign(Evar _src secp_frame_type)(Etempvar _src secp_frame_type))field_invert_rest.
Proof. reflexivity. Qed.

Theorem eval_secp_fe_invert_initialized env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
 (value:Ty.tySem(Word 8)) :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_fe_state m0 -> write_frame_at m0 bd dbase bw outedge cursor N -> 256<=N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc(map Some(frame_input_word_bits value)) ->
 0<=rc -> rc+256<=Int64.max_unsigned -> exists mf,
 Clight2.eval_funcall secp_ge m0(Internal f_simplicity_fe_invert)
  [Vptr bd(Ptrofs.repr dbase);Vptr bs(Ptrofs.repr sbase);env] E0 mf(Vint Int.one) /\
 finv m0 bd dbase bw outedge cursor N bi mf true(encode(@literal_fe_invert Alg.CoreFunSem value)) /\
 lframe(fun b _=>~extA m0 bd bw bi b)m0 mf /\ modinfo_fe_state mf /\ readonly_preserved m0 mf.
Proof.
 intros CountCall Ready HO Capacity Base Align Fields HI Hrc HM.
 destruct(Mem.alloc m0 0 16) as[ma bl] eqn:HA.
 destruct(Mem.alloc ma 0 40) as[mb ba] eqn:HB.
 pose proof(field_invert_entry env m0 ma mb bl ba bd dbase bs sbase HA HB) as Entry.
 destruct(secp_prepare_public_locals env m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
  HA HB HO Capacity Base Align Fields)
  as(mc & Copy & FreeA & FreeL & LocalFields & Separate & Sep & Inv & PrepFrame & FreshA & FreshL).
 assert(EntryReadonly:readonly_preserved m0 mb) by(eapply entry_preserved;exact Entry).
 assert(CopyReadonly:readonly_preserved mb mc).
 { eapply secp_closed_stmt_preserved;[exact Copy|eapply entry_plain;[exact Entry|reflexivity]|reflexivity]. }
 assert(ReadyC:modinfo_fe_state mc).
 { exact(proj1(modinfo_fe_state_preserved m0 mc Ready(preserved_trans m0 mb mc EntryReadonly CopyReadonly))). }
 destruct(exec_field_invert_rest(secp_public_temps env bd dbase bs sbase)
  m0 bd dbase bw outedge cursor N bi edge rc value mc ba bl CountCall eq_refl HO HI Hrc HM
  FreeA FreeL LocalFields Separate Sep Inv ReadyC)
  as(mw & Rest & Final & FinalFreeA & FinalFreeL & RestFrame & ReadyW & RestReadonly).
 destruct(secp_free_public_locals mw bl ba Separate FinalFreeL FinalFreeA) as(mf & Free & FreeFrame).
 assert(FreeExt:eqext m0 bd bw bi mw mf).
 { eapply lframe_implies;[exact FreeFrame|].
   intros b pos[_ Valid] _;split;intro Same;subst b;contradiction. }
 assert(FreeReadonly:readonly_preserved mw mf) by(eapply freelist_preserved;exact Free).
 exists mf;split.
 - eapply eval_funcall_internal with(e:=secp_public_env bl ba)
   (le1:=secp_public_temps env bd dbase bs sbase)(le2:=secp_public_temps env bd dbase bs sbase)
   (m1:=mb)(m2:=mw)(out:=Out_return(Some(Vint Int.one,tint))).
   + exact Entry.
   + rewrite field_invert_public_body;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mc)
     (le1:=secp_public_temps env bd dbase bs sbase);eassumption.
   + cbn;split;[discriminate|reflexivity].
   + exact Free.
 - split;[eapply finv_stable;[exact HO|exact Final|exact FreeExt]|];split.
   + assert(Outside:lframe(fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b)m0 mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact PrepFrame|];intros b pos[Valid _] _;
         split;intro Same;subst b;contradiction.
       - eapply lframe_trans.
         + eapply lframe_implies;[exact RestFrame|];intros b pos[Valid Ext] _;unfold secp_locals_outside.
           split;[intro Same;subst b;contradiction|];split;[intro Same;subst b;contradiction|exact Ext].
         + eapply lframe_implies;[exact FreeFrame|];intros b pos[Valid _] _;
           split;intro Same;subst b;contradiction. }
     eapply lframe_implies;[exact Outside|];intros b pos Ext Valid;split;assumption.
   + split;[exact(proj1(modinfo_fe_state_preserved mw mf ReadyW FreeReadonly))|].
     eapply preserved_trans;[exact EntryReadonly|];eapply preserved_trans;[exact CopyReadonly|].
     eapply preserved_trans;[exact RestReadonly|exact FreeReadonly].
Qed.
