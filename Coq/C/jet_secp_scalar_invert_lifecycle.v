(** Complete unchanged scalar-invert C call: actual entry, copy, three helper
    calls, return and freeing. Only the deferred counting-call premise remains. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_exec C.jet_readBit_layout C.jet_frame_layout C.jet_frame_inv
 C.jet_encoding C.jet_input_layout C.jet_output_layout C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame
 C.jet_secp_linkage C.jets_secp C.jet_secp_public_body C.jet_secp_wrapper_run
 C.jet_secp_scalar_public_entry C.jet_secp_scalar_public_setup C.jet_secp_scalar_invert_literal
 C.jet_secp_scalar_invert_rest C.jet_secp_modinfo_scalar_initialized C.jet_secp_scalar_io_preserve
 C.jet_secp_closed_helpers C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_scalar_invert encode.

Definition scalar_invert_temps (v_env:val) bd dbase bs sbase : temp_env :=
 PTree.set _env v_env (PTree.set _src (Vptr bs(Ptrofs.repr sbase))
  (PTree.set _dst (Vptr bd(Ptrofs.repr dbase))
   (create_undef_temps(fn_temps f_simplicity_scalar_invert)))).
Lemma scalar_invert_entry v_env m ma mb bl ba bd dbase bs sbase :
 Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 32=(mb,ba) ->
 function_entry2 secp_ge f_simplicity_scalar_invert
  [Vptr bd(Ptrofs.repr dbase);Vptr bs(Ptrofs.repr sbase);v_env] m
  (scalar_public_env bl ba)(scalar_invert_temps v_env bd dbase bs sbase) mb.
Proof.
 intros HA HB;constructor.
 - cbn;repeat constructor;cbn;intuition discriminate.
 - cbn;repeat constructor;cbn;intuition discriminate.
 - intros x y HX HY HE;cbn in HX,HY.
   repeat match goal with H:_ \/ _ |- _=>destruct H end;subst;
    first[contradiction|vm_compute in HE;discriminate|congruence].
 - eapply alloc_variables_cons with(m1:=ma)(b1:=bl).
   + change(Mem.alloc m 0 16=(ma,bl));exact HA.
   + eapply alloc_variables_cons with(m1:=mb)(b1:=ba).
     * change(Mem.alloc ma 0 32=(mb,ba));exact HB.
     * constructor.
 - reflexivity.
Qed.
Lemma scalar_invert_src_temp v_env bd dbase bs sbase :
 (scalar_invert_temps v_env bd dbase bs sbase)!_src=Some(Vptr bs(Ptrofs.repr sbase)).
Proof. unfold scalar_invert_temps;rewrite PTree.gso by discriminate;apply PTree.gss. Qed.
Lemma scalar_invert_public_body : fn_body f_simplicity_scalar_invert=
 Ssequence(Sassign(Evar _src secp_frame_type)(Etempvar _src secp_frame_type)) scalar_invert_rest.
Proof. reflexivity. Qed.

Theorem eval_secp_scalar_invert_initialized v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
 (value:Ty.tySem(Word 8)) :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_scalar_initialized m0 ->
 write_frame_at m0 bd dbase bw outedge cursor N -> 256<=N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc (map Some(frame_input_word_bits value)) ->
 0<=rc -> rc+256<=Int64.max_unsigned -> exists mf,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_scalar_invert)
  [Vptr bd(Ptrofs.repr dbase);Vptr bs(Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
 finv m0 bd dbase bw outedge cursor N bi mf true
  (encode(@literal_scalar_invert Alg.CoreFunSem value)) /\
 lframe(fun b _=>~extA m0 bd bw bi b) m0 mf /\ modinfo_scalar_initialized mf /\
 readonly_preserved m0 mf.
Proof.
 intros CountCall Ready HO Capacity Base Align Fields HI Hrc HM.
 destruct(Mem.alloc m0 0 16) as[ma bl] eqn:HA.
 destruct(Mem.alloc ma 0 32) as[mb ba] eqn:HB.
 pose proof(scalar_invert_entry v_env m0 ma mb bl ba bd dbase bs sbase HA HB) as Entry.
 destruct(scalar_prepare_public_locals(scalar_invert_temps v_env bd dbase bs sbase)
  m0 ma bl ba mb bd dbase bs sbase bw outedge cursor N bi edge rc value
  HA HB HO ltac:(lia) Base Align Fields (scalar_invert_src_temp v_env bd dbase bs sbase))
  as(mc & Copy & FreeA & FreeL & LocalFields & Separate & Sep & Inv & PrepFrame & FreshA & FreshL).
 assert(EntryReadonly:readonly_preserved m0 mb) by(eapply entry_preserved;exact Entry).
 assert(CopyReadonly:readonly_preserved mb mc).
 { eapply secp_closed_stmt_preserved;[exact Copy|eapply entry_plain;[exact Entry|reflexivity]|reflexivity]. }
 assert(ReadyC:modinfo_scalar_initialized mc).
 { eapply modinfo_scalar_initialized_preserved;[exact Ready|].
   eapply preserved_trans;[exact EntryReadonly|exact CopyReadonly]. }
 assert(Inv256:invA m0 bd dbase bw outedge cursor N bi rc false [] 256
  (read_fe_rho(frame_input_word_bits value)rc) [] mc).
 { destruct Inv as[Rho [Final [_ Written]]].
   split;[exact Rho|];split;[exact Final|];split;[exact Capacity|cbn;lia]. }
 assert(Dst:(scalar_invert_temps v_env bd dbase bs sbase)!_dst=Some(Vptr bd(Ptrofs.repr dbase))).
 { unfold scalar_invert_temps;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 destruct(exec_scalar_invert_rest(scalar_invert_temps v_env bd dbase bs sbase)
  m0 bd dbase bw outedge cursor N bi edge rc value mc ba bl CountCall Dst HO HI Hrc HM
  FreeA FreeL LocalFields Separate Sep Inv256 ReadyC)
  as(mw & Rest & Final & FinalFreeA & FinalFreeL & RestFrame & ReadyW & RestReadonly).
 destruct(scalar_free_public_locals mw bl ba Separate FinalFreeL FinalFreeA)
  as(mf & Free & FreeFrame).
 assert(FreeExt:eqext m0 bd bw bi mw mf).
 { eapply lframe_implies;[exact FreeFrame|].
   intros b pos[_ Valid] _;split;intro Same;subst b;contradiction. }
 assert(FreeReadonly:readonly_preserved mw mf) by(eapply freelist_preserved;exact Free).
 exists mf;split.
 - eapply eval_funcall_internal with(e:=scalar_public_env bl ba)
   (le1:=scalar_invert_temps v_env bd dbase bs sbase)
   (le2:=scalar_invert_temps v_env bd dbase bs sbase)(m1:=mb)(m2:=mw)
   (out:=Out_return(Some(Vint Int.one,tint))).
   + exact Entry.
   + rewrite scalar_invert_public_body.
     eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mc)
      (le1:=scalar_invert_temps v_env bd dbase bs sbase);eassumption.
   + cbn;split;[discriminate|reflexivity].
   + exact Free.
 - split;[eapply finv_stable;[exact HO|exact Final|exact FreeExt]|];split.
   + assert(Outside:lframe(fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact PrepFrame|].
         intros b pos[Valid _] _;split;intro Same;subst b;contradiction.
       - eapply lframe_trans.
         + eapply lframe_implies;[exact RestFrame|].
           intros b pos[Valid Ext] _;unfold secp_locals_outside.
           split;[intro Same;subst b;contradiction|];
            split;[intro Same;subst b;contradiction|exact Ext].
         + eapply lframe_implies;[exact FreeFrame|].
           intros b pos[Valid _] _;split;intro Same;subst b;contradiction. }
     eapply lframe_implies;[exact Outside|];intros b pos Ext Valid;split;assumption.
   + split;[exact(modinfo_scalar_initialized_preserved mw mf ReadyW FreeReadonly)|].
     eapply preserved_trans;[exact EntryReadonly|].
     eapply preserved_trans;[exact CopyReadonly|].
     eapply preserved_trans;[exact RestReadonly|exact FreeReadonly].
Qed.
