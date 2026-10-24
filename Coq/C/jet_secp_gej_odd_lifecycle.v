(** Complete original public gej_y_is_odd call, with arbitrary valid frames,
    exact literal output and all public local frees. CTZ stays explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.extraMath C.jet_exec C.jet_sx_exec C.jet_sx_mem C.jet_frame_inv C.jet_secp_frame
 C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_secp_curve_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_wrapper_run C.jet_secp_gej_norm_infinity C.jet_secp_gej_odd_entry C.jet_secp_gej_odd_body
 C.jet_secp_gej_odd_rest C.jet_secp_gej_odd_literal C.jet_secp_read_gej_fields C.jet_secp_rescale_public_reads
 C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state C.jet_secp_closed_helpers
 C.jet_secp_gej_predicate_body C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_y_is_odd Simplicity.Translate.encode.

Theorem eval_gej_y_is_odd_initialized envv m0 bd base bs sbase bw edge cursor N bi inedge rc
 (x y z:Ty.tySem Word256) :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 modinfo_fe_state m0 -> write_frame_at m0 bd base bw edge cursor N -> 1<=N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
 frame_input_cells_at m0 bi inedge rc(map Some(frame_input_word_bits x)) ->
 frame_input_cells_at m0 bi inedge(rc+256)(map Some(frame_input_word_bits y)) ->
 frame_input_cells_at m0 bi inedge(rc+512)(map Some(frame_input_word_bits z)) ->
 0<=rc -> rc+768<=Int64.max_unsigned -> exists mf,
 Clight2.eval_funcall secp_ge m0(Internal f_simplicity_gej_y_is_odd)
  [Vptr bd(Ptrofs.repr base);Vptr bs(Ptrofs.repr sbase);envv]E0 mf(Vint Int.one) /\
 finv m0 bd base bw edge cursor N bi mf true
  (Simplicity.Translate.encode(@literal_gej_y_is_odd Alg.CoreFunSem ((x,y),z))) /\
 lframe(fun b _=>~extA m0 bd bw bi b)m0 mf /\ modinfo_fe_state mf /\ readonly_preserved m0 mf.
Proof.
 intros CountCall Ready Output Cap Base Align Source IX IY IZ RC Max.
 destruct(gej_norm_prepare envv m0 bd base bs sbase bw edge cursor N bi inedge rc Output Base Align Source)
  as(bl & bp & br & mc & md & NormalEntry & NormalCopy & LocalFields & FLD & FPD & FRD & PL & RP & RL &
   Old & Sep & Fin & Globals & PrepFrame).
 pose proof(gej_odd_entry_from_normalize _ _ _ _ _ _ _ _ _ _ NormalEntry) as Entry.
 pose proof(gej_odd_copy_from_normalize _ _ _ _ _ _ NormalCopy) as Copy.
 rewrite <-gej_odd_temps_match in Copy.
 set(le:=gej_odd_temps envv bd base bs sbase).
 assert(Plain:plain_env(gej_odd_env bl bp br)) by(eapply entry_plain;[exact Entry|reflexivity]).
 assert(EntryReadonly:readonly_preserved m0 mc) by(eapply entry_preserved;exact Entry).
 assert(CopyReadonly:readonly_preserved mc md).
 { eapply secp_closed_stmt_preserved;[exact Copy|exact Plain|reflexivity]. }
 assert(SepRead:xsep(extA m0 bd bw bi)[(bp,0);(bl,0)]).
 { intros [|[|r]] Bound;[exact(Sep 0%nat ltac:(cbn;lia))|exact(Sep 2%nat ltac:(cbn;lia))|cbn in Bound;lia]. }
 assert(ReadInv:invA m0 bd base bw edge cursor N bi rc false [] 1(read_fe_rho(frame_input_word_bits x)rc)[]md).
 { split;[reflexivity|];split;[exact Fin|];split;[exact Cap|cbn;lia]. }
 destruct(eval_read_gej_canonical_fields m0 bd base bw edge cursor N 1 bi inedge rc x y z md bp bl
  Output IX IY IZ RC Max FPD FLD LocalFields PL SepRead ReadInv)
  as(mr & Read & XR & YR & ZR & Flag & SourceR & FPR & FLR & InvR & ReadFrame).
 rewrite !rescale_reader_limbs in XR,YR,ZR.
 destruct InvR as[_[FinR _]];change(finv m0 bd base bw edge cursor N bi mr false []) in FinR.
 assert(FRR:Mem.range_perm mr br 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FRD|exact ReadFrame|];intros;split;[exact RP|];split;
    [exact RL|exact(Sep 1%nat ltac:(cbn;lia))]. }
 pose proof(proj2(internal_exec_preserved _ _ gej_reader_internal_table_correct)
  _ _ _ _ _ _ Read gej_reader_allowed) as ReadReadonly.
 assert(ReadyR:modinfo_fe_state mr).
 { exact(proj1(modinfo_fe_state_preserved md mr(Globals Ready)ReadReadonly)). }
 destruct(exec_gej_odd_rest_initialized le m0 bd base bw edge cursor N bi mr bl bp br x y z
  CountCall eq_refl Output Cap FinR XR YR ZR Flag ReadyR FPR FLR FRR PL RP RL Sep)
  as(lef & mw & Rest & Final & FPW & FLW & FRW & RestFrame & ReadyW & RestReadonly).
 destruct(free_list_exists[(bl,0,16);(bp,0,128);(br,0,88)]mw) as(mf & Free & FreeUnchanged).
 { cbn;repeat constructor;cbn;intuition congruence. }
 { intros b lo hi[E|[E|[E|[]]]];injection E as <- <- <-;assumption. }
 assert(FreeFrame:lframe(fun b _=>b<>bl /\ b<>bp /\ b<>br)mw mf).
 { eapply lframe_implies;[apply lframe_unchanged;exact FreeUnchanged|].
   intros b pos(NL & NP & NR)Valid;cbn;intuition congruence. }
 assert(FreeExt:eqext m0 bd bw bi mw mf).
 { eapply lframe_implies;[exact FreeFrame|];intros b pos[_ Valid]_;apply Old;exact Valid. }
 assert(FreeReadonly:readonly_preserved mw mf) by(eapply freelist_preserved;exact Free).
 exists mf;split.
 - eapply eval_funcall_internal with(e:=gej_odd_env bl bp br)(le1:=le)(le2:=lef)(m1:=mc)(m2:=mw)
   (out:=Out_return(Some(Vint Int.one,tint))).
   + exact Entry.
   + rewrite gej_odd_body_source;eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=md)(le1:=le);[exact Copy|].
     eapply exec_Sseq_1 with(t1:=E0)(t2:=E0)(m1:=mr)(le1:=le);
      [apply(exec_gej_odd_read le md mr bl bp br);exact Read|exact Rest].
   + cbn;split;[discriminate|reflexivity].
   + rewrite gej_odd_blocks;exact Free.
 - split;[eapply finv_stable;[exact Output|exact Final|exact FreeExt]|];split.
   + assert(Outside:lframe(fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b)m0 mf).
     { eapply lframe_trans.
       - eapply lframe_implies;[exact PrepFrame|];intros b pos(Valid & NE)_;apply Old;exact Valid.
       - eapply lframe_trans.
         + eapply lframe_implies;[exact ReadFrame|];intros b pos(Valid & NE)_.
           destruct(Old b Valid) as(NL & NP & NR);split;[exact NP|];split;assumption.
         + eapply lframe_trans.
           * eapply lframe_implies;[exact RestFrame|];intros b pos(Valid & NE)_.
             destruct(Old b Valid) as(NL & NP & NR);split;[exact NP|];split;[exact NR|];split;assumption.
           * eapply lframe_implies;[exact FreeFrame|];intros b pos(Valid & NE)_;apply Old;exact Valid. }
     eapply lframe_implies;[exact Outside|];intros b pos NE Valid;split;assumption.
   + split;[exact(proj1(modinfo_fe_state_preserved mw mf ReadyW FreeReadonly))|].
     eapply preserved_trans;[exact EntryReadonly|];eapply preserved_trans;[exact CopyReadonly|].
     eapply preserved_trans;[exact ReadReadonly|];eapply preserved_trans;[exact RestReadonly|exact FreeReadonly].
Qed.
