(** Whole original public SWU call, including frame copy, reader, mapper,
    affine writer, return and frees. Startup and CTZ are explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.extraMath C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
  C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp
  C.jet_secp_swu_public_boundary C.jet_secp_swu_public_body C.jet_secp_swu_public_rest
  C.jet_secp_decompress_public_entry C.jet_secp_decompress_public_prepare C.jet_secp_rescale_public_reads
  C.jet_secp_swu_startup C.jet_secp_swu_literal C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode literal_swu.

Theorem eval_swu_literal_public v_env m0 bd base bs sbase bw outedge cursor N bi edge rc
    (t:Ty.tySem (Word 8)) :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  swu_startup m0 -> write_frame_at m0 bd base bw outedge cursor N -> 512<=N ->
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits t)) ->
  0<=rc -> rc+256<=Int64.max_unsigned -> exists mf,
  Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_swu)
    [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
  finv m0 bd base bw outedge cursor N bi mf true
    (Simplicity.Translate.encode (@literal_swu Simplicity.Alg.CoreFunSem t)) /\
  lframe (fun b _=>~extA m0 bd bw bi b) m0 mf /\ swu_startup mf /\ readonly_preserved m0 mf.
Proof.
  intros Count Ready Output Cap Base Align Source Input RC Max.
  destruct (Mem.alloc m0 0 16) as (ma & bl) eqn:A.
  destruct (Mem.alloc ma 0 40) as (mb & bt) eqn:B.
  destruct (Mem.alloc mb 0 88) as (mc & bp) eqn:C.
  destruct (decompress_public_allocations_fresh m0 ma mb mc bl bt bp A B C)
    as (FreshL & FreshT & FreshP & TL & PL & TP).
  set (le:=swu_public_temps v_env bd base bs sbase).
  pose proof (swu_public_entry v_env m0 ma mb mc bl bt bp bd base bs sbase A B C) as Entry.
  destruct (decompress_prepare_public le m0 ma mb mc bl bt bp bd base bs sbase bw outedge cursor N bi edge rc
    A B C ltac:(unfold le,swu_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
    Output Base Align Source) as (md & Copy & FTD & FPD & FLD & SourceD & Sep & InvD & FrameD).
  assert (ROEntry:readonly_preserved m0 mc) by (eapply entry_preserved;exact Entry).
  pose proof (swu_copy_readonly _ _ _ _ Copy) as ROCopy.
  assert (ReadyD:swu_startup md).
  { eapply swu_startup_preserved;[exact Ready|];eapply preserved_trans;[exact ROEntry|exact ROCopy]. }
  destruct (exec_swu_public_rest_owned le m0 bd base bw outedge cursor N bi edge rc t md bt bp bl
    Count ReadyD ltac:(unfold le,swu_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    Output Cap Input RC Max FTD FPD FLD SourceD TL PL TP Sep InvD)
    as (mw & Rest & Final & FTW & FPW & FLW & FrameW & ReadyW & ROW).
  destruct (swu_free_public_locals mw bl bt bp TL PL TP FLW FTW FPW) as (mf & Free & FrameF).
  pose proof (freelist_preserved _ _ _ Free) as ROFree.
  assert (ExtF:eqext m0 bd bw bi mw mf).
  { eapply lframe_implies;[exact FrameF|];intros b pos [_ Valid] _;
      repeat split;intro Same;subst b;contradiction. }
  assert (ReadOnly:readonly_preserved m0 mf) by
    (eapply preserved_trans;[exact ROEntry|];eapply preserved_trans;[exact ROCopy|];
     eapply preserved_trans;[exact ROW|exact ROFree]).
  exists mf;split.
  - eapply eval_funcall_internal with (e:=swu_public_env bl bt bp) (le1:=le) (le2:=le)
      (m1:=mc) (m2:=mw) (out:=Out_return (Some (Vint Int.one,tint))).
    + exact Entry.
    + rewrite swu_public_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le).
      * apply swu_copy_environment;exact Copy.
      * exact Rest.
    + split;[discriminate|reflexivity].
    + exact Free.
  - split;[eapply finv_stable;[exact Output|exact Final|exact ExtF]|];split.
    + assert (Frame:lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies;[exact FrameD|];intros b pos [Valid Outside] _;
            repeat split;intro Same;subst b;contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies;[exact FrameW|];intros b pos [Valid Outside] _;
              unfold rescale_locals_outside;repeat split;try exact Outside;intro Same;subst b;contradiction.
          + eapply lframe_implies;[exact FrameF|];intros b pos [Valid Outside] _;
              repeat split;intro Same;subst b;contradiction. }
      eapply lframe_implies;[exact Frame|];intros b pos Outside Valid;split;assumption.
    + split;[eapply swu_startup_preserved;[exact ReadyW|exact ROFree]|exact ReadOnly].
Qed.
