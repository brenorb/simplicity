(** Actual by-value source copy after all four public local allocations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_input_layout
  C.jet_output_layout C.jet_frame_inv C.jet_sx_expr C.jet_sx_state C.jet_sx_mem C.jet_sx_exec
  C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_rescale_public_body
  C.jet_secp_mixed_ex_public_body C.jet_secp_mixed_ex_public_entry.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem mixed_ex_prepare_public le m0 m1 m2 m3 mi bl bp ba br bd dbase bs sbase bw outedge cursor N bi edge rc :
  Mem.alloc m0 0 16=(m1,bl) -> Mem.alloc m1 0 128=(m2,bp) ->
  Mem.alloc m2 0 88=(m3,ba) -> Mem.alloc m3 0 40=(mi,br) ->
  le!_src=Some (Vptr bs (Ptrofs.repr sbase)) -> write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  exists mf,
  Clight2.exec_stmt secp_ge (mixed_ex_public_env bl bp ba br) le mi rescale_public_copy E0 le mf Out_normal /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bl 0 16 Cur Freeable /\ Mem.range_perm mf br 0 40 Cur Freeable /\
  frame_fields_at mf bl 0 bi edge rc /\
  xsep (extA m0 bd bw bi) [(bp,0);(ba,0);(bl,0);(br,0)] /\
  finv m0 bd dbase bw outedge cursor N bi mf false [] /\
  lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bl /\ b<>br) m0 mf.
Proof.
  intros AL AP AA AR HTemp HO HBase HAlign HFields.
  destruct (mixed_ex_allocations_fresh m0 m1 m2 m3 mi bl bp ba br AL AP AA AR)
    as ((NewL & NewP & NewA & NewR) & Sep).
  destruct (mixed_ex_allocations_free m0 m1 m2 m3 mi bl bp ba br AL AP AA AR) as (FL & FP & FA & FR).
  pose proof (mixed_ex_allocations_frame (fun _ _=>True) m0 m1 m2 m3 mi bl bp ba br AL AP AA AR) as Alloc.
  assert (Source : frame_fields_at mi bs sbase bi edge rc).
  { destruct HFields as (HE & HC);pose proof (load_valid m0 Mptr bs sbase _ HE) as HV.
    split;rewrite (proj1 Alloc) by auto;assumption. }
  destruct Source as (HEdge & HCursor).
  destruct (frame_loadbytes_at mi bs sbase _ _ HEdge HCursor) as (bytes & Load).
  pose proof (Mem.loadbytes_length _ _ _ _ _ Load) as Length.
  assert (Writable : Mem.range_perm mi bl 0 (0+Z.of_nat (length bytes)) Cur Writable).
  { rewrite Length;apply freeable_range_writable;exact FL. }
  destruct (Mem.range_perm_storebytes mi bl 0 bytes Writable) as (mf & Store).
  assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bl /\ b<>br) m0 mf).
  { eapply lframe_trans;[eapply mixed_ex_allocations_frame;eassumption|].
    apply lframe_unchanged;eapply Mem.storebytes_unchanged_on;[exact Store|].
    intros pos HP (_ & _ & NL & _);apply NL;reflexivity. }
  assert (Ext : eqext m0 bd bw bi m0 mf).
  { eapply lframe_implies;[exact Frame|].
    intros b pos (_ & HV) _;repeat split;intro HE;subst b;contradiction. }
  assert (HU : Ptrofs.unsigned (Ptrofs.repr sbase)=sbase).
  { apply Ptrofs.unsigned_repr;unfold frame_base_valid in HBase;lia. }
  exists mf;split.
  - unfold rescale_public_copy;eapply exec_Sassign_copy.
    + apply eval_Evar_local;reflexivity.
    + apply eval_Etempvar;exact HTemp.
    + reflexivity.
    + eapply assign_loc_copy with (b':=bs) (ofs':=Ptrofs.repr sbase) (bytes:=bytes).
      * reflexivity.
      * intros _;change (8|Ptrofs.unsigned (Ptrofs.repr sbase));rewrite HU;exact HAlign.
      * intros _;change (8|0);exists 0;reflexivity.
      * left;intro HE;apply NewL;subst bs;exact (load_valid m0 Mptr bl sbase _ (proj1 HFields)).
      * change (Mem.loadbytes mi bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16=Some bytes);rewrite HU;exact Load.
      * exact Store.
  - split;[intros pos HP;eapply Mem.perm_storebytes_1;[exact Store|apply FP;exact HP]|].
    split;[intros pos HP;eapply Mem.perm_storebytes_1;[exact Store|apply FA;exact HP]|].
    split;[intros pos HP;eapply Mem.perm_storebytes_1;[exact Store|apply FL;exact HP]|].
    split;[intros pos HP;eapply Mem.perm_storebytes_1;[exact Store|apply FR;exact HP]|].
    split;[exact (frame_copy_fields_at mi mf bs sbase bl bytes _ _ Load Store HEdge HCursor)|].
    split.
    + intros [|[|[|[|r]]]] HI;cbn [blk bas lay nth fst snd];unfold extA,fext;
        [intros (_ & HV);contradiction|intros (_ & HV);contradiction|
         intros (_ & HV);contradiction|intros (_ & HV);contradiction|cbn in HI;lia].
    + split;[eapply finv_stable;[exact HO|apply finv_init;exact HO|exact Ext]|exact Frame].
Qed.
