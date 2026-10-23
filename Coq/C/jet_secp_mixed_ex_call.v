(** Complete original extended public call for every input: entry, the six
    calls, all four local allocations and their frees, with the actual output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
  C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_public_copy
  C.jet_secp_mixed_ex_public_body C.jet_secp_mixed_ex_public_entry C.jet_secp_mixed_ex_public_prepare
  C.jet_secp_mixed_ex_public_rest C.jet_secp_mixed_ex_rest C.jet_secp_rescale_public_body C.jet_secp_square_spec_bridge
  C.jet_secp_mixed_finite_return C.jet_secp_multiply_finish_product C.jet_secp_fe_math C.jet_secp_canonical_zero.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge Simplicity.Translate.encode.

Theorem eval_gej_ge_add_ex_public v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (x y z u v : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 1024<=N ->
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
  frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits u)) ->
  frame_input_cells_at m0 bi edge (rc+1024) (map Some (frame_input_word_bits v)) ->
  0<=rc -> rc+1280<=Int64.max_unsigned ->
  exists mf,
  Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_ge_add_ex)
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
  finv m0 bd dbase bw outedge cursor N bi mf true (mixed_ex_output x y z u v) /\
  lframe (fun b _=>~extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HN HBase HAlign HSource HX HY HZ HU HV Hrc HM.
  destruct (Mem.alloc m0 0 16) as (m1 & bl) eqn:AL.
  destruct (Mem.alloc m1 0 128) as (m2 & bp) eqn:AP.
  destruct (Mem.alloc m2 0 88) as (m3 & ba) eqn:AA.
  destruct (Mem.alloc m3 0 40) as (mi & br) eqn:AR.
  destruct (mixed_ex_allocations_fresh m0 m1 m2 m3 mi bl bp ba br AL AP AA AR)
    as ((NewL & NewP & NewA & NewR) & Sep).
  set (le:=secp_public_temps v_env bd dbase bs sbase).
  destruct (mixed_ex_prepare_public le m0 m1 m2 m3 mi bl bp ba br bd dbase bs sbase bw outedge cursor N bi edge rc
    AL AP AA AR ltac:(unfold le,secp_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
    HO HBase HAlign HSource) as (mp & Copy & FPP & FAP & FLP & FRP & SrcP & SepP & FinP & FrameP).
  destruct (exec_mixed_ex_rest le m0 bd dbase bw outedge cursor N bi edge rc x y z u v mp bp ba bl br
    ltac:(unfold le,secp_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    HO HN HX HY HZ HU HV Hrc HM Sep FPP FAP FLP FRP SrcP SepP FinP)
    as (mw & Rest & FinW & FPW & FAW & FLW & FRW & FrameW).
  destruct (mixed_ex_free_public_locals mw bl bp ba br Sep FLW FPW FAW FRW) as (mf & Free & FrameF).
  assert (ExtF : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies;[exact FrameF|];intros b pos (_ & HB0) HBW;
      repeat split;intro EQ;subst b;contradiction. }
  exists mf;split.
  - eapply eval_funcall_internal with (e:=mixed_ex_public_env bl bp ba br) (le1:=le) (le2:=le)
      (m1:=mi) (m2:=mw) (out:=Out_return (Some (Vint Int.one,tint))).
    + eapply mixed_ex_public_entry;eassumption.
    + rewrite mixed_ex_public_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mp) (le1:=le);eassumption.
    + cbn;split;[discriminate|reflexivity].
    + exact Free.
  - split;[eapply finv_stable;[exact HO|exact FinW|exact ExtF]|].
    assert (Frame : lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FrameP|];intros b pos (HB0 & HE) HCur;
          repeat split;intro EQ;subst b;contradiction.
      - eapply lframe_trans.
        + eapply lframe_implies;[exact FrameW|];intros b pos (HB0 & HE) HCur;
            unfold mixed_ex_public_outside;repeat split;try exact HE;intro EQ;subst b;contradiction.
        + eapply lframe_implies;[exact FrameF|];intros b pos (HB0 & HE) HCur;
            repeat split;intro EQ;subst b;contradiction. }
    eapply lframe_implies;[exact Frame|];intros b pos HE HCur;split;assumption.
Qed.
