(** Entire unchanged public jet: allocation, copy, guarded remainder and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_body C.jet_secp_x_equiv_literal C.jet_secp_rescale_public_reads.
Require Import C.jet_secp_x_equiv_public_statements C.jet_secp_x_equiv_public_lifecycle C.jet_secp_x_equiv_public_rest.
Import ListNotations Clightdefs Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_x_equiv Simplicity.Translate.encode.

Theorem eval_gej_x_equiv_literal_public v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (q x y z : tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 1<=N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits q)) ->
  frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits x)) ->
  frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits y)) ->
  frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits z)) ->
  0<=rc -> rc+1024<=Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_x_equiv)
      [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_gej_x_equiv Alg.CoreFunSem (q,((x,y),z)))) /\
    lframe (fun b _ => ~extA m0 bd bw bi b) m0 mf.
Proof.
  intros HO HN HBase HAlign HFields HQ HX HY HZ Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ma bl] eqn:AL.
  destruct (Mem.alloc ma 0 40) as [mb bq] eqn:AQ.
  destruct (Mem.alloc mb 0 128) as [mc bp] eqn:AP.
  set (le := x_equiv_public_temps v_env bd dbase bs sbase).
  destruct (x_equiv_prepare_public le m0 ma mb mc bl bq bp bd dbase bs sbase bw outedge cursor N bi edge rc
    AL AQ AP ltac:(unfold le,x_equiv_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
    HO HBase HAlign HFields)
    as (md & CCopy & FPD & FQD & FLD & SrcD & HPL & HQL & HPQ & HSep & FinD & FrameD & NP & NQ & NL).
  destruct (exec_x_equiv_public_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc q x y z md bp bq bl
    ltac:(unfold le,x_equiv_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    HO HN HQ HX HY HZ Hrc HM FPD FQD FLD SrcD HPL HQL HPQ HSep FinD)
    as (le' & mw & CRest & FinW & FPW & FQW & FLW & FrameW).
  destruct (x_equiv_free_public mw bl bq bp HPL HQL HPQ FLW FPW FQW) as (mf & HFree & FrameF).
  assert (ExtF : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies;[exact FrameF|]. intros b pos [_ HV] _;repeat split;intro HE;subst b;contradiction. }
  exists mf. split.
  - eapply eval_funcall_internal with (e:=x_equiv_public_env bl bq bp) (le1:=le) (le2:=le')
      (m1:=mc) (m2:=mw) (out:=Out_return (Some (Vint Int.one,tint))).
    + eapply x_equiv_public_entry;eassumption.
    + rewrite x_equiv_public_body_source.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);eassumption.
    + cbn;split;[discriminate|reflexivity].
    + exact HFree.
  - split;[eapply finv_stable;[exact HO|exact FinW|exact ExtF]|].
    assert (HF : lframe (fun b _ => Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
    { eapply lframe_trans.
      - eapply lframe_implies;[exact FrameD|]. intros b pos [HV HE] _;repeat split;intro HB;subst b;contradiction.
      - eapply lframe_trans.
        + eapply lframe_implies;[exact FrameW|]. intros b pos [HV HE] _;unfold rescale_locals_outside.
          repeat split;try exact HE;intro HB;subst b;contradiction.
        + eapply lframe_implies;[exact FrameF|]. intros b pos [HV HE] _;repeat split;intro HB;subst b;contradiction. }
    eapply lframe_implies;[exact HF|]. intros b pos HE HV;split;assumption.
Qed.
