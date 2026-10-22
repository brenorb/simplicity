(** Complete original public C square-root call, including entry, all body
    calls, both result branches, return conversion and three local frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_root_public_entry C.jet_secp_root_public_prepare C.jet_secp_root_public_body
 C.jet_secp_root_public_rest C.jet_secp_root_function_literal C.jet_secp_root_literal
 C.jet_secp_rescale_public_reads.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_fe_square_root Simplicity.Translate.encode root_reader_flag.

Theorem eval_fe_square_root_literal_public v_env m0 bd base bs sbase bw outedge cursor N bi edge rc
 (x : Ty.tySem (Word 8)) :
 write_frame_at m0 bd base bw outedge cursor N -> 257<=N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
 0<=rc -> rc+256<=Int64.max_unsigned -> exists mf,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_square_root)
  [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
 finv m0 bd base bw outedge cursor N bi mf true
  (Simplicity.Translate.encode (@literal_fe_square_root Simplicity.Alg.CoreFunSem x)) /\
 lframe (fun b _=>~extA m0 bd bw bi b) m0 mf.
Proof.
 intros HO HN HBase HAlign HSource HX Hrc HM.
 destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
 destruct (Mem.alloc ma 0 40) as [mb br] eqn:HB.
 destruct (Mem.alloc mb 0 40) as [mc ba] eqn:HC.
 destruct (root_public_allocations_fresh m0 ma mb mc bl br ba HA HB HC)
  as (NewL & NewR & NewA & HRL & HAL & HRA).
 set (le:=root_public_temps v_env bd base bs sbase).
 destruct (root_prepare_public le m0 ma mb mc bl br ba bd base bs sbase bw outedge cursor N bi edge rc
  HA HB HC ltac:(unfold le,root_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
  HO HBase HAlign HSource) as (md & Copy & FRD & FAD & FLD & SrcD & Sep & FinD & FrameD).
 destruct (exec_root_public_rest_owned le m0 bd base bw outedge cursor N bi edge rc x md br ba bl
  ltac:(unfold le,root_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
  HO HN HX Hrc HM FRD FAD FLD SrcD HRL HAL HRA Sep FinD)
  as (mw & Rest & FinW & FRW & FAW & FLW & FrameW).
 destruct (root_free_public_locals mw bl br ba HRL HAL HRA FLW FRW FAW) as (mf & Free & FrameF).
 assert (ExtF : eqext m0 bd bw bi mw mf).
 { eapply lframe_implies;[exact FrameF|];intros b pos [_ HB0] HBW;
   repeat split;intro HE;subst b;contradiction. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=root_public_env bl br ba) (le1:=le)
    (le2:=root_public_final_temps le (root_reader_flag x)) (m1:=mc) (m2:=mw)
    (out:=Out_return (Some (Vint Int.one,tint))).
   + eapply root_public_entry;eassumption.
   + rewrite root_public_body;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);eassumption.
   + cbn;split;[discriminate|reflexivity].
   + exact Free.
 - split;[eapply finv_stable;[exact HO|exact FinW|exact ExtF]|].
   assert (Frame : lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FrameD|];intros b pos [HB0 HE] HCur;
       repeat split;intro EQ;subst b;contradiction.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact FrameW|];intros b pos [HB0 HE] HCur;unfold rescale_locals_outside;
         repeat split;try exact HE;intro EQ;subst b;contradiction.
       + eapply lframe_implies;[exact FrameF|];intros b pos [HB0 HE] HCur;
         repeat split;intro EQ;subst b;contradiction. }
   eapply lframe_implies;[exact Frame|];intros b pos HE HCur;split;assumption.
Qed.
