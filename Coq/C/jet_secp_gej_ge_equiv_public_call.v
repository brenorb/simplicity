(** Complete original public C equivalence jet over general frames.
    This is execution against its C-derived bit, not yet the literal specification. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_exec C.jet_encoding C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_sx_mem C.jet_sx_exec C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_mixed_public_entry C.jet_secp_mixed_public_prepare C.jet_secp_rescale_public_reads.
Require Import C.jet_secp_gej_ge_equiv_reader C.jet_secp_gej_ge_equiv_public_body
 C.jet_secp_gej_ge_equiv_public_rest.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge gej_ge_equiv_reader_bit.

Theorem eval_gej_ge_equiv_public_c_bit v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (x y z u v : Ty.tySem (Word 8)) :
 write_frame_at m0 bd dbase bw outedge cursor N -> 1<=N ->
 frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
 frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits x)) ->
 frame_input_cells_at m0 bi edge (rc+256) (map Some (frame_input_word_bits y)) ->
 frame_input_cells_at m0 bi edge (rc+512) (map Some (frame_input_word_bits z)) ->
 frame_input_cells_at m0 bi edge (rc+768) (map Some (frame_input_word_bits u)) ->
 frame_input_cells_at m0 bi edge (rc+1024) (map Some (frame_input_word_bits v)) ->
 0<=rc -> rc+1280<=Int64.max_unsigned ->
 exists mf,
 Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_gej_ge_equiv)
   [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] E0 mf (Vint Int.one) /\
 finv m0 bd dbase bw outedge cursor N bi mf true
   [Some (gej_ge_equiv_reader_bit x y z u v)] /\
 lframe (fun b _=>~extA m0 bd bw bi b) m0 mf.
Proof.
 intros HO HN HBase HAlign HSource HX HY HZ HU HV Hrc HM.
 destruct (Mem.alloc m0 0 16) as [ma bl] eqn:HA.
 destruct (Mem.alloc ma 0 128) as [mb bp] eqn:HB.
 destruct (Mem.alloc mb 0 88) as [mc ba] eqn:HC.
 destruct (mixed_allocations_fresh m0 ma mb mc bl bp ba HA HB HC)
   as (NewL & NewP & NewA & HPL & HAL & HPA).
 set (le:=gej_ge_equiv_public_temps v_env bd dbase bs sbase).
 destruct (mixed_prepare_public le m0 ma mb mc bl bp ba bd dbase bs sbase bw outedge cursor N bi edge rc
   HA HB HC ltac:(unfold le,gej_ge_equiv_public_temps;rewrite PTree.gso by discriminate;apply PTree.gss)
   HO HBase HAlign HSource) as (md & Copy & FPD & FAD & FLD & SrcD & HSep & FinD & FrameD).
 destruct (exec_gej_ge_equiv_public_rest_owned le m0 bd dbase bw outedge cursor N bi edge rc x y z u v md bp ba bl
   ltac:(unfold le,gej_ge_equiv_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
   HO HN HX HY HZ HU HV Hrc HM FPD FAD FLD SrcD HPL HAL HPA HSep FinD)
   as (mw & Rest & FinW & FPW & FAW & FLW & FrameW).
 destruct (mixed_free_public_locals mw bl bp ba HPL HAL HPA FLW FPW FAW) as (mf & Free & FrameF).
 assert (ExtF : eqext m0 bd bw bi mw mf).
 { eapply lframe_implies;[exact FrameF|];intros b pos [_ HB0] HBW;repeat split;intro HE;subst b;contradiction. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=mixed_public_env bl bp ba) (le1:=le) (le2:=PTree.set _t'1 (Vint (if gej_ge_equiv_reader_bit x y z u v then Int.one else Int.zero)) le)
    (m1:=mc) (m2:=mw) (out:=Out_return (Some (Vint Int.one,tint))).
   + eapply gej_ge_equiv_public_entry;eassumption.
   + rewrite gej_ge_equiv_public_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);eassumption.
   + cbn;split;[discriminate|reflexivity].
   + exact Free.
 - split;[eapply finv_stable;[exact HO|exact FinW|exact ExtF]|].
   assert (Frame : lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FrameD|];intros b pos [HB0 HE] HCur;repeat split;intro EQ;subst b;contradiction.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact FrameW|];intros b pos [HB0 HE] HCur;unfold rescale_locals_outside;
           repeat split;try exact HE;intro EQ;subst b;contradiction.
       + eapply lframe_implies;[exact FrameF|];intros b pos [HB0 HE] HCur;repeat split;intro EQ;subst b;contradiction. }
   eapply lframe_implies;[exact Frame|];intros b pos HE HCur;split;assumption.
Qed.
