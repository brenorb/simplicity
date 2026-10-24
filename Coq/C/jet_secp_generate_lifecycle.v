(** Complete original public generate on arbitrary valid frames/cursors.
    The only assumed executions are the explicitly deferred original wNAF
    memset steps. No scalar, generator-loop or public call is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep
  Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_exec C.jet_sx_exec C.jet_sx_mem C.jet_sx_state C.jet_sx_expr C.jet_secp_frame
  C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv C.jet_encoding
  C.jet_secp_linkage C.jets_secp C.jet_secp_public_copy C.jet_secp_scalar_add_reader_support
  C.jet_secp_scalar_public_rest C.jet_secp_scalar_reader_run C.jet_secp_wrapper_run
  C.jet_secp_scalar_io_preserve C.jet_secp_curve_frame C.jet_secp_generator_startup
  C.jet_secp_ecmult_generator C.jet_secp_generate_program C.jet_secp_point_output_literal
  C.jet_secp_generate_entry C.jet_secp_generate_body C.jet_clight_internal_preserve
  C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_generate Simplicity.Translate.encode.

Theorem eval_generate_initialized envv m0 bd base bs sbase bw edge cursor N bi inedge rc
    (value:Ty.tySem Word256) :
  (forall ma mi local ba b,Mem.alloc ma 0 32=(mi,local) ->
    Mem.range_perm ma b 0 516 Cur Freeable -> exists mz,
    Clight2.exec_stmt secp_ge (wnaf_env local)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero)))
      mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz) ->
  generator_startup m0 -> write_frame_at m0 bd base bw edge cursor N -> 768<=N ->
  frame_base_valid sbase -> (8|sbase) -> frame_fields_at m0 bs sbase bi inedge rc ->
  frame_input_cells_at m0 bi inedge rc (map Some (frame_input_word_bits value)) ->
  0<=rc -> rc+256<=Int64.max_unsigned -> exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_generate)
      [Vptr bd (Ptrofs.repr base);Vptr bs (Ptrofs.repr sbase);envv] E0 mf (Vint Int.one) /\
    finv m0 bd base bw edge cursor N bi mf true
      (Simplicity.Translate.encode (@literal_generate Alg.CoreFunSem value)) /\
    lframe (fun b _=>~extA m0 bd bw bi b) m0 mf /\ generator_startup mf.
Proof.
  intros ZeroSteps Ready Output Cap Base Align Source Input RC Max.
  destruct (generate_prepare envv m0 bd base bs sbase bw edge cursor N bi inedge rc
    Ready Output Base Align Source)
    as (bl & bp & bn & mc & md & Entry & Copy & FLD & FPD & FND & SrcD & PL & NL & PN &
        Old & Sep & FinD & ReadyD & PrepFrame).
  set (le:=secp_public_temps envv bd base bs sbase).
  assert (SepRead:xsep (extA m0 bd bw bi) [(bn,0);(bl,0)]).
  { intros [|[|r]] Index;[exact (Sep 1%nat ltac:(cbn;lia))|
      exact (Sep 2%nat ltac:(cbn;lia))|cbn in Index;lia]. }
  assert (InvD:invA m0 bd base bw edge cursor N bi rc false [] 768
    (read_fe_rho (frame_input_word_bits value) rc) [] md).
  { split;[reflexivity|];split;[exact FinD|];split;[exact Cap|cbn;lia]. }
  destruct (eval_read_scalar_canonical_with_source m0 bd base bw edge cursor N 768 bi inedge rc value
    md bn bl Output Input RC Max FND FLD SrcD NL SepRead InvD)
    as (mr & Read & Scalar & SrcR & FNR & FLR & InvR & ReaderFrame).
  assert (FinR:finv m0 bd base bw edge cursor N bi mr false []) by exact (proj1 (proj2 InvR)).
  assert (ReadyR:generator_startup mr).
  { apply (generator_startup_readonly md mr ReadyD);eapply scalar_reader_preserved;exact Read. }
  assert (PFR:Mem.range_perm mr bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact FPD|exact ReaderFrame|].
    intros pos;unfold frame;split;[eapply Mem.perm_valid_block;exact (FPD 0 ltac:(clear;lia))|].
    split;[apply scalar_locals_not_foot;assumption|exact (Sep 0%nat ltac:(cbn;lia))]. }
  destruct (eval_ecmult_generator value mr bp bn (secp_symbol_block _a) ReadyR PN PFR FNR Scalar ZeroSteps)
    as (mn & ox & oy & oz & Mult & X & Y & Z & Flag & FPN & FNN & BX & BY & BZ & Literal & ReadyN & MultFrame).
  assert (ExtN:eqext m0 bd bw bi mr mn).
  { eapply lframe_implies;[exact MultFrame|];intros b pos Ext Valid;split;intro E;subst b;
      [exact (Sep 0%nat ltac:(cbn;lia) Ext)|exact (Sep 1%nat ltac:(cbn;lia) Ext)]. }
  assert (FinN:finv m0 bd base bw edge cursor N bi mn false []).
  { eapply finv_stable;[exact Output|exact FinR|exact ExtN]. }
  assert (FLN:Mem.range_perm mn bl 0 16 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact FLR|exact MultFrame|intros;split;congruence]. }
  assert (SepPoint:xsep (extA m0 bd bw bi) [(bp,0)]).
  { intros [|r] Index;[exact (Sep 0%nat ltac:(cbn;lia))|cbn in Index;lia]. }
  destruct (eval_write_gej_literal_output m0 bd base bw edge cursor N bi rc mn bp ox oy oz
    (@literal_generate Alg.CoreFunSem value) Output Cap FinN BX BY BZ X Y Z FPN SepPoint Literal)
    as (mw & Write & FinW & FPW & WriterFrame).
  assert (FLW:Mem.range_perm mw bl 0 16 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact FLN|exact WriterFrame|].
    intros;split;[congruence|exact (Sep 2%nat ltac:(cbn;lia))]. }
  assert (FNW:Mem.range_perm mw bn 0 32 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact FNN|exact WriterFrame|].
    intros;split;[congruence|exact (Sep 1%nat ltac:(cbn;lia))]. }
  assert (ReadyW:generator_startup mw).
  { apply (generator_startup_readonly mn mw ReadyN);eapply generate_writer_preserved;exact Write. }
  destruct (free_list_exists [(bl,0,16);(bp,0,128);(bn,0,32)] mw) as (mf & Free & Unchanged).
  - clear -PL NL PN;cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [E|[E|[E|[]]]];injection E as <- <- <-;assumption.
  - assert (FreeFrame:lframe (fun b _=>b<>bp /\ b<>bn /\ b<>bl) mw mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos Outside Valid;clear -Outside;cbn in *;intuition congruence. }
    assert (FreeExt:eqext m0 bd bw bi mw mf).
    { eapply lframe_implies;[exact FreeFrame|];intros b pos [_ Valid] _;apply Old;exact Valid. }
    assert (ReadyF:generator_startup mf).
    { apply (generator_startup_readonly mw mf ReadyW);eapply freelist_preserved;exact Free. }
    exists mf;split.
    + eapply eval_funcall_internal with (e:=generate_public_env bl bp bn) (le1:=le) (le2:=le)
        (m1:=mc) (m2:=mw) (out:=Out_return (Some (Vint Int.one,tint))).
      * exact Entry.
      * rewrite generate_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le);
          [exact Copy|];eapply exec_generate_rest;
          [unfold le,secp_public_temps;rewrite !PTree.gso by discriminate;apply PTree.gss|
           exact Read|exact Mult|exact Write].
      * cbn;split;[discriminate|reflexivity].
      * rewrite generate_public_blocks;exact Free.
    + split;[eapply finv_stable;[exact Output|exact FinW|exact FreeExt]|];split;[|exact ReadyF].
      assert (WholeFrame:lframe (fun b _=>Mem.valid_block m0 b /\ ~extA m0 bd bw bi b) m0 mf).
      { eapply lframe_trans with (m2:=md).
        - eapply lframe_implies;[exact PrepFrame|];intros b pos [Valid Outside] _;apply Old;exact Valid.
        - eapply lframe_trans with (m2:=mr).
          + eapply lframe_implies;[exact ReaderFrame|];intros b pos [Valid Outside] Current;
              unfold frame;split;[exact Current|];split;
              [apply scalar_locals_not_foot;destruct (Old b Valid) as (NotP & NotN & NotL);assumption|exact Outside].
          + eapply lframe_trans with (m2:=mn).
            * eapply lframe_implies;[exact MultFrame|];intros b pos [Valid Outside] _;
                destruct (Old b Valid) as (NotP & NotN & NotL);split;assumption.
            * eapply lframe_trans with (m2:=mw).
              -- eapply lframe_implies;[exact WriterFrame|];intros b pos [Valid Outside] _;
                  split;[exact (proj1 (Old b Valid))|exact Outside].
              -- eapply lframe_implies;[exact FreeFrame|];intros b pos [Valid Outside] _;apply Old;exact Valid. }
      eapply lframe_implies;[exact WholeFrame|];intros b pos Outside Valid;split;assumption.
Qed.
