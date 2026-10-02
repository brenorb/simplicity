(** Actual wide right-extension calls: payload first, then repeated LSB fill.
    Reader/writer/free premises are derived by the initial-layout consumer. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_binary_wide_exec C.jet_readBit_layout C.jet_extend_wide_loop.
Require Import C.jet_extend_wide_exec C.jet_right_extend_wide_loop C.jet_right_extend_wide_spec.
Require Import C.jet_extend_bit_wide_exec C.jet_write_wide_sequence C.jet_wide C.jet_pad_bit_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition right_extend_wide_prepared le r := PTree.set _lsb
  (Vint (bit_int (right_extend_wide_lsb r)))
  (PTree.set _input (Vlong r) (PTree.set _t'1 (Vlong r) le)).
Lemma right_extend_wide_fill_from_sequence s bf base bit n m mf :
  write_wide_sequence_run (extend_wide_input s) bf base (repeat (extend_bit_long (extend_wide_input s) bit) n) m mf ->
  right_extend_wide_fill_run s bf base bit n m mf.
Proof.
  revert m. induction n as [|n IH]; intros m H; [exact H|].
  destruct H as [mi [HW HR]]. exists mi. split; [exact HW|apply IH; exact HR].
Qed.
Lemma right_extend_wide_body_shape s : (right_extend_wide_function s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read (extend_wide_input s) _t'1) (Sset _input (Etempvar _t'1 tulong)))
      (Ssequence (Sset _lsb right_extend_wide_lsb_expr)
        (Ssequence (frame_writer_call (wide_writer_id (extend_wide_input s)) tulong tvoid (Etempvar _input tulong))
          (Ssequence (Ssequence (Sset _i (Econst_int Int.zero tint)) (right_extend_wide_loop s))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Theorem eval_right_extend_wide_composes env s m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader (extend_wide_input s))) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  write_wide_sequence_run (extend_wide_input s) bd dbase (right_extend_wide_output_args s r) mr me ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (right_extend_wide_function s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC HR HW HF.
  change (exists mi,
    Clight2.eval_funcall ge0 mr (Internal (wide_writer (extend_wide_input s)))
      [Vptr bd (Ptrofs.repr dbase); Vlong r] E0 mi Vundef /\
    write_wide_sequence_run (extend_wide_input s) bd dbase
      (repeat (extend_bit_long (extend_wide_input s) (right_extend_wide_lsb r))
        (Z.to_nat (extend_wide_count s))) mi me) in HW.
  destruct HW as [mi [HWriteFirst HFill]].
  set (le := le_arith8_layout env (right_extend_wide_function s)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (inputle := PTree.set _input (Vlong r) (PTree.set _t'1 (Vlong r) le)).
  set (prepared := right_extend_wide_prepared le r).
  set (loopstart := PTree.set _i (Vint Int.zero) prepared).
  destruct (exec_right_extend_wide_loop s bl loopstart mi me bd dbase
    (right_extend_wide_lsb r) 0 (Z.to_nat (extend_wide_count s))
    ltac:(lia) ltac:(destruct s; reflexivity)
    ltac:(unfold loopstart; apply PTree.gss)
    ltac:(unfold loopstart, prepared, right_extend_wide_prepared;
      rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold loopstart, prepared, right_extend_wide_prepared, le, le_arith8_layout;
      repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity)
    (right_extend_wide_fill_from_sequence _ _ _ _ _ _ _ HFill)) as [lef [HLoop HTemp]].
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := lef)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s.
    all: change (list_disjoint [_dst; _src; _env] [_input; _lsb; _i; _t'2; _t'1]).
    all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite right_extend_wide_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := inputle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read; exact HR.
        -- apply exec_set. apply eval_Etempvar; apply PTree.gss.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := prepared).
        -- apply exec_set. apply eval_right_extend_wide_lsb; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := prepared).
           ++ eapply call_frame_writer_cast with (f := wide_writer (extend_wide_input s))
                (vraw := Vlong r) (v := Vlong r) (vret := Vundef).
              ** destruct s; reflexivity.
              ** unfold prepared, right_extend_wide_prepared, le, le_arith8_layout.
                 repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
              ** destruct s; reflexivity.
              ** apply wide_writer_symbol.
              ** apply wide_writer_funct.
              ** apply eval_Etempvar. unfold prepared, right_extend_wide_prepared.
                 rewrite PTree.gso by discriminate; apply PTree.gss.
              ** reflexivity.
              ** exact HWriteFirst.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := loopstart).
                 --- apply exec_set; constructor.
                 --- exact HLoop.
              ** apply exec_Sreturn_some; constructor.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
