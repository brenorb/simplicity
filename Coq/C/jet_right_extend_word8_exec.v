(** Actual right_extend_8_{16,32,64} call composition: payload before fill.
    Reader/writer-run/free premises remain internal until derived by layouts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_binary8_exec C.jet_readBit_layout C.jet_extend_word8_loop.
Require Import C.jet_extend_word8_exec C.jet_right_extend_word8_loop C.jet_right_extend_word_spec.
Require Import C.jet_extend_bit8_exec C.jet_write8_sequence.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition right_extend_word8_prepared le r := PTree.set _lsb
  (Vint (bit_int (right_extend_word8_lsb (extend_word8_payload r))))
  (PTree.set _input (Vint (extend_word8_payload r)) (PTree.set _t'1 (Vint r) le)).
Lemma right_extend_word8_fill_from_sequence bf base bit n m mf :
  write8_sequence_run bf base (repeat (extend_bit8_arg bit) n) m mf ->
  right_extend_word8_fill_run bf base bit n m mf.
Proof.
  revert m. induction n as [|n IH]; intros m H; [exact H|].
  destruct H as [mi [HW HR]]. exists mi. split; [exact HW|apply IH; exact HR].
Qed.
Lemma right_extend_word8_body_shape s : (right_extend_word8_function s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _input (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence (Sset _lsb right_extend_word8_lsb_expr)
        (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _input tuchar))
          (Ssequence (Ssequence (Sset _i (Econst_int Int.zero tint)) (right_extend_word8_loop s))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Theorem eval_right_extend_word8_composes env s m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  write8_sequence_run bd dbase (right_extend_word8_output_args s r) mr me ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (right_extend_word8_function s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC HR HW HF.
  change (exists mi,
    Clight2.eval_funcall ge0 mr (Internal f_simplicity_write8)
      [Vptr bd (Ptrofs.repr dbase); Vint (extend_word8_payload r)] E0 mi Vundef /\
    write8_sequence_run bd dbase
      (repeat (extend_bit8_arg (right_extend_word8_lsb (extend_word8_payload r)))
        (Z.to_nat (extend_word8_count s))) mi me) in HW.
  destruct HW as [mi [HWriteFirst HFill]].
  set (le := le_arith8_layout env (right_extend_word8_function s)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (inputle := PTree.set _input (Vint (extend_word8_payload r)) (PTree.set _t'1 (Vint r) le)).
  set (prepared := right_extend_word8_prepared le r).
  set (loopstart := PTree.set _i (Vint Int.zero) prepared).
  destruct (exec_right_extend_word8_loop s bl loopstart mi me bd dbase
    (right_extend_word8_lsb (extend_word8_payload r)) 0 (Z.to_nat (extend_word8_count s))
    ltac:(lia) ltac:(destruct s; reflexivity)
    ltac:(unfold loopstart; apply PTree.gss)
    ltac:(unfold loopstart, prepared, right_extend_word8_prepared;
      rewrite PTree.gso by discriminate; apply PTree.gss)
    ltac:(unfold loopstart, prepared, right_extend_word8_prepared, le, le_arith8_layout;
      repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity)
    (right_extend_word8_fill_from_sequence _ _ _ _ _ _ HFill)) as [lef [HLoop HTemp]].
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := lef)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s.
    all: change (list_disjoint [_dst; _src; _env] [_input; _lsb; _i; _t'2; _t'1]).
    all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite right_extend_word8_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := inputle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read; exact HR.
        -- apply exec_set. eapply eval_Ecast.
           ++ apply eval_Etempvar; apply PTree.gss.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := prepared).
        -- apply exec_set. apply eval_right_extend_word8_lsb; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := prepared).
           ++ eapply call_frame_writer_cast with (f := f_simplicity_write8)
                (vraw := Vint (extend_word8_payload r)) (v := Vint (extend_word8_payload r)) (vret := Vundef).
              ** reflexivity.
              ** unfold prepared, right_extend_word8_prepared, le, le_arith8_layout.
                 repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
              ** reflexivity.
              ** apply symbol_write8.
              ** apply funct_write8.
              ** apply eval_Etempvar. unfold prepared, right_extend_word8_prepared.
                 rewrite PTree.gso by discriminate; apply PTree.gss.
              ** change (Some (Vint (Int.zero_ext 8 (extend_word8_payload r))) =
                   Some (Vint (extend_word8_payload r))).
                 unfold extend_word8_payload; rewrite Int.zero_ext_idem by lia; reflexivity.
              ** exact HWriteFirst.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := loopstart).
                 --- apply exec_set; constructor.
                 --- exact HLoop.
              ** apply exec_Sreturn_some; constructor.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
