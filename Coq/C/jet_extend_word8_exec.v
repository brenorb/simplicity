(** Actual read/cast/MSB preparation and complete byte-extension call boundary.
    Intermediate reader/writer-run/free contracts are internal obligations. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_binary8_exec C.jet_readBit_layout C.jet_extend_word8_loop.
Require Import C.jet_extend_bit8_exec C.jet_write8_sequence.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition extend_word8_payload r := Int.zero_ext 8 r.
Definition extend_word8_msb r := negb (Int.eq (Int.shr r (Int.repr 7)) Int.zero).
Definition extend_word8_msb_expr := Ecast
  (Ebinop Oshr (Etempvar _input tuchar)
    (Ebinop Osub (Econst_int (Int.repr 8) tint) (Econst_int Int.one tint) tint) tint) tbool.
Definition extend_word8_prepared le r := PTree.set _msb
  (Vint (bit_int (extend_word8_msb (extend_word8_payload r))))
  (PTree.set _input (Vint (extend_word8_payload r)) (PTree.set _t'1 (Vint r) le)).

Lemma eval_extend_word8_msb e le m r :
  le!_input = Some (Vint r) ->
  eval_expr ge0 e le m extend_word8_msb_expr (Vint (bit_int (extend_word8_msb r))).
Proof.
  intros HR. eapply eval_Ecast with (v1 := Vint (Int.shr r (Int.repr 7))).
  - eapply eval_Ebinop with (v1 := Vint r) (v2 := Vint (Int.repr 7)).
    + apply eval_Etempvar; exact HR.
    + eapply eval_Ebinop; [constructor|constructor|reflexivity].
    + reflexivity.
  - change (Some (Vint (if Int.eq (Int.shr r (Int.repr 7)) Int.zero then Int.zero else Int.one)) =
      Some (Vint (bit_int (extend_word8_msb r)))).
    unfold extend_word8_msb, bit_int. destruct (Int.eq (Int.shr r (Int.repr 7)) Int.zero); reflexivity.
Qed.

Lemma exec_extend_word8_prepare bl le m mr r :
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _input (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Sset _msb extend_word8_msb_expr))
    E0 (extend_word8_prepared le r) mr Out_normal.
Proof.
  intros HR. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
    (le1 := PTree.set _input (Vint (extend_word8_payload r)) (PTree.set _t'1 (Vint r) le)).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
    + apply call_binary8_read; exact HR.
    + apply exec_set. eapply eval_Ecast.
      * apply eval_Etempvar; apply PTree.gss.
      * reflexivity.
  - apply exec_set. apply eval_extend_word8_msb; apply PTree.gss.
Qed.

Lemma write8_sequence_run_app bf base xs ys m mf :
  write8_sequence_run bf base (xs ++ ys) m mf <->
  exists mi, write8_sequence_run bf base xs m mi /\ write8_sequence_run bf base ys mi mf.
Proof.
  revert m. induction xs as [|x xs IH]; intros m; cbn [app write8_sequence_run].
  - split; [intros H; exists m; auto|intros [mi [-> H]]; exact H].
  - split.
    + intros [mx [HX HR]]. apply IH in HR. destruct HR as [mi [HT HY]].
      exists mi. split; [exists mx; auto|exact HY].
    + intros [mi [[mx [HX HT]] HY]]. exists mx. split; [exact HX|]. apply IH. exists mi; auto.
Qed.
Lemma extend_word8_fill_from_sequence bf base bit n m mf :
  write8_sequence_run bf base (repeat (extend_bit8_arg bit) n) m mf ->
  extend_word8_fill_run bf base bit n m mf.
Proof.
  revert m. induction n as [|n IH]; intros m H; [exact H|].
  destruct H as [mi [HW HR]]. exists mi. split; [exact HW|apply IH; exact HR].
Qed.
Definition extend_word8_output_args s r :=
  repeat (extend_bit8_arg (extend_word8_msb (extend_word8_payload r)))
    (Z.to_nat (extend_word8_count s)) ++ [extend_word8_payload r].
Lemma extend_word8_body_shape s : (extend_word8_function s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _input (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence (Sset _msb extend_word8_msb_expr)
        (Ssequence (Ssequence (Sset _i (Econst_int Int.zero tint)) (extend_word8_loop s))
          (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _input tuchar))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Theorem eval_extend_word8_composes env s m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  write8_sequence_run bd dbase (extend_word8_output_args s r) mr me ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (extend_word8_function s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC HR HW HF.
  unfold extend_word8_output_args in HW. apply write8_sequence_run_app in HW.
  destruct HW as [mi [HFill HLast]].
  cbn [write8_sequence_run] in HLast. destruct HLast as [mz [HWriteLast Heq]]. subst mz.
  set (le := le_arith8_layout env (extend_word8_function s)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (inputle := PTree.set _input (Vint (extend_word8_payload r)) (PTree.set _t'1 (Vint r) le)).
  set (prepared := extend_word8_prepared le r).
  set (loopstart := PTree.set _i (Vint Int.zero) prepared).
  destruct (exec_extend_word8_loop s bl loopstart mr mi bd dbase
    (extend_word8_msb (extend_word8_payload r)) 0 (Z.to_nat (extend_word8_count s))
    ltac:(lia) ltac:(destruct s; reflexivity)
    ltac:(unfold loopstart; apply PTree.gss)
    ltac:(unfold loopstart, prepared, extend_word8_prepared; rewrite PTree.gso by discriminate;
      apply PTree.gss)
    ltac:(unfold loopstart, prepared, extend_word8_prepared, le, le_arith8_layout;
      repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity)
    (extend_word8_fill_from_sequence _ _ _ _ _ _ HFill)) as [lef [HLoop HTemp]].
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := lef)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s.
    all: change (list_disjoint [_dst; _src; _env] [_input; _msb; _i; _t'2; _t'1]).
    all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite extend_word8_body_shape.
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
        -- apply exec_set. apply eval_extend_word8_msb; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := lef).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := loopstart).
              ** apply exec_set; constructor.
              ** exact HLoop.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef).
              ** eapply call_frame_writer_cast with (f := f_simplicity_write8)
                   (vraw := Vint (extend_word8_payload r)) (v := Vint (extend_word8_payload r)) (vret := Vundef).
                 --- reflexivity.
                 --- rewrite HTemp by discriminate.
                     unfold loopstart, prepared, extend_word8_prepared, le, le_arith8_layout.
                     repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
                 --- reflexivity.
                 --- apply symbol_write8.
                 --- apply funct_write8.
                 --- apply eval_Etempvar. rewrite HTemp by discriminate.
                     unfold loopstart, prepared, extend_word8_prepared.
                     repeat rewrite PTree.gso by discriminate; apply PTree.gss.
                 --- change (Some (Vint (Int.zero_ext 8 (extend_word8_payload r))) =
                       Some (Vint (extend_word8_payload r))).
                     unfold extend_word8_payload; rewrite Int.zero_ext_idem by lia; reflexivity.
                 --- exact HWriteLast.
              ** apply exec_Sreturn_some; constructor.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
