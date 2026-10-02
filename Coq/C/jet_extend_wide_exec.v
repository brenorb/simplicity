(** Actual unsigned-long read/MSB preparation and complete wide left-extension calls.
    Reader/writer/free premises remain internal until derived by initial layouts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_binary_wide_exec C.jet_readBit_layout C.jet_extend_wide_loop.
Require Import C.jet_extend_bit_wide_exec C.jet_write_wide_sequence C.jet_wide C.jet_pad_bit_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition extend_wide_msb s r :=
  negb (Int64.eq (Int64.shru r (Int64.repr (wide_bits (extend_wide_input s) - 1))) Int64.zero).
Definition extend_wide_msb_expr s := Ecast
  (Ebinop Oshr (Etempvar _input tulong)
    (Ebinop Osub (Econst_int (Int.repr (wide_bits (extend_wide_input s))) tint)
      (Econst_int Int.one tint) tint) tulong) tbool.
Definition extend_wide_prepared s le r := PTree.set _msb
  (Vint (bit_int (extend_wide_msb s r)))
  (PTree.set _input (Vlong r) (PTree.set _t'1 (Vlong r) le)).

Lemma eval_extend_wide_msb s e le m r :
  le!_input = Some (Vlong r) ->
  eval_expr ge0 e le m (extend_wide_msb_expr s) (Vint (bit_int (extend_wide_msb s r))).
Proof.
  intros HR. eapply eval_Ecast with
    (v1 := Vlong (Int64.shru r (Int64.repr (wide_bits (extend_wide_input s) - 1)))).
  - eapply eval_Ebinop with (v1 := Vlong r)
      (v2 := Vint (Int.repr (wide_bits (extend_wide_input s) - 1))).
    + apply eval_Etempvar; exact HR.
    + eapply eval_Ebinop; [constructor|constructor|destruct s; reflexivity].
    + destruct s; reflexivity.
  - change (Some (Vint (if Int64.eq
      (Int64.shru r (Int64.repr (wide_bits (extend_wide_input s) - 1))) Int64.zero
      then Int.zero else Int.one)) = Some (Vint (bit_int (extend_wide_msb s r)))).
    unfold extend_wide_msb, bit_int. destruct (Int64.eq
      (Int64.shru r (Int64.repr (wide_bits (extend_wide_input s) - 1))) Int64.zero); reflexivity.
Qed.

Lemma write_wide_sequence_run_app s bf base xs ys m mf :
  write_wide_sequence_run s bf base (xs ++ ys) m mf <->
  exists mi, write_wide_sequence_run s bf base xs m mi /\ write_wide_sequence_run s bf base ys mi mf.
Proof.
  revert m. induction xs as [|x xs IH]; intros m; cbn [app write_wide_sequence_run].
  - split; [intros H; exists m; auto|intros [mi [-> H]]; exact H].
  - split.
    + intros [mx [HX HR]]. apply IH in HR. destruct HR as [mi [HT HY]].
      exists mi. split; [exists mx; auto|exact HY].
    + intros [mi [[mx [HX HT]] HY]]. exists mx. split; [exact HX|]. apply IH. exists mi; auto.
Qed.
Lemma extend_wide_fill_from_sequence s bf base bit n m mf :
  write_wide_sequence_run (extend_wide_input s) bf base (repeat (extend_bit_long (extend_wide_input s) bit) n) m mf ->
  extend_wide_fill_run s bf base bit n m mf.
Proof.
  revert m. induction n as [|n IH]; intros m H; [exact H|].
  destruct H as [mi [HW HR]]. exists mi. split; [exact HW|apply IH; exact HR].
Qed.
Definition extend_wide_output_args s r :=
  repeat (extend_bit_long (extend_wide_input s) (extend_wide_msb s r))
    (Z.to_nat (extend_wide_count s)) ++ [r].
Lemma extend_wide_body_shape s : (extend_wide_function s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read (extend_wide_input s) _t'1) (Sset _input (Etempvar _t'1 tulong)))
      (Ssequence (Sset _msb (extend_wide_msb_expr s))
        (Ssequence (Ssequence (Sset _i (Econst_int Int.zero tint)) (extend_wide_loop s))
          (Ssequence (frame_writer_call (wide_writer_id (extend_wide_input s)) tulong tvoid (Etempvar _input tulong))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Theorem eval_extend_wide_composes env s m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader (extend_wide_input s))) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  write_wide_sequence_run (extend_wide_input s) bd dbase (extend_wide_output_args s r) mr me ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (extend_wide_function s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC HR HW HF.
  unfold extend_wide_output_args in HW. apply write_wide_sequence_run_app in HW.
  destruct HW as [mi [HFill HLast]].
  cbn [write_wide_sequence_run] in HLast. destruct HLast as [mz [HWriteLast Heq]]. subst mz.
  set (le := le_arith8_layout env (extend_wide_function s)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (inputle := PTree.set _input (Vlong r) (PTree.set _t'1 (Vlong r) le)).
  set (prepared := extend_wide_prepared s le r).
  set (loopstart := PTree.set _i (Vint Int.zero) prepared).
  destruct (exec_extend_wide_loop s bl loopstart mr mi bd dbase
    (extend_wide_msb s r) 0 (Z.to_nat (extend_wide_count s))
    ltac:(lia) ltac:(destruct s; reflexivity)
    ltac:(unfold loopstart; apply PTree.gss)
    ltac:(unfold loopstart, prepared, extend_wide_prepared; rewrite PTree.gso by discriminate;
      apply PTree.gss)
    ltac:(unfold loopstart, prepared, extend_wide_prepared, le, le_arith8_layout;
      repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity)
    (extend_wide_fill_from_sequence _ _ _ _ _ _ _ HFill)) as [lef [HLoop HTemp]].
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := lef)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s.
    all: change (list_disjoint [_dst; _src; _env] [_input; _msb; _i; _t'2; _t'1]).
    all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite extend_wide_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := inputle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read; exact HR.
        -- apply exec_set. apply eval_Etempvar; apply PTree.gss.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := prepared).
        -- apply exec_set. apply eval_extend_wide_msb; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mi) (le1 := lef).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := loopstart).
              ** apply exec_set; constructor.
              ** exact HLoop.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef).
              ** eapply call_frame_writer_cast with (f := wide_writer (extend_wide_input s))
                   (vraw := Vlong r) (v := Vlong r) (vret := Vundef).
                 --- destruct s; reflexivity.
                 --- rewrite HTemp by discriminate.
                     unfold loopstart, prepared, extend_wide_prepared, le, le_arith8_layout.
                     repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
                 --- destruct s; reflexivity.
                 --- apply wide_writer_symbol.
                 --- apply wide_writer_funct.
                 --- apply eval_Etempvar. rewrite HTemp by discriminate.
                     unfold loopstart, prepared, extend_wide_prepared.
                     repeat rewrite PTree.gso by discriminate; apply PTree.gss.
                 --- reflexivity.
                 --- exact HWriteLast.
              ** apply exec_Sreturn_some; constructor.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
