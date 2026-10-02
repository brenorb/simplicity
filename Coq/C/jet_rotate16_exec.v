(** Shared actual left/right rotate_16 composition, retaining every C count
    expression. Scalar helper execution is reused from the wider consumers. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_binary8_exec C.jet_binary_wide_exec C.jet_wide C.jet_read4_call.
Require Import C.jet_rotate_wide_helper C.jet_rotate_count_exec.
Require Import C.jet_left_rotate_wide_exec C.jet_right_rotate_wide_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rotate16_function (right : bool) :=
  if right then f_simplicity_right_rotate_16 else f_simplicity_left_rotate_16.
Definition rotate16_scalar_value (right : bool) r a :=
  if right then wide_rotate_result W16 r (wide_rotate_reverse_amount W16 a)
  else wide_rotate_result W16 r a.
Definition rotate16_payload right r a := rotate16_scalar_value right r (wide_rotate_amount W16 a).
Definition rotate16_scalar_call (right : bool) :=
  if right then right_rotate_scalar_call W16 else rotate_scalar_call W16.
Lemma exec_rotate16_scalar_call right bl le m r a :
  0 <= Int.unsigned a < wide_bits W16 ->
  le!_input = Some (Vlong r) -> le!_amt = Some (Vint a) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (rotate16_scalar_call right)
    E0 (PTree.set _t'3 (Vlong (rotate16_scalar_value right r a)) le) m Out_normal.
Proof. destruct right; [apply exec_right_rotate_scalar_call|apply exec_rotate_scalar_call]. Qed.

Lemma rotate16_body right : (rotate16_function right).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (nibble_read _t'1) (Sset _amt
        (wide_rotate_amount_expr W16 (Etempvar _t'1 tuchar))))
      (Ssequence
        (Ssequence (wide_binary_read W16 _t'2) (Sset _input (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (rotate16_scalar_call right)
            (frame_writer_call (wide_writer_id W16) tulong tvoid (Etempvar _t'3 tulong)))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct right; reflexivity. Qed.

Theorem eval_rotate16_composes env right m ma mc mr mr2 me mf bl bd dbase bs sbase bytes a r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read4) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  0 <= Int.unsigned a < 256 ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader W16))
    [Vptr bl Ptrofs.zero] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer W16))
    [Vptr bd (Ptrofs.repr dbase); Vlong (rotate16_payload right r a)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (rotate16_function right))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread4 Hamount Hread HW HF.
  set (le := le_arith8_layout env (rotate16_function right)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (countle := PTree.set _amt (Vint (wide_rotate_amount W16 a))
    (PTree.set _t'1 (Vint a) le)).
  set (inputle := PTree.set _input (Vlong r) (PTree.set _t'2 (Vlong r) countle)).
  set (outputle := PTree.set _t'3 (Vlong (rotate16_payload right r a)) inputle).
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := outputle)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct right; reflexivity|destruct right; reflexivity| |exact HA].
    destruct right.
    all: change (list_disjoint [_dst; _src; _env] [_amt; _input; _t'3; _t'2; _t'1]).
    all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite rotate16_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := countle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_nibble_read; exact Hread4.
        -- apply exec_set. apply eval_wide_rotate_amount;
             [left; reflexivity|apply eval_Etempvar; apply PTree.gss|exact Hamount].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := inputle).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
           ++ apply call_wide_binary_read; exact Hread.
           ++ apply exec_set. apply eval_Etempvar; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := outputle).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := outputle).
              ** apply exec_rotate16_scalar_call.
                 --- apply wide_rotate_amount_bounds.
                 --- unfold inputle; apply PTree.gss.
                 --- unfold inputle, countle. repeat rewrite PTree.gso by discriminate; apply PTree.gss.
              ** eapply call_frame_writer_cast with (f := wide_writer W16)
                   (vraw := Vlong (rotate16_payload right r a)) (v := Vlong (rotate16_payload right r a))
                   (vret := Vundef).
                 --- destruct right; reflexivity.
                 --- unfold outputle, inputle, countle, le, le_arith8_layout.
                     repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
                 --- destruct right; reflexivity.
                 --- apply wide_writer_symbol.
                 --- apply wide_writer_funct.
                 --- apply eval_Etempvar. unfold outputle; apply PTree.gss.
                 --- reflexivity.
                 --- exact HW.
           ++ apply exec_Sreturn_some; constructor.
  - destruct right; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.

