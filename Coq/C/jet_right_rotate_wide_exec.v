(** Actual right_rotate_32/64 call composition. The reversed shift count is
    evaluated from the generated subtraction/modulo/cast argument. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_binary8_exec C.jet_binary_wide_exec C.jet_wide.
Require Import C.jet_rotate_wide_helper C.jet_rotate_count_exec C.jet_left_rotate_wide_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition right_rotate_byte_function s := match s with
  R32 => f_simplicity_right_rotate_32 | R64 => f_simplicity_right_rotate_64 end.
Definition right_rotate_byte_payload s r a :=
  wide_rotate_result (byte_rotate_width s) r
    (wide_rotate_reverse_amount (byte_rotate_width s) (wide_rotate_amount (byte_rotate_width s) a)).
Definition right_rotate_scalar_call s := Scall (Some _t'3)
  (Evar (wide_rotate_helper_id s) (Tfunction (Tcons tulong (Tcons tuchar Tnil)) tulong cc_default))
  [Etempvar _input tulong; wide_rotate_reverse_amount_expr s].

Lemma exec_right_rotate_scalar_call s bl le m r a :
  0 <= Int.unsigned a < wide_bits s ->
  le!_input = Some (Vlong r) -> le!_amt = Some (Vint a) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (right_rotate_scalar_call s)
    E0 (PTree.set _t'3 (Vlong (wide_rotate_result s r (wide_rotate_reverse_amount s a))) le) m Out_normal.
Proof.
  intros HA HI HM.
  eapply exec_Scall with (vf := Vptr (jet_symbol_block (wide_rotate_helper_id s)) Ptrofs.zero)
    (vargs := [Vlong r; Vint (wide_rotate_reverse_amount s a)]) (f := Internal (wide_rotate_helper s))
    (vres := Vlong (wide_rotate_result s r (wide_rotate_reverse_amount s a))).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [destruct s; reflexivity|apply wide_rotate_helper_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HI.
    + reflexivity.
    + eapply eval_Econs.
      * exact (@eval_wide_rotate_reverse_amount s (e_one8 bl) le m a HA HM).
      * change (Some (Vint (Int.zero_ext 8 (wide_rotate_reverse_amount s a))) =
          Some (Vint (wide_rotate_reverse_amount s a))).
        unfold wide_rotate_reverse_amount. rewrite wide_rotate_amount_cast_id; reflexivity.
      * apply eval_Enil.
  - apply wide_rotate_helper_funct.
  - destruct s; reflexivity.
  - apply eval_wide_rotate_helper. unfold wide_rotate_reverse_amount. apply wide_rotate_amount_bounds.
Qed.

Lemma right_rotate_byte_body s : (right_rotate_byte_function s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _amt
        (wide_rotate_amount_expr (byte_rotate_width s) (Etempvar _t'1 tuchar))))
      (Ssequence
        (Ssequence (wide_binary_read (byte_rotate_width s) _t'2) (Sset _input (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (right_rotate_scalar_call (byte_rotate_width s))
            (frame_writer_call (wide_writer_id (byte_rotate_width s)) tulong tvoid (Etempvar _t'3 tulong)))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct s; reflexivity. Qed.

Theorem eval_right_rotate_byte_composes env s m ma mc mr mr2 me mf bl bd dbase bs sbase bytes a r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  0 <= Int.unsigned a < 256 ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader (byte_rotate_width s)))
    [Vptr bl Ptrofs.zero] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer (byte_rotate_width s)))
    [Vptr bd (Ptrofs.repr dbase); Vlong (right_rotate_byte_payload s r a)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (right_rotate_byte_function s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread8 Hamount Hread HW HF.
  set (le := le_arith8_layout env (right_rotate_byte_function s)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (countle := PTree.set _amt (Vint (wide_rotate_amount (byte_rotate_width s) a))
    (PTree.set _t'1 (Vint a) le)).
  set (inputle := PTree.set _input (Vlong r) (PTree.set _t'2 (Vlong r) countle)).
  set (outputle := PTree.set _t'3 (Vlong (right_rotate_byte_payload s r a)) inputle).
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := outputle)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s.
    all: change (list_disjoint [_dst; _src; _env] [_amt; _input; _t'3; _t'2; _t'1]).
    all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite right_rotate_byte_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := countle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read; exact Hread8.
        -- apply exec_set. apply eval_wide_rotate_amount;
             [left; reflexivity|apply eval_Etempvar; apply PTree.gss|exact Hamount].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := inputle).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
           ++ apply call_wide_binary_read; exact Hread.
           ++ apply exec_set. apply eval_Etempvar; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := outputle).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := outputle).
              ** apply exec_right_rotate_scalar_call.
                 --- apply wide_rotate_amount_bounds.
                 --- unfold inputle; apply PTree.gss.
                 --- unfold inputle, countle. repeat rewrite PTree.gso by discriminate; apply PTree.gss.
              ** eapply call_frame_writer_cast with (f := wide_writer (byte_rotate_width s))
                   (vraw := Vlong (right_rotate_byte_payload s r a)) (v := Vlong (right_rotate_byte_payload s r a))
                   (vret := Vundef).
                 --- destruct s; reflexivity.
                 --- unfold outputle, inputle, countle, le, le_arith8_layout.
                     repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
                 --- destruct s; reflexivity.
                 --- apply wide_writer_symbol.
                 --- apply wide_writer_funct.
                 --- apply eval_Etempvar. unfold outputle; apply PTree.gss.
                 --- reflexivity.
                 --- exact HW.
           ++ apply exec_Sreturn_some; constructor.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
