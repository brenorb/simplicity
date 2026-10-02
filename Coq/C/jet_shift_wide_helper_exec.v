(** Complete LP64 wide shift helpers through internal reader/writer contracts.
    Both fill values and all count branches are executed. Final consumers must
    derive these call premises from initial frames; this is not jet coverage. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_readBit_layout.
Require Import C.jet_arith8_layout_exec C.jet_wide C.jet_rotate8_exec.
Require Import C.jet_shift8_helper_exec C.jet_shift_wide_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma exec_shift_wide_payload_reader s le m mf bs sofs r :
  le!_src = Some (Vptr bs sofs) ->
  Clight2.eval_funcall ge0 m (Internal (wide_reader s))
    [Vptr bs sofs] E0 mf (Vlong r) ->
  Clight2.exec_stmt ge0 empty_env le m (shift_wide_payload_reader s)
    E0 (PTree.set _t'2 (Vlong r) le) mf Out_normal.
Proof.
  intros HS HC. eapply exec_Scall with
    (vf := Vptr (jet_symbol_block (wide_reader_id s)) Ptrofs.zero)
    (vargs := [Vptr bs sofs]) (f := Internal (wide_reader s)) (vres := Vlong r).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply wide_reader_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HS.
    + reflexivity.
    + apply eval_Enil.
  - apply wide_reader_funct.
  - destruct s; reflexivity.
  - exact HC.
Qed.

Definition shift_wide_maybe_fill s (fill : bool) r := if fill then shift_wide_fill_result s r else r.
Definition shift_wide_fill_env s (fill : bool) r le :=
  if fill then PTree.set _output (Vlong (shift_wide_fill_result s r)) le else le.
Definition shift_wide_count_result s right r a :=
  if zlt (Int.unsigned a) (wide_bits s) then shift_wide_scalar_result right r a else Int64.zero.
Definition shift_wide_payload s right fill r a := shift_wide_maybe_fill s fill
  (shift_wide_count_result s right (shift_wide_maybe_fill s fill r) (Int.zero_ext 8 a)).

Lemma shift_wide_fill_env_output s fill r le : le!_output = Some (Vlong r) ->
  (shift_wide_fill_env s fill r le)!_output = Some (Vlong (shift_wide_maybe_fill s fill r)).
Proof. intros HR. destruct fill; [apply PTree.gss|exact HR]. Qed.
Lemma shift_wide_fill_env_other s fill r le id : id <> _output ->
  (shift_wide_fill_env s fill r le)!id = le!id.
Proof. intros HN. destruct fill; [apply PTree.gso; congruence|reflexivity]. Qed.

Lemma exec_shift_wide_fill_step s fill e le m r :
  le!_with = Some (Vint (bit_int fill)) -> le!_output = Some (Vlong r) ->
  Clight2.exec_stmt ge0 e le m (shift_wide_fill_step s)
    E0 (shift_wide_fill_env s fill r le) m Out_normal.
Proof.
  intros HF HR. unfold shift_wide_fill_step.
  eapply exec_Sifthenelse with (v1 := Vint (bit_int fill)) (b := fill).
  - apply eval_Etempvar; exact HF.
  - destruct fill; reflexivity.
  - destruct fill.
    + apply exec_set. apply eval_shift_wide_fill_expr; exact HR.
    + apply exec_Sskip.
Qed.

Definition le_shift_wide_helper s right fill bd dofs bs sofs :=
  PTree.set _src (Vptr bs sofs) (PTree.set _dst (Vptr bd dofs)
    (PTree.set _with (Vint (bit_int fill)) (create_undef_temps (shift_wide_helper s right).(fn_temps)))).

Lemma entry_shift_wide_helper s right fill m bd dofs bs sofs :
  function_entry2 ge0 (shift_wide_helper s right) [Vint (bit_int fill); Vptr bd dofs; Vptr bs sofs]
    m empty_env (le_shift_wide_helper s right fill bd dofs bs sofs) m.
Proof.
  constructor.
  - destruct s, right; constructor.
  - destruct s, right; change (list_norepet [_with; _dst; _src]);
      repeat constructor; cbn; intuition discriminate.
  - destruct s, right; change (list_disjoint [_with; _dst; _src] [_amt; _output; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; vm_compute in *; congruence.
  - destruct s, right; constructor.
  - destruct s, right; reflexivity.
Qed.

Theorem eval_shift_wide_helper_composes s right fill m mr mr2 mf bd dofs bs sofs a r :
  Clight2.eval_funcall ge0 m (Internal (shift8_reader_function (match s with W16 => true | _ => false end))) [Vptr bs sofs] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bs sofs] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_writer s))
    [Vptr bd dofs; Vlong (shift_wide_payload s right fill r a)] E0 mf Vundef ->
  Clight2.eval_funcall ge0 m (Internal (shift_wide_helper s right))
    [Vint (bit_int fill); Vptr bd dofs; Vptr bs sofs] E0 mf Vundef.
Proof.
  intros Hread4 Hread8 Hwrite. pose proof (wide_bits_bounds s) as Hwidth.
  set (le := le_shift_wide_helper s right fill bd dofs bs sofs).
  set (countle := PTree.set _amt (Vint (Int.zero_ext 8 a)) (PTree.set _t'1 (Vint a) le)).
  set (inputle := PTree.set _output (Vlong r) (PTree.set _t'2 (Vlong r) countle)).
  set (fillle := shift_wide_fill_env s fill r inputle).
  set (shiftle := PTree.set _output
    (Vlong (shift_wide_count_result s right (shift_wide_maybe_fill s fill r) (Int.zero_ext 8 a))) fillle).
  set (outputle := shift_wide_fill_env s fill
    (shift_wide_count_result s right (shift_wide_maybe_fill s fill r) (Int.zero_ext 8 a)) shiftle).
  assert (HCountRange : 0 <= Int.unsigned (Int.zero_ext 8 a) < 256) by apply zero_ext8_unsigned_range.
  assert (HFillWith : fillle!_with = Some (Vint (bit_int fill))).
  { unfold fillle. rewrite shift_wide_fill_env_other by discriminate.
    unfold inputle, countle, le, le_shift_wide_helper; repeat rewrite PTree.gso by discriminate; apply PTree.gss. }
  assert (HFillAmt : fillle!_amt = Some (Vint (Int.zero_ext 8 a))).
  { unfold fillle. rewrite shift_wide_fill_env_other by discriminate.
    unfold inputle, countle; repeat rewrite PTree.gso by discriminate; apply PTree.gss. }
  assert (HFillOut : fillle!_output = Some (Vlong (shift_wide_maybe_fill s fill r))).
  { unfold fillle. apply shift_wide_fill_env_output. unfold inputle; apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := outputle)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply entry_shift_wide_helper.
  - rewrite shift_wide_helper_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := countle).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * unfold shift_wide_count_reader. eapply exec_shift8_reader with (bs := bs) (sofs := sofs);
          [unfold le, le_shift_wide_helper; apply PTree.gss|exact Hread4].
      * apply exec_set. eapply eval_Ecast with (v1 := Vint a).
        -- apply eval_Etempvar; apply PTree.gss.
        -- reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := inputle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        -- eapply exec_shift_wide_payload_reader with (bs := bs) (sofs := sofs).
           ++ unfold countle, le, le_shift_wide_helper; repeat rewrite PTree.gso by discriminate; apply PTree.gss.
           ++ exact Hread8.
        -- apply exec_set. apply eval_Etempvar; apply PTree.gss.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := fillle).
        -- apply exec_shift_wide_fill_step.
           ++ unfold inputle, countle, le, le_shift_wide_helper; repeat rewrite PTree.gso by discriminate; apply PTree.gss.
           ++ unfold inputle; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := shiftle).
           ++ eapply exec_Sifthenelse with
                (v1 := Vint (if zlt (Int.unsigned (Int.zero_ext 8 a)) (wide_bits s) then Int.one else Int.zero))
                (b := if zlt (Int.unsigned (Int.zero_ext 8 a)) (wide_bits s) then true else false).
              ** apply eval_shift_wide_count_expr; assumption.
              ** destruct (zlt (Int.unsigned (Int.zero_ext 8 a)) (wide_bits s)); reflexivity.
              ** unfold shiftle, shift_wide_count_result.
                 destruct (zlt (Int.unsigned (Int.zero_ext 8 a)) (wide_bits s)) as [HL|HG].
                 --- apply exec_set. apply eval_shift_wide_scalar_expr; [lia|exact HFillOut|exact HFillAmt].
                 --- apply exec_set. eapply eval_Ecast with (v1 := Vint Int.zero); [constructor|reflexivity].
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := outputle).
              ** apply exec_shift_wide_fill_step.
                 --- unfold shiftle; rewrite PTree.gso by discriminate; exact HFillWith.
                 --- unfold shiftle; apply PTree.gss.
              ** eapply call_frame_writer_cast with (f := (wide_writer s))
                   (vraw := Vlong (shift_wide_payload s right fill r a))
                   (v := Vlong (shift_wide_payload s right fill r a)) (vret := Vundef).
                 --- destruct s; reflexivity.
                 --- unfold outputle, shiftle, fillle, inputle, countle, le, le_shift_wide_helper.
                     repeat first [rewrite shift_wide_fill_env_other by discriminate
                       |rewrite PTree.gso by discriminate].
                     rewrite PTree.gss; reflexivity.
                 --- destruct s; reflexivity.
                 --- apply wide_writer_symbol.
                 --- apply wide_writer_funct.
                 --- apply eval_Etempvar. unfold outputle, shift_wide_payload.
                     apply shift_wide_fill_env_output. unfold shiftle; apply PTree.gss.
                 --- reflexivity.
                 --- exact Hwrite.
  - destruct s, right; reflexivity.
  - reflexivity.
Qed.
