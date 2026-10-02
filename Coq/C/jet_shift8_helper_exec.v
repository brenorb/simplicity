(** Complete byte shift helper execution through internal reader/writer
    contracts. Both fill values and the out-of-range count branch are covered.
    Initial-frame consumers must discharge these internal call premises. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_readBit_layout.
Require Import C.jet_arith8_layout_exec.
Require Import C.jet_rotate8_exec C.jet_rotate_count_exec C.jet_shift8_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition shift8_reader_function (nibble : bool) :=
  if nibble then f_simplicity_read4 else f_simplicity_read8.
Definition shift8_reader_id (nibble : bool) :=
  if nibble then _simplicity_read4 else _simplicity_read8.

Lemma shift8_reader_symbol nibble :
  Genv.find_symbol (Clight.genv_genv ge0) (shift8_reader_id nibble) =
    Some (jet_symbol_block (shift8_reader_id nibble)).
Proof. destruct nibble; vm_compute; reflexivity. Qed.
Lemma shift8_reader_funct nibble :
  Genv.find_funct (Clight.genv_genv ge0)
    (Vptr (jet_symbol_block (shift8_reader_id nibble)) Ptrofs.zero) =
    Some (Internal (shift8_reader_function nibble)).
Proof. destruct nibble; vm_compute; reflexivity. Qed.

Lemma exec_shift8_reader nibble result le m mf bs sofs r :
  le!_src = Some (Vptr bs sofs) ->
  Clight2.eval_funcall ge0 m (Internal (shift8_reader_function nibble))
    [Vptr bs sofs] E0 mf (Vint r) ->
  Clight2.exec_stmt ge0 empty_env le m (shift8_reader nibble result)
    E0 (PTree.set result (Vint r) le) mf Out_normal.
Proof.
  intros HS HC. eapply exec_Scall with
    (vf := Vptr (jet_symbol_block (shift8_reader_id nibble)) Ptrofs.zero)
    (vargs := [Vptr bs sofs]) (f := Internal (shift8_reader_function nibble)) (vres := Vint r).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply shift8_reader_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HS.
    + reflexivity.
    + apply eval_Enil.
  - apply shift8_reader_funct.
  - destruct nibble; reflexivity.
  - exact HC.
Qed.

Definition shift8_maybe_fill (fill : bool) r := if fill then shift8_fill_result r else r.
Definition shift8_fill_env (fill : bool) r le :=
  if fill then PTree.set _output (Vint (shift8_fill_result r)) le else le.
Definition shift8_count_result right r a :=
  if zlt (Int.unsigned a) 8 then shift8_scalar_result right r a else Int.zero.
Definition shift8_payload right fill r a := shift8_maybe_fill fill
  (shift8_count_result right (shift8_maybe_fill fill (Int.zero_ext 8 r)) (Int.zero_ext 8 a)).

Lemma shift8_fill_env_output fill r le : le!_output = Some (Vint r) ->
  (shift8_fill_env fill r le)!_output = Some (Vint (shift8_maybe_fill fill r)).
Proof. intros HR. destruct fill; [apply PTree.gss|exact HR]. Qed.
Lemma shift8_fill_env_other fill r le id : id <> _output ->
  (shift8_fill_env fill r le)!id = le!id.
Proof. intros HN. destruct fill; [apply PTree.gso; congruence|reflexivity]. Qed.

Lemma exec_shift8_fill_step fill e le m r :
  le!_with = Some (Vint (bit_int fill)) -> le!_output = Some (Vint r) ->
  Clight2.exec_stmt ge0 e le m shift8_fill_step
    E0 (shift8_fill_env fill r le) m Out_normal.
Proof.
  intros HF HR. unfold shift8_fill_step.
  eapply exec_Sifthenelse with (v1 := Vint (bit_int fill)) (b := fill).
  - apply eval_Etempvar; exact HF.
  - destruct fill; reflexivity.
  - destruct fill.
    + apply exec_set. apply eval_shift8_fill_expr; exact HR.
    + apply exec_Sskip.
Qed.

Definition le_shift8_helper right fill bd dofs bs sofs :=
  PTree.set _src (Vptr bs sofs) (PTree.set _dst (Vptr bd dofs)
    (PTree.set _with (Vint (bit_int fill)) (create_undef_temps (shift8_helper right).(fn_temps)))).

Lemma entry_shift8_helper right fill m bd dofs bs sofs :
  function_entry2 ge0 (shift8_helper right) [Vint (bit_int fill); Vptr bd dofs; Vptr bs sofs]
    m empty_env (le_shift8_helper right fill bd dofs bs sofs) m.
Proof.
  constructor.
  - destruct right; constructor.
  - destruct right; change (list_norepet [_with; _dst; _src]);
      repeat constructor; cbn; intuition discriminate.
  - destruct right; change (list_disjoint [_with; _dst; _src] [_amt; _output; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; vm_compute in *; congruence.
  - destruct right; constructor.
  - destruct right; reflexivity.
Qed.

Theorem eval_shift8_helper_composes right fill m mr mr2 mf bd dofs bs sofs a r :
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read4) [Vptr bs sofs] E0 mr (Vint a) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bs sofs] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd dofs; Vint (Int.zero_ext 8 (shift8_payload right fill r a))] E0 mf Vundef ->
  Clight2.eval_funcall ge0 m (Internal (shift8_helper right))
    [Vint (bit_int fill); Vptr bd dofs; Vptr bs sofs] E0 mf Vundef.
Proof.
  intros Hread4 Hread8 Hwrite.
  set (le := le_shift8_helper right fill bd dofs bs sofs).
  set (countle := PTree.set _amt (Vint (Int.zero_ext 8 a)) (PTree.set _t'1 (Vint a) le)).
  set (inputle := PTree.set _output (Vint (Int.zero_ext 8 r)) (PTree.set _t'2 (Vint r) countle)).
  set (fillle := shift8_fill_env fill (Int.zero_ext 8 r) inputle).
  set (shiftle := PTree.set _output
    (Vint (shift8_count_result right (shift8_maybe_fill fill (Int.zero_ext 8 r)) (Int.zero_ext 8 a))) fillle).
  set (outputle := shift8_fill_env fill
    (shift8_count_result right (shift8_maybe_fill fill (Int.zero_ext 8 r)) (Int.zero_ext 8 a)) shiftle).
  assert (HCountRange : 0 <= Int.unsigned (Int.zero_ext 8 a) < 256) by apply zero_ext8_unsigned_range.
  assert (HFillWith : fillle!_with = Some (Vint (bit_int fill))).
  { unfold fillle. rewrite shift8_fill_env_other by discriminate.
    unfold inputle, countle, le, le_shift8_helper; repeat rewrite PTree.gso by discriminate; apply PTree.gss. }
  assert (HFillAmt : fillle!_amt = Some (Vint (Int.zero_ext 8 a))).
  { unfold fillle. rewrite shift8_fill_env_other by discriminate.
    unfold inputle, countle; repeat rewrite PTree.gso by discriminate; apply PTree.gss. }
  assert (HFillOut : fillle!_output = Some (Vint (shift8_maybe_fill fill (Int.zero_ext 8 r)))).
  { unfold fillle. apply shift8_fill_env_output. unfold inputle; apply PTree.gss. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := outputle)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply entry_shift8_helper.
  - rewrite shift8_helper_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := countle).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_shift8_reader with (bs := bs) (sofs := sofs);
          [unfold le, le_shift8_helper; apply PTree.gss|exact Hread4].
      * apply exec_set. eapply eval_Ecast with (v1 := Vint a).
        -- apply eval_Etempvar; apply PTree.gss.
        -- reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := inputle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        -- eapply exec_shift8_reader with (bs := bs) (sofs := sofs).
           ++ unfold countle, le, le_shift8_helper; repeat rewrite PTree.gso by discriminate; apply PTree.gss.
           ++ exact Hread8.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint r).
           ++ apply eval_Etempvar; apply PTree.gss.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := fillle).
        -- apply exec_shift8_fill_step.
           ++ unfold inputle, countle, le, le_shift8_helper; repeat rewrite PTree.gso by discriminate; apply PTree.gss.
           ++ unfold inputle; apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := shiftle).
           ++ eapply exec_Sifthenelse with
                (v1 := Vint (if zlt (Int.unsigned (Int.zero_ext 8 a)) 8 then Int.one else Int.zero))
                (b := if zlt (Int.unsigned (Int.zero_ext 8 a)) 8 then true else false).
              ** apply eval_shift8_count_expr; assumption.
              ** destruct (zlt (Int.unsigned (Int.zero_ext 8 a)) 8); reflexivity.
              ** unfold shiftle, shift8_count_result.
                 destruct (zlt (Int.unsigned (Int.zero_ext 8 a)) 8) as [HL|HG].
                 --- apply exec_set. apply eval_shift8_scalar_expr; [lia|exact HFillOut|exact HFillAmt].
                 --- apply exec_set. eapply eval_Ecast with (v1 := Vint Int.zero); [constructor|reflexivity].
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := outputle).
              ** apply exec_shift8_fill_step.
                 --- unfold shiftle; rewrite PTree.gso by discriminate; exact HFillWith.
                 --- unfold shiftle; apply PTree.gss.
              ** eapply call_frame_writer_cast with (f := f_simplicity_write8)
                   (vraw := Vint (shift8_payload right fill r a))
                   (v := Vint (Int.zero_ext 8 (shift8_payload right fill r a))) (vret := Vundef).
                 --- reflexivity.
                 --- unfold outputle, shiftle, fillle, inputle, countle, le, le_shift8_helper.
                     repeat first [rewrite shift8_fill_env_other by discriminate
                       |rewrite PTree.gso by discriminate].
                     rewrite PTree.gss; reflexivity.
                 --- reflexivity.
                 --- apply symbol_write8.
                 --- apply funct_write8.
                 --- apply eval_Etempvar. unfold outputle, shift8_payload.
                     apply shift8_fill_env_output. unfold shiftle; apply PTree.gss.
                 --- reflexivity.
                 --- exact Hwrite.
  - destruct right; reflexivity.
  - reflexivity.
Qed.
