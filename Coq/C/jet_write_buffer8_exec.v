(** Actual mixed-buffer writer branches. These internal adapters retain the
    length comparison, bit call, payload/skip call and pointer/length updates.
    Total consumers must derive their intermediate execution premises. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_readBit_layout C.jet_write_buffer8_empty_exec C.jet_read_buffer8_exec.
Require Import C.jet_arith8_layout_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma buffer8_write_array_symbol : Genv.find_symbol (Clight.genv_genv ge0) _write8s =
  Some (jet_symbol_block _write8s).
Proof. vm_compute; reflexivity. Qed.
Lemma buffer8_write_array_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _write8s) Ptrofs.zero) = Some (Internal f_write8s).
Proof. vm_compute; reflexivity. Qed.

Lemma eval_buffer8_tag e le m j len :
  0 <= j <= Int64.max_unsigned -> 0 <= len <= Int64.max_unsigned ->
  le!_i = Some (Vlong (Int64.repr j)) -> le!_len = Some (Vlong (Int64.repr len)) ->
  eval_expr ge0 e le m buffer8_tag_expr (Vint (bit_int (j <=? len))).
Proof.
  intros HJ HL HI HLen. eapply eval_Ebinop with
    (v1 := Vlong (Int64.repr j)) (v2 := Vlong (Int64.repr len)).
  - apply eval_Etempvar; exact HI.
  - apply eval_Etempvar; exact HLen.
  - change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr len) (Int64.repr j)))) =
      Some (Vint (bit_int (j <=? len)))).
    unfold Int64.ltu. rewrite !Int64.unsigned_repr by lia.
    destruct (j <=? len) eqn:HC.
    + apply Z.leb_le in HC. rewrite zlt_false by lia; reflexivity.
    + apply Z.leb_gt in HC. rewrite zlt_true by lia; reflexivity.
Qed.

Definition buffer8_write_present_temps le bi input len j :=
  PTree.set _len (Vlong (Int64.repr (len - j)))
    (PTree.set _buf (Vptr bi (Ptrofs.repr (input + j))) le).

Lemma exec_buffer8_write_present e le m mf bf base bi input j len :
  e!_write8s = None -> le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_buf = Some (Vptr bi (Ptrofs.repr input)) -> le!_len = Some (Vlong (Int64.repr len)) ->
  le!_i = Some (Vlong (Int64.repr j)) ->
  0 <= input -> input + j <= Ptrofs.max_unsigned -> (0 <= j <= len /\ len <= Int64.max_unsigned) ->
  Clight2.eval_funcall ge0 m (Internal f_write8s)
    [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr j)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 e le m buffer8_present_branch E0
    (buffer8_write_present_temps le bi input len j) mf Out_normal.
Proof.
  intros HE HD HB HL HI HInput HMax HLen HR.
  set (next := PTree.set _buf (Vptr bi (Ptrofs.repr (input + j))) le).
  assert (Haddr : Ptrofs.add (Ptrofs.repr input)
    (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr j))) = Ptrofs.repr (input + j)).
  { unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by lia.
    unfold Ptrofs.mul, Ptrofs.add. change (Ptrofs.unsigned (Ptrofs.repr 1)) with 1.
    rewrite (Ptrofs.unsigned_repr j) by lia. rewrite Z.mul_1_l.
    rewrite !Ptrofs.unsigned_repr by lia; reflexivity. }
  unfold buffer8_present_branch, buffer8_loop_body, buffer8_actual_loop; cbn [f_simplicity_write_buffer8 fn_body].
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
  - eapply exec_Scall with (vf := Vptr (jet_symbol_block _write8s) Ptrofs.zero)
      (vargs := [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input); Vlong (Int64.repr j)])
      (f := Internal f_write8s) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [exact HE|exact buffer8_write_array_symbol]|apply deref_loc_reference; reflexivity].
    + eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; exact HB|reflexivity|].
      eapply eval_Econs; [apply eval_Etempvar; exact HI|reflexivity|apply eval_Enil].
    + exact buffer8_write_array_funct.
    + reflexivity.
    + exact HR.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := next).
    + apply exec_set. eapply eval_Ebinop with (v1 := Vptr bi (Ptrofs.repr input)) (v2 := Vlong (Int64.repr j)).
      * apply eval_Etempvar; exact HB.
      * apply eval_Etempvar; exact HI.
      * change (Some (Vptr bi (Ptrofs.add (Ptrofs.repr input)
          (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr j))))) = Some (Vptr bi (Ptrofs.repr (input + j)))).
        rewrite Haddr; reflexivity.
    + apply exec_set. eapply eval_Ebinop with (v1 := Vlong (Int64.repr len)) (v2 := Vlong (Int64.repr j)).
      * apply eval_Etempvar. unfold next; rewrite PTree.gso by discriminate; exact HL.
      * apply eval_Etempvar. unfold next; rewrite PTree.gso by discriminate; exact HI.
      * change (Some (Vlong (Int64.sub (Int64.repr len) (Int64.repr j))) = Some (Vlong (Int64.repr (len - j)))).
        unfold Int64.sub. rewrite !Int64.unsigned_repr by lia; reflexivity.
Qed.

Lemma exec_buffer8_write_absent e le m mf bf base j :
  e!_skipBits = None -> le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_i = Some (Vlong (Int64.repr j)) -> 0 <= j <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_skipBits)
    [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (8 * j))] E0 mf Vundef ->
  Clight2.exec_stmt ge0 e le m buffer8_skip_call E0 le mf Out_normal.
Proof.
  intros HE HD HI HJ HR. eapply call_frame_writer with (f := f_skipBits)
    (b := jet_symbol_block _skipBits) (v := Vlong (Int64.repr (8 * j))) (vret := Vundef).
  - exact HE.
  - exact HD.
  - reflexivity.
  - exact buffer8_skipBits_symbol.
  - exact buffer8_skipBits_funct.
  - exact (eval_buffer8_skip_expr e le m j HJ HI).
  - reflexivity.
  - exact HR.
Qed.

Lemma exec_buffer8_write_body e le m mb mf lef bf base j len :
  e!_writeBit = None -> le!_dst = Some (Vptr bf (Ptrofs.repr base)) ->
  le!_i = Some (Vlong (Int64.repr j)) -> le!_len = Some (Vlong (Int64.repr len)) ->
  0 < j <= Int64.max_unsigned -> 0 <= len <= Int64.max_unsigned ->
  Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bf (Ptrofs.repr base); Vint (bit_int (j <=? len))] E0 mb (Vint (bit_int (j <=? len))) ->
  Clight2.exec_stmt ge0 e (PTree.set _t'2 (Vint (bit_int (j <=? len))) le) mb
    (if j <=? len then buffer8_present_branch else buffer8_skip_call) E0 lef mf Out_normal ->
  Clight2.exec_stmt ge0 e le m buffer8_loop_body E0 lef mf Out_normal.
Proof.
  intros HE HD HI HL HJ HLen HBit HBranch. unfold buffer8_loop_body. rewrite buffer8_actual_loop_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
  - eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
    + pose proof (eval_buffer8_guard e le m j ltac:(lia) HI) as HG.
      rewrite (proj2 (Z.ltb_lt 0 j) ltac:(lia)) in HG; exact HG.
    + reflexivity.
    + apply exec_Sskip.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb)
      (le1 := PTree.set _t'2 (Vint (bit_int (j <=? len))) le).
    + eapply exec_Scall with (vf := Vptr (jet_symbol_block _writeBit) Ptrofs.zero)
        (vargs := [Vptr bf (Ptrofs.repr base); Vint (bit_int (j <=? len))])
        (f := Internal f_writeBit) (vres := Vint (bit_int (j <=? len))).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [exact HE|exact buffer8_writeBit_symbol]|apply deref_loc_reference; reflexivity].
      * eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
        eapply eval_Econs.
        -- exact (eval_buffer8_tag e le m j len ltac:(lia) HLen HI HL).
        -- destruct (j <=? len); reflexivity.
        -- apply eval_Enil.
      * exact buffer8_writeBit_funct.
      * reflexivity.
      * exact HBit.
    + eapply exec_Sifthenelse with (v1 := Vint (bit_int (j <=? len))) (b := j <=? len).
      * apply eval_Etempvar; apply PTree.gss.
      * destruct (j <=? len); reflexivity.
      * exact HBranch.
Qed.

Lemma exec_buffer8_write_halve e le m j :
  le!_i = Some (Vlong (Int64.repr j)) -> 0 <= j <= Int64.max_unsigned ->
  Clight2.exec_stmt ge0 e le m buffer8_loop_update E0
    (PTree.set _i (Vlong (Int64.repr (j / 2))) le) m Out_normal.
Proof.
  change (le!_i = Some (Vlong (Int64.repr j)) -> 0 <= j <= Int64.max_unsigned ->
    Clight2.exec_stmt ge0 e le m buffer8_read_update E0
      (PTree.set _i (Vlong (Int64.repr (j / 2))) le) m Out_normal).
  apply exec_buffer8_read_halve.
Qed.
