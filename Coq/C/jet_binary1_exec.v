(** Complete one-bit and/or/xor calls, including their actual C branches. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_readBit_layout C.jet_increment8_exec C.jet_binary_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition binary1 k := match k with BAnd => f_simplicity_and_1 | BOr => f_simplicity_or_1 | BXor => f_simplicity_xor_1 end.
Definition binary1_read result := Scall (Some result)
  (Evar _readBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tbool cc_default))
  [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition binary1_choose k := match k with
  | BAnd => Sifthenelse (Etempvar _x tbool)
      (Sset _t'3 (Ecast (Etempvar _y tbool) tbool)) (Sset _t'3 (Econst_int Int.zero tint))
  | BOr => Sifthenelse (Etempvar _x tbool)
      (Sset _t'3 (Econst_int Int.one tint)) (Sset _t'3 (Ecast (Etempvar _y tbool) tbool))
  | BXor => Sskip
  end.
Definition binary1_arg k := match k with
  | BXor => Ebinop Oxor (Etempvar _x tbool) (Etempvar _y tbool) tint
  | _ => Etempvar _t'3 tint end.
Definition binary1_write k := match k with
  | BXor => frame_writer_call _writeBit tbool tbool (binary1_arg k)
  | _ => Ssequence (binary1_choose k) (frame_writer_call _writeBit tbool tbool (binary1_arg k)) end.
Definition le_binary1_x env k bd dofs bs sofs bx :=
  PTree.set _x (Vint (bit_int bx)) (PTree.set _t'1 (Vint (bit_int bx))
    (le_arith8_layout env (binary1 k) bd dofs bs sofs)).
Definition le_binary1_y env k bd dofs bs sofs bx bity :=
  PTree.set _y (Vint (bit_int bity)) (PTree.set _t'2 (Vint (bit_int bity))
    (le_binary1_x env k bd dofs bs sofs bx)).
Definition le_binary1_result k le bx bity := match k with
  | BXor => le | _ => PTree.set _t'3 (Vint (bit_int (binary_bool k bx bity))) le end.

Lemma binary1_body k : (binary1 k).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (binary1_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tbool) tbool)))
        (Ssequence (binary1_write k) (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct k; reflexivity. Qed.

Lemma call_binary1_read result le m mr bl bit :
  Clight2.eval_funcall ge0 m (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (binary1_read result)
    E0 (PTree.set result (Vint (bit_int bit)) le) mr Out_normal.
Proof.
  intros HC. eapply exec_Scall with (vf := Vptr (jet_symbol_block _readBit) Ptrofs.zero)
    (vargs := [Vptr bl Ptrofs.zero]) (f := Internal f_readBit) (vres := Vint (bit_int bit)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply symbol_readBit].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Eaddrof. eapply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply funct_readBit.
  - reflexivity.
  - exact HC.
Qed.

Lemma exec_binary1_choose k e le m bx bity : k <> BXor ->
  le!_x = Some (Vint (bit_int bx)) -> le!_y = Some (Vint (bit_int bity)) ->
  Clight2.exec_stmt ge0 e le m (binary1_choose k) E0
    (PTree.set _t'3 (Vint (bit_int (binary_bool k bx bity))) le) m Out_normal.
Proof.
  intros HK HX HY. destruct k; [| |contradiction]; destruct bx;
    eapply exec_Sifthenelse with (v1 := Vint (bit_int _)).
  all: try (eapply eval_Etempvar; exact HX).
  all: try reflexivity.
  all: apply exec_set.
  - eapply eval_Ecast with (v1 := Vint (bit_int bity));
      [eapply eval_Etempvar; exact HY|destruct bity; reflexivity].
  - apply eval_Econst_int.
  - apply eval_Econst_int.
  - eapply eval_Ecast with (v1 := Vint (bit_int bity));
      [eapply eval_Etempvar; exact HY|destruct bity; reflexivity].
Qed.

Lemma eval_binary1_arg k e le m bx bity :
  le!_x = Some (Vint (bit_int bx)) -> le!_y = Some (Vint (bit_int bity)) ->
  eval_expr ge0 e (le_binary1_result k le bx bity) m (binary1_arg k)
    (Vint (bit_int (binary_bool k bx bity))).
Proof.
  intros HX HY. destruct k.
  - apply eval_Etempvar. apply PTree.gss.
  - apply eval_Etempvar. apply PTree.gss.
  - eapply eval_Ebinop with (v1 := Vint (bit_int bx)) (v2 := Vint (bit_int bity)).
    + eapply eval_Etempvar; exact HX.
    + eapply eval_Etempvar; exact HY.
    + destruct bx, bity; reflexivity.
Qed.

Lemma exec_binary1_write k e le m me bd dbase bx bity :
  e!_writeBit = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_x = Some (Vint (bit_int bx)) -> le!_y = Some (Vint (bit_int bity)) ->
  Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (binary_bool k bx bity))] E0 me
    (Vint (bit_int (binary_bool k bx bity))) ->
  Clight2.exec_stmt ge0 e le m (binary1_write k) E0 (le_binary1_result k le bx bity) me Out_normal.
Proof.
  intros HE HD HX HY HW.
  assert (HCall : Clight2.exec_stmt ge0 e (le_binary1_result k le bx bity) m
    (frame_writer_call _writeBit tbool tbool (binary1_arg k)) E0
    (le_binary1_result k le bx bity) me Out_normal).
  { eapply call_frame_writer_cast with (f := f_writeBit)
      (vraw := Vint (bit_int (binary_bool k bx bity)))
      (v := Vint (bit_int (binary_bool k bx bity)))
      (vret := Vint (bit_int (binary_bool k bx bity))).
    - exact HE.
    - unfold le_binary1_result. destruct k; try exact HD.
      all: rewrite PTree.gso by discriminate; exact HD.
    - reflexivity.
    - apply symbol_writeBit.
    - apply funct_writeBit.
    - apply eval_binary1_arg; assumption.
    - destruct k, bx, bity; reflexivity.
    - exact HW. }
  destruct k.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + apply (exec_binary1_choose BAnd e le m bx bity); [discriminate|exact HX|exact HY].
    + exact HCall.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + apply (exec_binary1_choose BOr e le m bx bity); [discriminate|exact HX|exact HY].
    + exact HCall.
  - exact HCall.
Qed.

Lemma eval_binary1_composes env k m ma mc mr mr2 me mf bl bd dbase bs sbase bytes bx bity :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bx)) ->
  Clight2.eval_funcall ge0 mr (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr2 (Vint (bit_int bity)) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (binary_bool k bx bity))] E0 me
    (Vint (bit_int (binary_bool k bx bity))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (binary1 k))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (binary1 k) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_binary1_result k (le_binary1_y env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bx bity) bx bity)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k; reflexivity|destruct k; reflexivity| |exact HA].
    destruct k; cbn; intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite binary1_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_binary1_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bx).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary1_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bx)).
           ++ eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ destruct bx; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_binary1_y env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bx bity).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary1_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bity)).
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + destruct bity; reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply exec_binary1_write; [reflexivity| | | |exact Hwrite].
           ++ unfold le_binary1_y, le_binary1_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ unfold le_binary1_y, le_binary1_x.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ unfold le_binary1_y. rewrite PTree.gss. reflexivity.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k; cbn; split; solve [discriminate|reflexivity].
  - destruct k; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
