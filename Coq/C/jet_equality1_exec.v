(** Actual one-bit equality: two Boolean reads, comparison, bit write and cleanup. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word Simplicity.Bit C.jets C.jet_exec C.jet_one8 C.jet_spec.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8_exec.
Require Import C.jet_binary1_exec C.jet_readBit_layout C.jet_equality_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition eq1_expr := Ebinop Oeq (Etempvar _x tbool) (Etempvar _y tbool) tint.
Definition eq1_bit := Bool.eqb.
Definition le_eq1_x env bd dofs bs sofs r :=
  PTree.set _x (Vint (bit_int r)) (PTree.set _t'1 (Vint (bit_int r))
    (le_arith8_layout env f_simplicity_eq_1 bd dofs bs sofs)).
Definition le_eq1_y env bd dofs bs sofs r t :=
  PTree.set _y (Vint (bit_int t)) (PTree.set _t'2 (Vint (bit_int t))
    (le_eq1_x env bd dofs bs sofs r)).

Lemma eq1_body : f_simplicity_eq_1.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (binary1_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tbool) tbool)))
        (Ssequence (frame_writer_call _writeBit tbool tbool eq1_expr)
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. reflexivity. Qed.

Lemma eval_eq1_expr e le m r t :
  le!_x = Some (Vint (bit_int r)) -> le!_y = Some (Vint (bit_int t)) ->
  eval_expr ge0 e le m eq1_expr (Vint (bit_int (eq1_bit r t))).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vint (bit_int r)) (v2 := Vint (bit_int t)).
  - apply eval_Etempvar; exact HX.
  - apply eval_Etempvar; exact HY.
  - destruct r, t; reflexivity.
Qed.

Lemma eval_eq1_composes env m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int r)) ->
  Clight2.eval_funcall ge0 mr (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr2 (Vint (bit_int t)) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (eq1_bit r t))] E0 me (Vint (bit_int (eq1_bit r t))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_eq_1)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_eq_1 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_eq1_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite eq1_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_eq1_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary1_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int r)).
           ++ eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ destruct r; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_eq1_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary1_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int t)).
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + destruct t; reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (eq1_bit r t))) (v := Vint (bit_int (eq1_bit r t)))
             (vret := Vint (bit_int (eq1_bit r t))).
           ++ reflexivity.
           ++ unfold le_eq1_y, le_eq1_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_eq1_expr.
              ** unfold le_eq1_y, le_eq1_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_eq1_y. rewrite PTree.gss. reflexivity.
           ++ destruct (eq1_bit r t); reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
