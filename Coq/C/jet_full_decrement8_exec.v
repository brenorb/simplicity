(** Complete borrow-input byte decrement body, including actual promotions. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_increment8_exec C.jet_binary1_exec C.jet_binary8_exec C.jet_readBit_layout.
Require Import C.jet_full_decrement_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_decrement8_borrow_expr :=
  Ebinop Olt
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tuchar) tuint)
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _z tbool) tuint) tint.
Definition full_decrement8_payload_expr :=
  Ecast (Ebinop Osub
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tuchar) tuint)
    (Etempvar _z tbool) tuint) tuchar.
Definition le_full_decrement8_z env bd dofs bs sofs cin :=
  PTree.set _z (Vint (bit_int cin)) (PTree.set _t'1 (Vint (bit_int cin))
    (le_arith8_layout env f_simplicity_full_decrement_8 bd dofs bs sofs)).
Definition le_full_decrement8_x env bd dofs bs sofs cin r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'2 (Vint r)
    (le_full_decrement8_z env bd dofs bs sofs cin)).

Lemma full_decrement8_body : f_simplicity_full_decrement_8.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _z (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _x (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence (frame_writer_call _writeBit tbool tbool full_decrement8_borrow_expr)
          (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid full_decrement8_payload_expr)
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. reflexivity. Qed.

Lemma eval_full_decrement8_borrow_expr e le m cin r :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vint (Int.zero_ext 8 r)) ->
  eval_expr ge0 e le m full_decrement8_borrow_expr (Vint (bit_int (full_decrement8_borrow cin r))).
Proof.
  intros HZ HX. unfold full_decrement8_borrow_expr.
  eapply eval_Ebinop with (v1 := Vint (Int.zero_ext 8 r)) (v2 := Vint (bit_int cin)).
  - eapply eval_Ebinop.
    + apply eval_Econst_int.
    + apply eval_Etempvar. exact HX.
    + change (Some (Vint (Int.mul Int.one (Int.zero_ext 8 r))) = Some (Vint (Int.zero_ext 8 r))).
      rewrite Int.mul_commut, Int.mul_one. reflexivity.
  - eapply eval_Ebinop.
    + apply eval_Econst_int.
    + apply eval_Etempvar. exact HZ.
    + change (Some (Vint (Int.mul Int.one (bit_int cin))) = Some (Vint (bit_int cin))).
      rewrite Int.mul_commut, Int.mul_one. reflexivity.
  - change (Some (Val.of_bool (full_decrement8_borrow cin r)) =
      Some (Vint (bit_int (full_decrement8_borrow cin r)))).
    destruct (full_decrement8_borrow cin r); reflexivity.
Qed.

Lemma eval_full_decrement8_payload_expr e le m cin r :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vint (Int.zero_ext 8 r)) ->
  eval_expr ge0 e le m full_decrement8_payload_expr (Vint (full_decrement8_payload cin r)).
Proof.
  intros HZ HX. unfold full_decrement8_payload_expr, full_decrement8_payload.
  eapply eval_Ecast.
  - eapply eval_Ebinop.
    + eapply eval_Ebinop.
      * apply eval_Econst_int.
      * apply eval_Etempvar. exact HX.
      * reflexivity.
    + apply eval_Etempvar. exact HZ.
    + reflexivity.
  - reflexivity.
Qed.

Lemma eval_full_decrement8_composes env m ma mc mr mr2 mb me mf bl bd dbase bs sbase bytes cin r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int cin)) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (full_decrement8_borrow cin r))]
    E0 mb (Vint (bit_int (full_decrement8_borrow cin r))) ->
  Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (full_decrement8_payload cin r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_full_decrement_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_full_decrement_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_full_decrement8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_z; _x; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite full_decrement8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_full_decrement8_z env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary1_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int cin)).
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ destruct cin; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_full_decrement8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint r).
            + apply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        assert (HZ : (le_full_decrement8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_z =
          Some (Vint (bit_int cin))).
        { unfold le_full_decrement8_x, le_full_decrement8_z.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HX : (le_full_decrement8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_x =
          Some (Vint (Int.zero_ext 8 r))) by (apply PTree.gss).
        assert (HDst : (le_full_decrement8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_dst =
          Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le_full_decrement8_x, le_full_decrement8_z, le_arith8_layout.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (full_decrement8_borrow cin r)))
             (v := Vint (bit_int (full_decrement8_borrow cin r)))
             (vret := Vint (bit_int (full_decrement8_borrow cin r))).
           ++ reflexivity.
           ++ exact HDst.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_full_decrement8_borrow_expr; assumption.
           ++ destruct (full_decrement8_borrow cin r); reflexivity.
           ++ exact Hbit.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply call_frame_writer with (f := f_simplicity_write8)
                (v := Vint (full_decrement8_payload cin r)) (vret := Vundef).
              ** reflexivity.
              ** exact HDst.
              ** reflexivity.
              ** apply symbol_write8.
              ** apply funct_write8.
              ** apply eval_full_decrement8_payload_expr; assumption.
              ** change (Some (Vint (Int.zero_ext 8 (full_decrement8_payload cin r))) =
                   Some (Vint (full_decrement8_payload cin r))).
                 unfold full_decrement8_payload. rewrite Int.zero_ext_idem by lia. reflexivity.
              ** exact Hwrite.
           ++ apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
