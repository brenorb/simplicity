(** Actual full_decrement_16/32/64 calls, retaining mixed uint/ulong operations. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_increment8_exec C.jet_binary1_exec C.jet_binary_wide_exec C.jet_readBit_layout.
Require Import C.jet_full_decrement_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_full_decrement s := match s with
  | W16 => f_simplicity_full_decrement_16 | W32 => f_simplicity_full_decrement_32
  | W64 => f_simplicity_full_decrement_64 end.
Definition wide_full_decrement_borrow_expr :=
  Ebinop Olt
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong)
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _z tbool) tuint) tint.
Definition wide_full_decrement_payload_expr :=
  Ecast (Ebinop Osub
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong)
    (Etempvar _z tbool) tulong) tulong.
Definition le_wide_full_decrement_z env s bd dofs bs sofs cin :=
  PTree.set _z (Vint (bit_int cin)) (PTree.set _t'1 (Vint (bit_int cin))
    (le_arith8_layout env (wide_full_decrement s) bd dofs bs sofs)).
Definition le_wide_full_decrement_x env s bd dofs bs sofs cin r :=
  PTree.set _x (Vlong r) (PTree.set _t'2 (Vlong r)
    (le_wide_full_decrement_z env s bd dofs bs sofs cin)).

Lemma wide_full_decrement_body s : (wide_full_decrement s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _z (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _x (Etempvar _t'2 tulong)))
        (Ssequence (frame_writer_call _writeBit tbool tbool wide_full_decrement_borrow_expr)
          (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid wide_full_decrement_payload_expr)
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_wide_full_decrement_borrow_expr e le m cin r :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m wide_full_decrement_borrow_expr
    (Vint (bit_int (wide_full_decrement_borrow cin r))).
Proof.
  intros HZ HX. unfold wide_full_decrement_borrow_expr.
  eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint (bit_int cin)).
  - eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
    + apply eval_Econst_int.
    + apply eval_Etempvar; exact HX.
    + change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
      rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
  - eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint (bit_int cin)).
    + apply eval_Econst_int.
    + apply eval_Etempvar; exact HZ.
    + change (Some (Vint (Int.mul Int.one (bit_int cin))) = Some (Vint (bit_int cin))).
      rewrite Int.mul_commut, Int.mul_one. reflexivity.
  - destruct cin.
    all: lazymatch goal with
      | |- _ = Some (Vint (bit_int ?b)) =>
          change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity
      end.
Qed.

Lemma eval_wide_full_decrement_payload_expr e le m cin r :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m wide_full_decrement_payload_expr (Vlong (wide_full_decrement_payload cin r)).
Proof.
  intros HZ HX. unfold wide_full_decrement_payload_expr.
  eapply eval_Ecast with (v1 := Vlong (wide_full_decrement_payload cin r)).
  - eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint (bit_int cin)).
    + eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
      * apply eval_Econst_int.
      * apply eval_Etempvar; exact HX.
      * change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
        rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
    + apply eval_Etempvar; exact HZ.
    + destruct cin; reflexivity.
  - reflexivity.
Qed.

Lemma eval_wide_full_decrement_composes env s m ma mc mr mr2 mb me mf bl bd dbase bs sbase bytes cin r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int cin)) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_full_decrement_borrow cin r))]
    E0 mb (Vint (bit_int (wide_full_decrement_borrow cin r))) ->
  Clight2.eval_funcall ge0 mb (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (wide_full_decrement_payload cin r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_full_decrement s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_full_decrement s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_full_decrement_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_z; _x; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_full_decrement_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_full_decrement_z env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary1_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int cin)).
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ destruct cin; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_wide_full_decrement_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        assert (HZ : (le_wide_full_decrement_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_z =
          Some (Vint (bit_int cin))).
        { unfold le_wide_full_decrement_x, le_wide_full_decrement_z.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HX : (le_wide_full_decrement_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_x =
          Some (Vlong r)) by (apply PTree.gss).
        assert (HDst : (le_wide_full_decrement_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_dst =
          Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le_wide_full_decrement_x, le_wide_full_decrement_z, le_arith8_layout.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (wide_full_decrement_borrow cin r)))
             (v := Vint (bit_int (wide_full_decrement_borrow cin r)))
             (vret := Vint (bit_int (wide_full_decrement_borrow cin r))).
           ++ reflexivity.
           ++ exact HDst.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_wide_full_decrement_borrow_expr; assumption.
           ++ destruct (wide_full_decrement_borrow cin r); reflexivity.
           ++ exact Hbit.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply call_frame_writer with (f := wide_writer s)
                (v := Vlong (wide_full_decrement_payload cin r)) (vret := Vundef).
              ** destruct s; reflexivity.
              ** exact HDst.
              ** destruct s; reflexivity.
              ** apply wide_writer_symbol.
              ** apply wide_writer_funct.
              ** apply eval_wide_full_decrement_payload_expr; assumption.
              ** reflexivity.
              ** exact Hwrite.
           ++ apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
