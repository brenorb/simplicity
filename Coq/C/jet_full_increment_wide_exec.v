(** Actual full_increment_16/32/64 calls, retaining mixed uint/ulong operations. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_increment8_exec C.jet_binary1_exec C.jet_binary_wide_exec C.jet_readBit_layout.
Require Import C.jet_full_increment_wide_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_full_increment s := match s with
  | W16 => f_simplicity_full_increment_16 | W32 => f_simplicity_full_increment_32
  | W64 => f_simplicity_full_increment_64 end.
Definition wide_full_increment_limit_expr s := match s with
  | W16 => Econst_int (Int.repr 65535) tint
  | W32 => Econst_int Int.mone tuint | W64 => Econst_long Int64.mone tulong end.
Definition wide_full_increment_limit_type s := match s with W64 => tulong | _ => tuint end.
Definition wide_full_increment_limit_value s := match s with
  | W16 => Vint (Int.repr 65535) | W32 => Vint Int.mone | W64 => Vlong Int64.mone end.
Definition wide_full_increment_sub_value s cin := match s with
  | W16 => Vint (Int.sub (Int.repr 65535) (bit_int cin))
  | W32 => Vint (Int.sub Int.mone (bit_int cin))
  | W64 => Vlong (Int64.sub Int64.mone (bit_long cin)) end.
Definition wide_full_increment_sub_expr s :=
  Ebinop Osub
    (Ebinop Omul (Econst_int Int.one tuint) (wide_full_increment_limit_expr s)
      (wide_full_increment_limit_type s))
    (Etempvar _z tbool) (wide_full_increment_limit_type s).
Definition wide_full_increment_carry_expr s :=
  Ebinop Olt (wide_full_increment_sub_expr s) (Etempvar _x tulong) tint.
Definition wide_full_increment_sum_expr :=
  Ecast (Ebinop Oadd
    (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong)
    (Etempvar _z tbool) tulong) tulong.
Definition le_wide_full_increment_z env s bd dofs bs sofs cin :=
  PTree.set _z (Vint (bit_int cin)) (PTree.set _t'1 (Vint (bit_int cin))
    (le_arith8_layout env (wide_full_increment s) bd dofs bs sofs)).
Definition le_wide_full_increment_x env s bd dofs bs sofs cin r :=
  PTree.set _x (Vlong r) (PTree.set _t'2 (Vlong r)
    (le_wide_full_increment_z env s bd dofs bs sofs cin)).

Lemma wide_full_increment_body s : (wide_full_increment s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _z (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _x (Etempvar _t'2 tulong)))
        (Ssequence (frame_writer_call _writeBit tbool tbool (wide_full_increment_carry_expr s))
          (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid wide_full_increment_sum_expr)
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_wide_full_increment_sub_expr e le m s cin :
  le!_z = Some (Vint (bit_int cin)) ->
  eval_expr ge0 e le m (wide_full_increment_sub_expr s) (wide_full_increment_sub_value s cin).
Proof.
  intros HZ. eapply eval_Ebinop with (v1 := wide_full_increment_limit_value s) (v2 := Vint (bit_int cin)).
  - eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := wide_full_increment_limit_value s).
    + apply eval_Econst_int.
    + destruct s; [apply eval_Econst_int|apply eval_Econst_int|apply eval_Econst_long].
    + destruct s.
      * change (Some (Vint (Int.mul Int.one (Int.repr 65535))) = Some (Vint (Int.repr 65535))).
        rewrite Int.mul_commut, Int.mul_one. reflexivity.
      * change (Some (Vint (Int.mul Int.one Int.mone)) = Some (Vint Int.mone)).
        rewrite Int.mul_commut, Int.mul_one. reflexivity.
      * change (Some (Vlong (Int64.mul Int64.one Int64.mone)) = Some (Vlong Int64.mone)).
        rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
  - apply eval_Etempvar; exact HZ.
  - destruct s, cin; reflexivity.
Qed.

Lemma eval_wide_full_increment_carry_expr e le m s cin r :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m (wide_full_increment_carry_expr s)
    (Vint (bit_int (wide_full_increment_carry s cin r))).
Proof.
  intros HZ HX. eapply eval_Ebinop with (v1 := wide_full_increment_sub_value s cin) (v2 := Vlong r).
  - apply eval_wide_full_increment_sub_expr; exact HZ.
  - apply eval_Etempvar; exact HX.
  - destruct s, cin.
    all: lazymatch goal with
      | |- _ = Some (Vint (bit_int ?b)) =>
          change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity
      end.
Qed.

Lemma eval_wide_full_increment_sum_expr e le m cin r :
  le!_z = Some (Vint (bit_int cin)) -> le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m wide_full_increment_sum_expr (Vlong (wide_full_increment_payload cin r)).
Proof.
  intros HZ HX. unfold wide_full_increment_sum_expr.
  eapply eval_Ecast with (v1 := Vlong (wide_full_increment_payload cin r)).
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

Lemma eval_wide_full_increment_composes env s m ma mc mr mr2 mb me mf bl bd dbase bs sbase bytes cin r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int cin)) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_full_increment_carry s cin r))]
    E0 mb (Vint (bit_int (wide_full_increment_carry s cin r))) ->
  Clight2.eval_funcall ge0 mb (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (wide_full_increment_payload cin r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_full_increment s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hbit Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_full_increment s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_full_increment_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_z; _x; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_full_increment_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_full_increment_z env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary1_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int cin)).
           ++ apply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ destruct cin; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_wide_full_increment_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        assert (HZ : (le_wide_full_increment_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_z =
          Some (Vint (bit_int cin))).
        { unfold le_wide_full_increment_x, le_wide_full_increment_z.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        assert (HX : (le_wide_full_increment_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_x =
          Some (Vlong r)) by (apply PTree.gss).
        assert (HDst : (le_wide_full_increment_x env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) cin r)!_dst =
          Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le_wide_full_increment_x, le_wide_full_increment_z, le_arith8_layout.
          rewrite !PTree.gso by discriminate. apply PTree.gss. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (wide_full_increment_carry s cin r)))
             (v := Vint (bit_int (wide_full_increment_carry s cin r)))
             (vret := Vint (bit_int (wide_full_increment_carry s cin r))).
           ++ reflexivity.
           ++ exact HDst.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_wide_full_increment_carry_expr; assumption.
           ++ destruct (wide_full_increment_carry s cin r); reflexivity.
           ++ exact Hbit.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply call_frame_writer with (f := wide_writer s)
                (v := Vlong (wide_full_increment_payload cin r)) (vret := Vundef).
              ** destruct s; reflexivity.
              ** exact HDst.
              ** destruct s; reflexivity.
              ** apply wide_writer_symbol.
              ** apply wide_writer_funct.
              ** apply eval_wide_full_increment_sum_expr; assumption.
              ** reflexivity.
              ** exact Hwrite.
           ++ apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate|reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
