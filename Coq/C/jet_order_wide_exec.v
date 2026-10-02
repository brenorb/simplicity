(** Actual lt/le_16/32/64 bodies: two readers, a bit comparison/write and cleanup. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary_wide_exec C.jet_readBit_layout C.jet_increment8_exec.
Require Import C.jet_predicate_wide_exec C.jet_order_spec C.jet_subtract_word.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition order_cmp k := match k with OLt => Clt | OLe => Cle end.
Definition order_binop k := match k with OLt => Olt | OLe => Ole end.
Definition wide_order k s := match k, s with
  | OLt, W16 => f_simplicity_lt_16 | OLt, W32 => f_simplicity_lt_32 | OLt, W64 => f_simplicity_lt_64
  | OLe, W16 => f_simplicity_le_16 | OLe, W32 => f_simplicity_le_32 | OLe, W64 => f_simplicity_le_64 end.
Definition wide_order_expr k := Ebinop (order_binop k) (Etempvar _x tulong) (Etempvar _y tulong) tint.
Definition wide_order_bit k r t := Int64.cmpu (order_cmp k) r t.
Definition le_wide_order_x env k s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_order k s) bd dofs bs sofs)).
Definition le_wide_order_y env k s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t) (le_wide_order_x env k s bd dofs bs sofs r)).

Lemma wide_order_bit_numeric k r t :
  wide_order_bit k r t = order_numeric k (Int64.unsigned r) (Int64.unsigned t).
Proof.
  destruct k.
  - apply wide_subtract_borrow_numeric.
  - change (negb (wide_subtract_borrow t r) = (Int64.unsigned r <=? Int64.unsigned t)).
    rewrite wide_subtract_borrow_numeric.
    destruct (Int64.unsigned t <? Int64.unsigned r) eqn:H;
      [apply Z.ltb_lt in H|apply Z.ltb_ge in H]; cbn [negb]; symmetry;
      [apply Z.leb_gt|apply Z.leb_le]; lia.
Qed.
Lemma order_int64_denotes k n (x y : Ty.tySem (Word n)) r t :
  Int64.unsigned r = @toZ (WordToZ n) x -> Int64.unsigned t = @toZ (WordToZ n) y ->
  wide_order_bit k r t = Bit.toBool (@order_word_spec k n Alg.CoreFunSem (x, y)).
Proof. intros Hr Ht. rewrite order_word_spec_numeric, wide_order_bit_numeric, Hr, Ht. reflexivity. Qed.

Lemma wide_order_body k s : (wide_order k s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read s _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence (frame_writer_call _writeBit tbool tbool (wide_order_expr k))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct k, s; reflexivity. Qed.

Lemma eval_wide_order_expr e le m k r t :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) ->
  eval_expr ge0 e le m (wide_order_expr k) (Vint (bit_int (wide_order_bit k r t))).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong t).
  - apply eval_Etempvar; exact HX.
  - apply eval_Etempvar; exact HY.
  - destruct k.
    all: lazymatch goal with | |- _ = Some (Vint (bit_int ?b)) =>
      change (Some (Val.of_bool b) = Some (Vint (bit_int b))); destruct b; reflexivity end.
Qed.

Lemma eval_wide_order_composes env k s m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (wide_order_bit k r t))] E0 me (Vint (bit_int (wide_order_bit k r t))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_order k s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_order k s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_order_y env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k, s; reflexivity|destruct k, s; reflexivity| |exact HA].
    destruct k, s; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_order_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k, s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_order_x env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read. exact Hread1.
        -- apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. apply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (bit_int (wide_order_bit k r t))) (v := Vint (bit_int (wide_order_bit k r t)))
             (vret := Vint (bit_int (wide_order_bit k r t))).
           ++ reflexivity.
           ++ unfold le_wide_order_y, le_wide_order_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_wide_order_expr.
              ** unfold le_wide_order_y, le_wide_order_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_wide_order_y. rewrite PTree.gss. reflexivity.
           ++ destruct (wide_order_bit k r t); reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k, s; cbn; split; solve [discriminate|reflexivity].
  - destruct k, s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
