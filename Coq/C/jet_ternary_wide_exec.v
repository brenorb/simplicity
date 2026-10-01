(** Actual maj/xor_xor/ch bodies at 16/32/64 bits: three reads, one write. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec C.jet_wide.
Require Import C.jet_binary_spec C.jet_binary_wide_exec C.jet_ternary_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_ternary k s := match k, s with
  | TMaj, W16 => f_simplicity_maj_16 | TMaj, W32 => f_simplicity_maj_32 | TMaj, W64 => f_simplicity_maj_64
  | TXorXor, W16 => f_simplicity_xor_xor_16 | TXorXor, W32 => f_simplicity_xor_xor_32 | TXorXor, W64 => f_simplicity_xor_xor_64
  | TCh, W16 => f_simplicity_ch_16 | TCh, W32 => f_simplicity_ch_32 | TCh, W64 => f_simplicity_ch_64
  end.
Definition long_bin k a b := Ebinop (binary_clight_op k) a b tulong.
Definition wide_ternary_expr k := match k with
  | TMaj => long_bin BOr (long_bin BOr
      (long_bin BAnd (Etempvar _x tulong) (Etempvar _y tulong))
      (long_bin BAnd (Etempvar _y tulong) (Etempvar _z tulong)))
      (long_bin BAnd (Etempvar _z tulong) (Etempvar _x tulong))
  | TXorXor => long_bin BXor (long_bin BXor (Etempvar _x tulong) (Etempvar _y tulong)) (Etempvar _z tulong)
  | TCh => long_bin BOr (long_bin BAnd (Etempvar _x tulong) (Etempvar _y tulong))
      (long_bin BAnd (Eunop Onotint
        (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tulong) tulong) tulong) (Etempvar _z tulong))
  end.
Definition le_wide_ternary_x env k s bd dofs bs sofs r :=
  PTree.set _x (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env (wide_ternary k s) bd dofs bs sofs)).
Definition le_wide_ternary_y env k s bd dofs bs sofs r t :=
  PTree.set _y (Vlong t) (PTree.set _t'2 (Vlong t) (le_wide_ternary_x env k s bd dofs bs sofs r)).
Definition le_wide_ternary_z env k s bd dofs bs sofs r t u :=
  PTree.set _z (Vlong u) (PTree.set _t'3 (Vlong u) (le_wide_ternary_y env k s bd dofs bs sofs r t)).

Lemma wide_ternary_body k s : (wide_ternary k s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read s _t'1) (Sset _x (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read s _t'2) (Sset _y (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (wide_binary_read s _t'3) (Sset _z (Etempvar _t'3 tulong)))
          (Ssequence (frame_writer_call (wide_writer_id s) tulong tvoid (wide_ternary_expr k))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct k, s; reflexivity. Qed.

Lemma eval_long_bin k e le m a b r t : typeof a = tulong -> typeof b = tulong ->
  eval_expr ge0 e le m a (Vlong r) -> eval_expr ge0 e le m b (Vlong t) ->
  eval_expr ge0 e le m (long_bin k a b) (Vlong (binary_int64 k r t)).
Proof.
  intros HA HB HX HY. eapply eval_Ebinop; [exact HX|exact HY|].
  rewrite HA, HB. destruct k; reflexivity.
Qed.

Lemma eval_wide_ternary_expr k e le m r t u :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong t) -> le!_z = Some (Vlong u) ->
  eval_expr ge0 e le m (wide_ternary_expr k) (Vlong (ternary_int64 k r t u)).
Proof.
  intros HX HY HZ. destruct k; cbn [wide_ternary_expr ternary_int64].
  - apply (eval_long_bin BOr); try reflexivity.
    + apply (eval_long_bin BOr); try reflexivity;
        apply (eval_long_bin BAnd); try reflexivity; apply eval_Etempvar; assumption.
    + apply (eval_long_bin BAnd); try reflexivity; apply eval_Etempvar; assumption.
  - apply (eval_long_bin BXor); try reflexivity.
    + apply (eval_long_bin BXor); try reflexivity; apply eval_Etempvar; assumption.
    + apply eval_Etempvar; exact HZ.
  - apply (eval_long_bin BOr); try reflexivity.
    + apply (eval_long_bin BAnd); try reflexivity; apply eval_Etempvar; assumption.
    + apply (eval_long_bin BAnd); try reflexivity.
      * eapply eval_Eunop with (v1 := Vlong (Int64.mul Int64.one r)).
        -- eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
           ++ apply eval_Econst_int.
           ++ apply eval_Etempvar; exact HX.
           ++ reflexivity.
        -- reflexivity.
      * apply eval_Etempvar; exact HZ.
Qed.

Lemma eval_wide_ternary_composes env k s m ma mc mr mr2 mr3 me mf bl bd dbase bs sbase bytes r t u :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong t) ->
  Clight2.eval_funcall ge0 mr2 (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr3 (Vlong u) ->
  Clight2.eval_funcall ge0 mr3 (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (ternary_int64 k r t u)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_ternary k s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_ternary k s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_wide_ternary_z env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k, s; reflexivity|destruct k, s; reflexivity| |exact HA].
    destruct k, s; change (list_disjoint [_dst; _src; _env] [_x; _y; _z; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_ternary_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k, s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_ternary_x env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_wide_binary_read. exact Hread1.
        -- apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_wide_ternary_y env k s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_wide_binary_read. exact Hread2.
          - apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
          - apply call_wide_binary_read. exact Hread3.
          - apply exec_set. eapply eval_Etempvar. rewrite PTree.gss. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := wide_writer s)
             (vraw := Vlong (ternary_int64 k r t u)) (v := Vlong (ternary_int64 k r t u)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_ternary_z, le_wide_ternary_y, le_wide_ternary_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ apply eval_wide_ternary_expr.
              ** unfold le_wide_ternary_z, le_wide_ternary_y, le_wide_ternary_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_wide_ternary_z, le_wide_ternary_y.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_wide_ternary_z. rewrite PTree.gss. reflexivity.
           ++ destruct k; reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k, s; cbn; split; solve [discriminate|reflexivity].
  - destruct k, s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
