(** Function-boundary composition for the generated add_64 Clight body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Require Import C.jet_arith8_layout_exec C.jet_add64_wide_word.
Require Import C.jet_increment64_layout_exec C.jet_increment8_exec C.jet_wide.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition le_add64_layout_x bd dofs bs sofs r :=
  PTree.set _x (Vlong r)
    (PTree.set _t'1 (Vlong r)
      (le_arith8_layout f_simplicity_add_64 bd dofs bs sofs)).

Definition le_add64_layout_ready bd dofs bs sofs r s :=
  PTree.set _y (Vlong s)
    (PTree.set _t'2 (Vlong s)
      (le_add64_layout_x bd dofs bs sofs r)).

Definition add64_read_stmt (tmp : ident) : statement :=
  Scall (Some tmp)
    (Evar _simplicity_read64
      (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)
        tulong cc_default))
    ((Eaddrof (Evar _src (Tstruct _frameItem noattr))
      (tptr (Tstruct _frameItem noattr))) :: nil).

Definition add64_carry_expr : expr :=
  Ebinop Olt
    (Ebinop Osub
      (Ebinop Omul (Econst_int Int.one tuint)
        (Econst_long (Int64.repr (-1)) tulong) tulong)
      (Etempvar _y tulong) tulong)
    (Etempvar _x tulong) tint.

Definition add64_sum_expr : expr :=
  Ecast
    (Ebinop Oadd
      (Ebinop Omul (Econst_int Int.one tuint)
        (Etempvar _x tulong) tulong)
      (Etempvar _y tulong) tulong)
    tulong.

Lemma symbol_read64 :
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read64 =
    Some (jet_symbol_block _simplicity_read64).
Proof. vm_compute; reflexivity. Qed.

Lemma funct_read64 :
  Genv.find_funct (Clight.genv_genv ge0)
    (Vptr (jet_symbol_block _simplicity_read64) Ptrofs.zero) =
    Some (Internal f_simplicity_read64).
Proof. vm_compute; reflexivity. Qed.

Lemma call_add64_read le m m' bl tmp r :
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read64 =
    Some (jet_symbol_block _simplicity_read64) ->
  Genv.find_funct (Clight.genv_genv ge0)
    (Vptr (jet_symbol_block _simplicity_read64) Ptrofs.zero) =
    Some (Internal f_simplicity_read64) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 m' (Vlong r) ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_one8 bl) le m
    (add64_read_stmt tmp) E0 (PTree.set tmp (Vlong r) le) m' Out_normal.
Proof.
  intros Hsym Hfun Hread.
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr (jet_symbol_block _simplicity_read64) Ptrofs.zero)
      (vargs := [Vptr bl Ptrofs.zero])
      (f := Internal f_simplicity_read64) (vres := Vlong r).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [simpl; reflexivity|exact Hsym].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Eaddrof. eapply eval_Evar_local. simpl [e_one8]. reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - exact Hfun.
  - reflexivity.
  - exact Hread.
Qed.

Lemma eval_add64_carry_env m e le r s :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong s) ->
  eval_expr ge0 e le m add64_carry_expr
    (Vint (if add64_carry r s then Int.one else Int.zero)).
Proof.
  intros HX HY. unfold add64_carry_expr, add64_carry.
  eapply eval_Ebinop with (v1 := Vlong (Int64.sub Int64.mone s))
      (v2 := Vlong r).
  - eapply eval_Ebinop with (v1 := Vlong Int64.mone) (v2 := Vlong s).
    + eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong Int64.mone).
      * apply eval_Econst_int.
      * apply eval_Econst_long.
      * unfold sem_binary_operation, sem_mul, sem_binarith.
        change (Some (Vlong (Int64.mul Int64.one Int64.mone)) =
          Some (Vlong Int64.mone)).
        rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
    + eapply eval_Etempvar. exact HY.
    + reflexivity.
  - eapply eval_Etempvar. exact HX.
  - change (Some (Val.of_bool (Int64.ltu (Int64.sub Int64.mone s) r)) =
      Some (Vint (if Int64.ltu (Int64.sub Int64.mone s) r
        then Int.one else Int.zero))).
    destruct (Int64.ltu (Int64.sub Int64.mone s) r); reflexivity.
Qed.

Lemma eval_add64_sum_env m e le r s :
  le!_x = Some (Vlong r) -> le!_y = Some (Vlong s) ->
  eval_expr ge0 e le m add64_sum_expr (Vlong (add64_payload r s)).
Proof.
  intros HX HY. unfold add64_sum_expr, add64_payload.
  eapply eval_Ecast.
  - eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vlong s).
    + eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
      * apply eval_Econst_int.
      * eapply eval_Etempvar. exact HX.
      * change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
        rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
    + eapply eval_Etempvar. exact HY.
    + reflexivity.
  - reflexivity.
Qed.

Lemma cast_add64_carry m r s :
  sem_cast (Vint (if add64_carry r s then Int.one else Int.zero))
    (typeof add64_carry_expr) tbool m =
  Some (Vint (if add64_carry r s then Int.one else Int.zero)).
Proof.
  unfold add64_carry, sem_cast, classify_cast.
  destruct (Int64.ltu (Int64.sub Int64.mone s) r); cbn; reflexivity.
Qed.

Lemma eval_add64_layout_composes m ma mc mr mr2 mb me mf bl bd dofs bs sbase bytes r s :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.eval_funcall ge0 mc (Internal f_simplicity_read64)
    [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  ClightBigstep.Clight2.eval_funcall ge0 mr (Internal f_simplicity_read64)
    [Vptr bl Ptrofs.zero] E0 mr2 (Vlong s) ->
  ClightBigstep.Clight2.eval_funcall ge0 mr2 (Internal f_writeBit)
    [Vptr bd dofs; Vint (if add64_carry r s then Int.one else Int.zero)]
    E0 mb (Vint (if add64_carry r s then Int.one else Int.zero)) ->
  ClightBigstep.Clight2.eval_funcall ge0 mb (Internal (wide_writer W64))
    [Vptr bd dofs; Vlong (add64_payload r s)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_add_64)
    [Vptr bd dofs; Vptr bs (Ptrofs.repr sbase); Vundef] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hread2 Hbit Hwrite HF.
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl)
      (le1 := le_arith8_layout f_simplicity_add_64 bd dofs bs (Ptrofs.repr sbase))
      (le2 := le_add64_layout_ready bd dofs bs (Ptrofs.repr sbase) r s)
      (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]).
    intros id1 id2 H1 H2 Heq. simpl in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - unfold f_simplicity_add_64; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_add64_layout_x bd dofs bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- eapply call_add64_read; [apply symbol_read64|apply funct_read64|exact Hread].
        -- apply exec_set. eapply eval_Etempvar. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_add64_layout_ready bd dofs bs (Ptrofs.repr sbase) r s).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - eapply call_add64_read; [apply symbol_read64|apply funct_read64|exact Hread2].
          - apply exec_set. eapply eval_Etempvar. reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- eapply call_frame_writer_cast with (f := f_writeBit)
             (vraw := Vint (if add64_carry r s then Int.one else Int.zero))
             (v := Vint (if add64_carry r s then Int.one else Int.zero))
             (vret := Vint (if add64_carry r s then Int.one else Int.zero)).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_add64_carry_env; reflexivity.
           ++ apply cast_add64_carry.
           ++ exact Hbit.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply call_frame_writer_cast with (f := wide_writer W64)
                (b := jet_symbol_block (wide_writer_id W64))
                (vraw := Vlong (add64_payload r s))
                (v := Vlong (add64_payload r s)) (vret := Vundef).
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** exact (wide_writer_symbol W64).
              ** exact (wide_writer_funct W64).
              ** apply eval_add64_sum_env; reflexivity.
              ** reflexivity.
              ** exact Hwrite.
           ++ apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
