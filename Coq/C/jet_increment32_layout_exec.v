(** Function-boundary composition for the generated increment_32 Clight body. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Require Import C.jet_arith8_layout_exec C.jet_wide C.jet_increment32_wide_word.
Require Import C.jet_increment8_exec C.jet_read32_layout_total.
Import Values Mem Ctypes ListNotations Clightdefs Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition le_increment32_layout_x env bd dofs bs sofs r :=
  PTree.set _x (Vlong r)
    (PTree.set _t'1 (Vlong r)
      (le_arith8_layout env f_simplicity_increment_32 bd dofs bs sofs)).

Definition increment32_read_stmt : statement :=
  Scall (Some _t'1)
    (Evar _simplicity_read32
      (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil)
        tulong cc_default))
    ((Eaddrof (Evar _src (Tstruct _frameItem noattr))
      (tptr (Tstruct _frameItem noattr))) :: nil).

Definition increment32_carry_expr : expr :=
  Ebinop Olt
    (Ebinop Osub
      (Ebinop Omul (Econst_int Int.one tuint)
        (Econst_int (Int.repr (-1)) tuint) tuint)
      (Econst_int Int.one tint) tuint)
    (Etempvar _x tulong) tint.

Definition increment32_sum_expr : expr :=
  Ecast
    (Ebinop Oadd
      (Ebinop Omul (Econst_int Int.one tuint)
        (Etempvar _x tulong) tulong)
      (Econst_int Int.one tint) tulong)
    tulong.

Lemma symbol_read32 :
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read32 =
    Some (jet_symbol_block _simplicity_read32).
Proof. vm_compute; reflexivity. Qed.

Lemma funct_read32 :
  Genv.find_funct (Clight.genv_genv ge0)
    (Vptr (jet_symbol_block _simplicity_read32) Ptrofs.zero) =
    Some (Internal f_simplicity_read32).
Proof. vm_compute; reflexivity. Qed.

Lemma call_increment32_read le m m' bl r b :
  Genv.find_symbol (Clight.genv_genv ge0) _simplicity_read32 = Some b ->
  Genv.find_funct (Clight.genv_genv ge0) (Vptr b Ptrofs.zero) =
    Some (Internal f_simplicity_read32) ->
  ClightBigstep.Clight2.eval_funcall ge0 m
    (Internal f_simplicity_read32) [Vptr bl Ptrofs.zero] E0 m' (Vlong r) ->
  ClightBigstep.Clight2.exec_stmt ge0 (e_one8 bl) le m increment32_read_stmt
    E0 (PTree.set _t'1 (Vlong r) le) m' Out_normal.
Proof.
  intros Hsym Hfun Hread.
  eapply ClightBigstep.exec_Scall
    with (vf := Vptr b Ptrofs.zero) (vargs := [Vptr bl Ptrofs.zero])
      (f := Internal f_simplicity_read32) (vres := Vlong r).
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

Lemma eval_increment32_carry_env m e le r :
  le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m increment32_carry_expr
    (Vint (if increment32_carry r then Int.one else Int.zero)).
Proof.
  intros HX. unfold increment32_carry_expr, increment32_carry.
  eapply eval_Ebinop with (v1 := Vint (Int.repr 4294967294)) (v2 := Vlong r).
  - eapply eval_Ebinop with (v1 := Vint Int.mone) (v2 := Vint Int.one).
    + eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint Int.mone).
      * apply eval_Econst_int.
      * apply eval_Econst_int.
      * unfold sem_binary_operation, sem_mul, sem_binarith.
        change (Some (Vint (Int.mul Int.one Int.mone)) = Some (Vint Int.mone)).
        rewrite Int.mul_commut, Int.mul_one. reflexivity.
    + apply eval_Econst_int.
    + unfold sem_binary_operation, sem_sub.
      change (Some (Vint (Int.sub Int.mone Int.one)) =
        Some (Vint (Int.repr 4294967294))).
      unfold Int.sub. rewrite Int.unsigned_mone, Int.unsigned_one. reflexivity.
  - eapply eval_Etempvar. exact HX.
  - change (Some (Val.of_bool (Int64.ltu (Int64.repr 4294967294) r)) =
      Some (Vint (if Int64.ltu (Int64.repr 4294967294) r then Int.one else Int.zero))).
    destruct (Int64.ltu (Int64.repr 4294967294) r); reflexivity.
Qed.

Lemma eval_increment32_sum_env m e le r :
  le!_x = Some (Vlong r) ->
  eval_expr ge0 e le m increment32_sum_expr (Vlong (increment32_payload r)).
Proof.
  intros HX. unfold increment32_sum_expr, increment32_payload.
  eapply eval_Ecast.
  - eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint Int.one).
    + eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vlong r).
      * apply eval_Econst_int.
      * eapply eval_Etempvar. exact HX.
      * change (Some (Vlong (Int64.mul Int64.one r)) = Some (Vlong r)).
        rewrite Int64.mul_commut, Int64.mul_one. reflexivity.
    + apply eval_Econst_int.
    + cbn; reflexivity.
  - reflexivity.
Qed.

Lemma cast_increment32_carry m r :
  sem_cast (Vint (if increment32_carry r then Int.one else Int.zero))
    (typeof increment32_carry_expr) tbool m =
  Some (Vint (if increment32_carry r then Int.one else Int.zero)).
Proof.
  unfold increment32_carry, sem_cast, classify_cast.
  destruct (Int64.ltu (Int64.repr 4294967294) r); cbn; reflexivity.
Qed.

Lemma eval_increment32_layout_composes env m ma mc mr mb me mf bl bd dofs bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) ->
  Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  ClightBigstep.Clight2.eval_funcall ge0 mc (Internal f_simplicity_read32)
    [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  ClightBigstep.Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd dofs; Vint (if increment32_carry r then Int.one else Int.zero)]
    E0 mb (Vint (if increment32_carry r then Int.one else Int.zero)) ->
  ClightBigstep.Clight2.eval_funcall ge0 mb (Internal (wide_writer W32))
    [Vptr bd dofs; Vlong (increment32_payload r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_increment_32)
    [Vptr bd dofs; Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hbit Hwrite HF.
  eapply ClightBigstep.eval_funcall_internal
    with (e := e_one8 bl)
      (le1 := le_arith8_layout env f_simplicity_increment_32 bd dofs bs (Ptrofs.repr sbase))
      (le2 := le_increment32_layout_x env bd dofs bs (Ptrofs.repr sbase) r)
      (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _t'1]).
    intros id1 id2 H1 H2 Heq. simpl in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - unfold f_simplicity_increment_32; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- eapply call_increment32_read; [apply symbol_read32|apply funct_read32|exact Hread].
        -- apply exec_set. eapply eval_Etempvar. reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb).
        -- eapply call_frame_writer_cast with
             (f := f_writeBit)
             (vraw := Vint (if increment32_carry r then Int.one else Int.zero))
             (v := Vint (if increment32_carry r then Int.one else Int.zero))
             (vret := Vint (if increment32_carry r then Int.one else Int.zero)).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply symbol_writeBit.
           ++ apply funct_writeBit.
           ++ apply eval_increment32_carry_env. reflexivity.
           ++ apply cast_increment32_carry.
           ++ exact Hbit.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
           ++ eapply call_frame_writer_cast with
                (f := wide_writer W32)
                (b := jet_symbol_block (wide_writer_id W32))
                (vraw := Vlong (increment32_payload r))
                (v := Vlong (increment32_payload r)) (vret := Vundef).
              ** reflexivity.
              ** reflexivity.
              ** reflexivity.
              ** exact (wide_writer_symbol W32).
              ** exact (wide_writer_funct W32).
              ** apply eval_increment32_sum_env. reflexivity.
              ** reflexivity.
              ** exact Hwrite.
           ++ apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
