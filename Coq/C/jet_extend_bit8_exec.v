(** Exact left_extend_1_8 conditional assignment and int-to-byte cast. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_readBit_layout C.jet_complement1_exec C.jet_wide C.jet_pad_bit_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition extend_bit8_arg (bit : bool) := if bit then Int.repr 255 else Int.zero.
Definition extend_bit8_choice_expr (bit : bool) :=
  Ecast (if bit then Econst_int (Int.repr 255) tint else Econst_int Int.zero tint) tint.
Definition extend_bit8_choose :=
  Sifthenelse (Etempvar _bit tbool)
    (Sset _t'2 (extend_bit8_choice_expr Datatypes.true))
    (Sset _t'2 (extend_bit8_choice_expr Datatypes.false)).
Definition le_extend_bit8 env bd dofs bs sofs bit :=
  PTree.set _bit (Vint (bit_int bit)) (PTree.set _t'1 (Vint (bit_int bit))
    (le_arith8_layout env f_simplicity_left_extend_1_8 bd dofs bs sofs)).

Lemma extend_bit8_body : f_simplicity_left_extend_1_8.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence bit_jet_read (Sset _bit (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence extend_bit8_choose
          (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'2 tint)))
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. reflexivity. Qed.

Lemma eval_extend_bit8_choice_expr e le m bit :
  eval_expr ge0 e le m (extend_bit8_choice_expr bit) (Vint (extend_bit8_arg bit)).
Proof. destruct bit; eapply eval_Ecast; [constructor|reflexivity|constructor|reflexivity]. Qed.

Lemma exec_extend_bit8_choose e le m bit :
  le!_bit = Some (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 e le m extend_bit8_choose
    E0 (PTree.set _t'2 (Vint (extend_bit8_arg bit)) le) m Out_normal.
Proof.
  intros HB. unfold extend_bit8_choose.
  eapply exec_Sifthenelse with (v1 := Vint (bit_int bit)) (b := bit).
  - eapply eval_Etempvar; exact HB.
  - unfold bit_int; destruct bit; reflexivity.
  - destruct bit; apply exec_set; apply eval_extend_bit8_choice_expr.
Qed.

Lemma extend_bit8_cast bit m :
  sem_cast (Vint (extend_bit8_arg bit)) tint tuchar m = Some (Vint (extend_bit8_arg bit)).
Proof. destruct bit; reflexivity. Qed.

Lemma eval_extend_bit8_composes env m ma mc mr me mf bl bd dbase bs sbase bytes bit :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bit)) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (extend_bit8_arg bit)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_left_extend_1_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_left_extend_1_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'2 (Vint (extend_bit8_arg bit))
      (le_extend_bit8 env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit))
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_bit; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|H2]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite extend_bit8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_extend_bit8 env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_bit_jet_read; exact Hread.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bit)).
           ++ eapply eval_Etempvar; rewrite PTree.gss; reflexivity.
           ++ unfold bit_int; destruct bit; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
             (le1 := PTree.set _t'2 (Vint (extend_bit8_arg bit))
               (le_extend_bit8 env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit)).
           { apply exec_extend_bit8_choose. unfold le_extend_bit8; rewrite PTree.gss; reflexivity. }
           eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (extend_bit8_arg bit)) (v := Vint (extend_bit8_arg bit)) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le_extend_bit8, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ eapply eval_Etempvar; rewrite PTree.gss; reflexivity.
           ++ apply extend_bit8_cast.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some; apply eval_Econst_int.
  - cbn; split; solve [discriminate | reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
