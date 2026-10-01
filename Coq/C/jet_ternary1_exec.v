(** Actual one-bit maj/xor_xor/ch branches and complete C calls. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_readBit_layout C.jet_increment8_exec C.jet_binary1_exec C.jet_ternary_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition ternary1 k := match k with TMaj => f_simplicity_maj_1 | TXorXor => f_simplicity_xor_xor_1 | TCh => f_simplicity_ch_1 end.
Definition ternary1_choose k := match k with
  | TMaj => Ssequence
      (Ssequence
        (Sifthenelse (Etempvar _x tbool)
          (Sset _t'4 (Ecast (Etempvar _y tbool) tbool)) (Sset _t'4 (Econst_int Int.zero tint)))
        (Sifthenelse (Etempvar _t'4 tint)
          (Sset _t'5 (Econst_int Int.one tint))
          (Sifthenelse (Etempvar _y tbool)
            (Ssequence (Sset _t'5 (Ecast (Etempvar _z tbool) tbool))
              (Sset _t'5 (Ecast (Etempvar _t'5 tint) tbool)))
            (Sset _t'5 (Ecast (Econst_int Int.zero tint) tbool)))))
      (Sifthenelse (Etempvar _t'5 tint)
        (Sset _t'6 (Econst_int Int.one tint))
        (Sifthenelse (Etempvar _z tbool)
          (Ssequence (Sset _t'6 (Ecast (Etempvar _x tbool) tbool))
            (Sset _t'6 (Ecast (Etempvar _t'6 tint) tbool)))
          (Sset _t'6 (Ecast (Econst_int Int.zero tint) tbool))))
  | TXorXor => Sskip
  | TCh => Sifthenelse (Etempvar _x tbool)
      (Sset _t'4 (Ecast (Etempvar _y tbool) tint)) (Sset _t'4 (Ecast (Etempvar _z tbool) tint))
  end.
Definition ternary1_arg k := match k with
  | TMaj => Etempvar _t'6 tint
  | TXorXor => Ebinop Oxor (Ebinop Oxor (Etempvar _x tbool) (Etempvar _y tbool) tint) (Etempvar _z tbool) tint
  | TCh => Etempvar _t'4 tint end.
Definition ternary1_write k := match k with
  | TXorXor => frame_writer_call _writeBit tbool tbool (ternary1_arg k)
  | _ => Ssequence (ternary1_choose k) (frame_writer_call _writeBit tbool tbool (ternary1_arg k)) end.
Definition le_ternary1_x env k bd dofs bs sofs bx :=
  PTree.set _x (Vint (bit_int bx)) (PTree.set _t'1 (Vint (bit_int bx))
    (le_arith8_layout env (ternary1 k) bd dofs bs sofs)).
Definition le_ternary1_y env k bd dofs bs sofs bx bity :=
  PTree.set _y (Vint (bit_int bity)) (PTree.set _t'2 (Vint (bit_int bity))
    (le_ternary1_x env k bd dofs bs sofs bx)).
Definition le_ternary1_z env k bd dofs bs sofs bx bity bz :=
  PTree.set _z (Vint (bit_int bz)) (PTree.set _t'3 (Vint (bit_int bz))
    (le_ternary1_y env k bd dofs bs sofs bx bity)).

Lemma ternary1_body k : (ternary1 k).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary1_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (binary1_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tbool) tbool)))
        (Ssequence
          (Ssequence (binary1_read _t'3) (Sset _z (Ecast (Etempvar _t'3 tbool) tbool)))
          (Ssequence (ternary1_write k) (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct k; reflexivity. Qed.

Lemma eval_ternary1_xor e le m bx bity bz :
  le!_x = Some (Vint (bit_int bx)) -> le!_y = Some (Vint (bit_int bity)) ->
  le!_z = Some (Vint (bit_int bz)) ->
  eval_expr ge0 e le m (ternary1_arg TXorXor) (Vint (bit_int (ternary_bool TXorXor bx bity bz))).
Proof.
  intros HX HY HZ. eapply eval_Ebinop with (v1 := Vint (bit_int (xorb bx bity))) (v2 := Vint (bit_int bz)).
  - eapply eval_Ebinop with (v1 := Vint (bit_int bx)) (v2 := Vint (bit_int bity)).
    + apply eval_Etempvar; exact HX.
    + apply eval_Etempvar; exact HY.
    + destruct bx, bity; reflexivity.
  - apply eval_Etempvar; exact HZ.
  - destruct bx, bity, bz; reflexivity.
Qed.

(** This bounded structural tactic executes only sets, casts and conditionals
    after the three returned booleans have been split. It never reduces memory. *)
Local Ltac ternary1_lookup :=
  repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate];
  first [reflexivity | eassumption].
Local Ltac ternary1_eval_atom :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ => apply eval_Etempvar; ternary1_lookup
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => apply eval_Econst_int
  | |- eval_expr _ _ _ _ (Ecast _ _) _ => eapply eval_Ecast; [ternary1_eval_atom | reflexivity]
  end.
Local Ltac ternary1_exec_step :=
  lazymatch goal with
  | |- exec_stmt function_entry2 ?ge ?e ?le ?m (if ?c then ?st else ?sf) ?tr ?le' ?m' ?out =>
      tryif has_evar c then fail 1 "unresolved branch condition" else
      let choice := eval vm_compute in c in
      lazymatch choice with
      | true => change (exec_stmt function_entry2 ge e le m st tr le' m' out)
      | false => change (exec_stmt function_entry2 ge e le m sf tr le' m' out)
      end
  | |- exec_stmt function_entry2 _ _ _ ?m (Ssequence _ _) _ _ _ _ =>
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
  | |- exec_stmt function_entry2 _ _ _ _ (Sifthenelse _ _ _) _ _ _ _ =>
      eapply exec_Sifthenelse
  | |- exec_stmt function_entry2 _ _ _ _ (Sset _ _) _ _ _ _ => apply exec_set
  | |- exec_stmt function_entry2 _ _ _ _ Sskip _ _ _ _ => apply exec_Sskip
  | |- eval_expr _ _ _ _ _ _ => ternary1_eval_atom
  | |- _ = Some _ => reflexivity
  end.

Lemma exec_ternary1_choose_result k e le m bx bity bz :
  le!_x = Some (Vint (bit_int bx)) -> le!_y = Some (Vint (bit_int bity)) ->
  le!_z = Some (Vint (bit_int bz)) ->
  exists le',
    Clight2.exec_stmt ge0 e le m (ternary1_choose k) E0 le' m Out_normal /\
    le'!_dst = le!_dst /\
    eval_expr ge0 e le' m (ternary1_arg k) (Vint (bit_int (ternary_bool k bx bity bz))).
Proof.
  intros HX HY HZ. unfold Clight2.exec_stmt. destruct k.
  - unfold ternary1_choose. destruct bx, bity, bz; eexists; split.
    all: repeat ternary1_exec_step.
    all: split; [ternary1_lookup | apply eval_Etempvar; ternary1_lookup].
  - exists le. split; [apply exec_Sskip|]. split; [reflexivity|]. apply eval_ternary1_xor; assumption.
  - unfold ternary1_choose. destruct bx, bity, bz; eexists; split.
    all: repeat ternary1_exec_step.
    all: split; [ternary1_lookup | apply eval_Etempvar; ternary1_lookup].
Qed.

Lemma exec_ternary1_write k e le m me bd dbase bx bity bz :
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_x = Some (Vint (bit_int bx)) -> le!_y = Some (Vint (bit_int bity)) -> le!_z = Some (Vint (bit_int bz)) ->
  Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (ternary_bool k bx bity bz))] E0 me
    (Vint (bit_int (ternary_bool k bx bity bz))) ->
  exists le', Clight2.exec_stmt ge0 e le m (ternary1_write k) E0 le' me Out_normal.
Proof.
  intros HE HD HX HY HZ HW.
  destruct (exec_ternary1_choose_result k e le m bx bity bz HX HY HZ) as [le' [HC [HD' HV]]].
  assert (HCall : Clight2.exec_stmt ge0 e le' m
    (frame_writer_call _writeBit tbool tbool (ternary1_arg k)) E0 le' me Out_normal).
  { eapply call_frame_writer_cast with (f := f_writeBit)
      (vraw := Vint (bit_int (ternary_bool k bx bity bz)))
      (v := Vint (bit_int (ternary_bool k bx bity bz)))
      (vret := Vint (bit_int (ternary_bool k bx bity bz))).
    - exact HE.
    - rewrite HD'; exact HD.
    - reflexivity.
    - apply symbol_writeBit.
    - apply funct_writeBit.
    - exact HV.
    - destruct k, bx, bity, bz; reflexivity.
    - exact HW. }
  exists le'. destruct k.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m); eauto.
  - inversion HC; subst. exact HCall.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m); eauto.
Qed.

Lemma eval_ternary1_composes env k m ma mc mr mr2 mr3 me mf bl bd dbase bs sbase bytes bx bity bz :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bx)) ->
  Clight2.eval_funcall ge0 mr (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr2 (Vint (bit_int bity)) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr3 (Vint (bit_int bz)) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_writeBit)
    [Vptr bd (Ptrofs.repr dbase); Vint (bit_int (ternary_bool k bx bity bz))] E0 me
    (Vint (bit_int (ternary_bool k bx bity bz))) ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (ternary1 k))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hwrite HF.
  destruct (exec_ternary1_write k (e_one8 bl)
    (le_ternary1_z env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bx bity bz)
    mr3 me bd dbase bx bity bz) as [le' Htail].
  - reflexivity.
  - unfold le_ternary1_z, le_ternary1_y, le_ternary1_x, le_arith8_layout.
    rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
  - unfold le_ternary1_z, le_ternary1_y, le_ternary1_x.
    rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
  - unfold le_ternary1_z, le_ternary1_y.
    rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
  - unfold le_ternary1_z. rewrite PTree.gss. reflexivity.
  - exact Hwrite.
  - eapply eval_funcall_internal with (e := e_one8 bl)
      (le1 := le_arith8_layout env (ternary1 k) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
      (le2 := le') (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
    + eapply entry_frame_jet; [destruct k; reflexivity|destruct k; reflexivity| |exact HA].
      destruct k; cbn; intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
        repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
        try contradiction; vm_compute in H1, H2; congruence.
    + rewrite ternary1_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
      * eapply exec_frame_jet_copy; eauto. destruct k; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
          (le1 := le_ternary1_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bx).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
          - apply call_binary1_read. exact Hread1.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bx)).
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + destruct bx; reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_ternary1_y env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bx bity).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary1_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bity)).
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + destruct bity; reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
          (le1 := le_ternary1_z env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bx bity bz).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
          - apply call_binary1_read. exact Hread3.
          - apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bz)).
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + destruct bz; reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me); [exact Htail|].
        apply exec_Sreturn_some. apply eval_Econst_int.
    + destruct k; cbn; split; solve [discriminate|reflexivity].
    + destruct k; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
