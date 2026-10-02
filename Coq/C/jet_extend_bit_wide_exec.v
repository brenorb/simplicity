(** Exact left_extend_1_{16,32,64} conditional assignments and payload casts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_readBit_layout C.jet_complement1_exec C.jet_wide C.jet_pad_bit_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wide_extend_bit s := match s with
  W16 => f_simplicity_left_extend_1_16 | W32 => f_simplicity_left_extend_1_32
  | W64 => f_simplicity_left_extend_1_64 end.
Definition extend_bit_type s := match s with W16 => tint | W32 => tuint | W64 => tulong end.
Definition extend_bit_true_expr s := match s with
  W16 => Econst_int (Int.repr 65535) tint
  | W32 => Econst_int (Int.repr (-1)) tuint
  | W64 => Econst_long (Int64.repr (-1)) tulong end.
Definition extend_bit_raw s (bit : bool) := match s with
  W16 => Vint (if bit then Int.repr 65535 else Int.zero)
  | W32 => Vint (if bit then Int.mone else Int.zero)
  | W64 => Vlong (if bit then Int64.mone else Int64.zero) end.
Definition extend_bit_choice_expr s (bit : bool) :=
  Ecast (if bit then extend_bit_true_expr s else Econst_int Int.zero tint) (extend_bit_type s).
Definition wide_extend_bit_choose s :=
  Sifthenelse (Etempvar _bit tbool)
    (Sset _t'2 (extend_bit_choice_expr s Datatypes.true))
    (Sset _t'2 (extend_bit_choice_expr s Datatypes.false)).
Definition le_wide_extend_bit env s bd dofs bs sofs bit :=
  PTree.set _bit (Vint (bit_int bit)) (PTree.set _t'1 (Vint (bit_int bit))
    (le_arith8_layout env (wide_extend_bit s) bd dofs bs sofs)).

Lemma wide_extend_bit_body s : (wide_extend_bit s).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence bit_jet_read (Sset _bit (Ecast (Etempvar _t'1 tbool) tbool)))
      (Ssequence
        (Ssequence (wide_extend_bit_choose s)
          (frame_writer_call (wide_writer_id s) tulong tvoid (Etempvar _t'2 (extend_bit_type s))))
        (Sreturn (Some (Econst_int Int.one tint))))).
Proof. destruct s; reflexivity. Qed.

Lemma eval_extend_bit_choice_expr e le m s bit :
  eval_expr ge0 e le m (extend_bit_choice_expr s bit) (extend_bit_raw s bit).
Proof. destruct s, bit; eapply eval_Ecast; [constructor|reflexivity|constructor|reflexivity|
  constructor|reflexivity|constructor|reflexivity|constructor|reflexivity|constructor|reflexivity]. Qed.

Lemma exec_wide_extend_bit_choose e le m s bit :
  le!_bit = Some (Vint (bit_int bit)) ->
  Clight2.exec_stmt ge0 e le m (wide_extend_bit_choose s)
    E0 (PTree.set _t'2 (extend_bit_raw s bit) le) m Out_normal.
Proof.
  intros HB. unfold wide_extend_bit_choose.
  eapply exec_Sifthenelse with (v1 := Vint (bit_int bit)) (b := bit).
  - eapply eval_Etempvar; exact HB.
  - unfold bit_int; destruct bit; reflexivity.
  - destruct bit; apply exec_set; apply eval_extend_bit_choice_expr.
Qed.

Lemma extend_bit_long64 bit :
  extend_bit_long W64 bit = if bit then Int64.mone else Int64.zero.
Proof.
  destruct bit; [|reflexivity].
  change (Int64.repr (Int64.unsigned Int64.mone) = Int64.mone).
  apply Int64.repr_unsigned.
Qed.

Lemma extend_bit_raw_cast s bit m :
  sem_cast (extend_bit_raw s bit) (extend_bit_type s) tulong m =
    Some (Vlong (extend_bit_long s bit)).
Proof. destruct s, bit; try reflexivity. rewrite extend_bit_long64; reflexivity. Qed.

Lemma eval_wide_extend_bit_composes env s m ma mc mr me mf bl bd dbase bs sbase bytes bit :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bit)) ->
  Clight2.eval_funcall ge0 mr (Internal (wide_writer s))
    [Vptr bd (Ptrofs.repr dbase); Vlong (extend_bit_long s bit)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (wide_extend_bit s))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (wide_extend_bit s) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := PTree.set _t'2 (extend_bit_raw s bit)
      (le_wide_extend_bit env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit))
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct s; reflexivity|destruct s; reflexivity| |exact HA].
    destruct s; change (list_disjoint [_dst; _src; _env] [_bit; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|H2]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite wide_extend_bit_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct s; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_wide_extend_bit env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_bit_jet_read; exact Hread.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bit)).
           ++ eapply eval_Etempvar; rewrite PTree.gss; reflexivity.
           ++ unfold bit_int; destruct bit; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
             (le1 := PTree.set _t'2 (extend_bit_raw s bit)
               (le_wide_extend_bit env s bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit)).
           { apply exec_wide_extend_bit_choose. unfold le_wide_extend_bit; rewrite PTree.gss; reflexivity. }
           eapply call_frame_writer_cast with (f := wide_writer s)
             (vraw := extend_bit_raw s bit) (v := Vlong (extend_bit_long s bit)) (vret := Vundef).
           ++ destruct s; reflexivity.
           ++ unfold le_wide_extend_bit, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
           ++ destruct s; reflexivity.
           ++ apply wide_writer_symbol.
           ++ apply wide_writer_funct.
           ++ eapply eval_Etempvar; rewrite PTree.gss; reflexivity.
           ++ apply extend_bit_raw_cast.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some; apply eval_Econst_int.
  - destruct s; cbn; split; solve [discriminate | reflexivity].
  - destruct s; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
