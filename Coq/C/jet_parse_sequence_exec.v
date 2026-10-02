(** Exact parse_sequence masks, argument casts and conditional Clight calls.
    Function composition is internal; the layout consumer discharges every
    intermediate call from initial frames. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Require Import C.jet_arith8_layout_exec C.jet_increment8_exec C.jet_increment32_layout_exec.
Require Import C.jet_wide C.jet_parse_sequence_spec C.jet_skipBits_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition long_one_shift_expr k :=
  Ebinop Oshl (Ecast (Econst_int (Int.repr 1) tint) tulong)
    (Econst_int (Int.repr k) tint) tulong.
Lemma eval_long_one_shift e le m k :
  0 <= k < 64 ->
  eval_expr ge0 e le m (long_one_shift_expr k)
    (Vlong (Int64.shl Int64.one (Int64.repr k))).
Proof.
  intros HK.
  assert (HM : 0 <= k <= Int.max_unsigned).
  { change (0 <= k <= 4294967295); lia. }
  assert (HG : Int.ltu (Int.repr k) Int64.iwordsize' = Datatypes.true).
  { unfold Int.ltu. rewrite Int.unsigned_repr by exact HM.
    change ((if zlt k 64 then Datatypes.true else Datatypes.false) = Datatypes.true).
    rewrite zlt_true by lia. reflexivity. }
  unfold long_one_shift_expr.
  eapply eval_Ebinop with (v1 := Vlong Int64.one) (v2 := Vint (Int.repr k)).
  - eapply eval_Ecast with (v1 := Vint Int.one); [apply eval_Econst_int|reflexivity].
  - apply eval_Econst_int.
  - change ((if Int.ltu (Int.repr k) Int64.iwordsize'
      then Some (Vlong (Int64.shl Int64.one (Int64.repr (Int.unsigned (Int.repr k)))))
      else None) = Some (Vlong (Int64.shl Int64.one (Int64.repr k)))).
    rewrite HG, Int.unsigned_repr by exact HM. reflexivity.
Qed.

Definition parse_sequence_enabled_expr :=
  Ebinop Olt (Etempvar _nSequence tulong) (long_one_shift_expr 31) tint.
Definition parse_sequence_tag_expr :=
  Ebinop Oand (Etempvar _nSequence tulong) (long_one_shift_expr 22) tulong.
Definition parse_sequence_payload_expr :=
  Ebinop Oand (Etempvar _nSequence tulong) (Econst_int (Int.repr 65535) tint) tulong.
Definition le_parse_sequence_x env bd dofs bs sofs r :=
  PTree.set _nSequence (Vlong r) (PTree.set _t'1 (Vlong r)
    (le_arith8_layout env f_simplicity_parse_sequence bd dofs bs sofs)).
Definition le_parse_sequence_flag env bd dofs bs sofs r :=
  PTree.set _t'2 (Vint (if parse_sequence_enabled r then Int.one else Int.zero))
    (le_parse_sequence_x env bd dofs bs sofs r).

Lemma eval_parse_sequence_enabled e le m r :
  le!_nSequence = Some (Vlong r) ->
  eval_expr ge0 e le m parse_sequence_enabled_expr
    (Vint (if parse_sequence_enabled r then Int.one else Int.zero)).
Proof.
  intros HX. unfold parse_sequence_enabled_expr.
  eapply eval_Ebinop with (v1 := Vlong r)
    (v2 := Vlong (Int64.shl Int64.one (Int64.repr 31))).
  - apply eval_Etempvar; exact HX.
  - apply eval_long_one_shift; lia.
  - change (Some (Val.of_bool (parse_sequence_enabled r)) =
      Some (Vint (if parse_sequence_enabled r then Int.one else Int.zero))).
    destruct (parse_sequence_enabled r); reflexivity.
Qed.

Lemma cast_parse_sequence_enabled m r :
  sem_cast (Vint (if parse_sequence_enabled r then Int.one else Int.zero))
    (typeof parse_sequence_enabled_expr) tbool m =
    Some (Vint (if parse_sequence_enabled r then Int.one else Int.zero)).
Proof. destruct (parse_sequence_enabled r); reflexivity. Qed.

Lemma eval_parse_sequence_tag e le m r :
  le!_nSequence = Some (Vlong r) ->
  eval_expr ge0 e le m parse_sequence_tag_expr
    (Vlong (Int64.and r (Int64.shl Int64.one (Int64.repr 22)))).
Proof.
  intros HX. unfold parse_sequence_tag_expr.
  eapply eval_Ebinop with (v1 := Vlong r)
    (v2 := Vlong (Int64.shl Int64.one (Int64.repr 22))).
  - apply eval_Etempvar; exact HX.
  - apply eval_long_one_shift; lia.
  - reflexivity.
Qed.

Lemma cast_parse_sequence_tag m r :
  sem_cast (Vlong (Int64.and r (Int64.shl Int64.one (Int64.repr 22))))
    (typeof parse_sequence_tag_expr) tbool m =
    Some (Vint (if parse_sequence_tag r then Int.one else Int.zero)).
Proof.
  unfold parse_sequence_tag.
  change (Some (Vint (if Int64.eq (Int64.and r (Int64.shl Int64.one (Int64.repr 22)))
    Int64.zero then Int.zero else Int.one)) =
    Some (Vint (if negb (Int64.eq (Int64.and r (Int64.shl Int64.one (Int64.repr 22)))
    Int64.zero) then Int.one else Int.zero))).
  destruct (Int64.eq (Int64.and r (Int64.shl Int64.one (Int64.repr 22))) Int64.zero);
    reflexivity.
Qed.

Lemma eval_parse_sequence_payload e le m r :
  le!_nSequence = Some (Vlong r) ->
  eval_expr ge0 e le m parse_sequence_payload_expr (Vlong (parse_sequence_payload r)).
Proof.
  intros HX. unfold parse_sequence_payload_expr.
  eapply eval_Ebinop with (v1 := Vlong r) (v2 := Vint (Int.repr 65535)).
  - apply eval_Etempvar; exact HX.
  - apply eval_Econst_int.
  - reflexivity.
Qed.

Lemma symbol_skipBits :
  Genv.find_symbol (Clight.genv_genv ge0) _skipBits = Some (jet_symbol_block _skipBits).
Proof. vm_compute; reflexivity. Qed.
Lemma funct_skipBits :
  Genv.find_funct (Clight.genv_genv ge0) (Vptr (jet_symbol_block _skipBits) Ptrofs.zero) =
    Some (Internal f_skipBits).
Proof. vm_compute; reflexivity. Qed.

Definition parse_sequence_branch_calls mb me bd dofs r : Prop :=
  if parse_sequence_enabled r then
    exists mt,
      Clight2.eval_funcall ge0 mb (Internal f_writeBit)
        [Vptr bd dofs; Vint (if parse_sequence_tag r then Int.one else Int.zero)] E0 mt
        (Vint (if parse_sequence_tag r then Int.one else Int.zero)) /\
      Clight2.eval_funcall ge0 mt (Internal (wide_writer W16))
        [Vptr bd dofs; Vlong (parse_sequence_payload r)] E0 me Vundef
  else Clight2.eval_funcall ge0 mb (Internal f_skipBits)
    [Vptr bd dofs; Vlong (Int64.repr 17)] E0 me Vundef.

Lemma eval_parse_sequence_composes env m ma mc mr mb me mf bl bd dofs bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read32)
    [Vptr bl Ptrofs.zero] E0 mr (Vlong r) ->
  Clight2.eval_funcall ge0 mr (Internal f_writeBit)
    [Vptr bd dofs; Vint (if parse_sequence_enabled r then Int.one else Int.zero)] E0 mb
    (Vint (if parse_sequence_enabled r then Int.one else Int.zero)) ->
  parse_sequence_branch_calls mb me bd dofs r ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_parse_sequence)
    [Vptr bd dofs; Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hflag Hbranch HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_parse_sequence bd dofs bs (Ptrofs.repr sbase))
    (le2 := le_parse_sequence_flag env bd dofs bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_nSequence; _t'2; _t'1]).
    intros i j HI HJ Heq; cbn in HI, HJ; subst j.
    destruct HI as [HI|[HI|[HI|HI]]]; destruct HJ as [HJ|[HJ|[HJ|HJ]]];
      try contradiction; vm_compute in HI, HJ; congruence.
  - unfold f_simplicity_parse_sequence; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_parse_sequence_x env bd dofs bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- eapply call_increment32_read; [apply symbol_read32|apply funct_read32|exact Hread].
        -- apply exec_set. apply eval_Etempvar; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me)
          (le1 := le_parse_sequence_flag env bd dofs bs (Ptrofs.repr sbase) r).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb)
             (le1 := le_parse_sequence_flag env bd dofs bs (Ptrofs.repr sbase) r).
           ++ eapply exec_Scall with
                (vf := Vptr (jet_symbol_block _writeBit) Ptrofs.zero)
                (vargs := [Vptr bd dofs;
                  Vint (if parse_sequence_enabled r then Int.one else Int.zero)])
                (f := Internal f_writeBit)
                (vres := Vint (if parse_sequence_enabled r then Int.one else Int.zero)).
              ** reflexivity.
              ** eapply eval_Elvalue.
                 --- eapply eval_Evar_global; [reflexivity|apply symbol_writeBit].
                 --- apply deref_loc_reference; reflexivity.
              ** eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
                 eapply eval_Econs.
                 --- apply eval_parse_sequence_enabled; reflexivity.
                 --- apply cast_parse_sequence_enabled.
                 --- apply eval_Enil.
              ** apply funct_writeBit.
              ** reflexivity.
              ** exact Hflag.
           ++ eapply exec_Sifthenelse with
                (v1 := Vint (if parse_sequence_enabled r then Int.one else Int.zero))
                (b := parse_sequence_enabled r).
              ** apply eval_Etempvar; reflexivity.
              ** destruct (parse_sequence_enabled r); reflexivity.
              ** unfold parse_sequence_branch_calls in Hbranch.
                 destruct (parse_sequence_enabled r) eqn:Hen.
                 --- destruct Hbranch as [mt [Htag Hpayload]].
                     eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mt).
                     +++ eapply call_frame_writer_cast with (f := f_writeBit)
                           (vraw := Vlong (Int64.and r (Int64.shl Int64.one (Int64.repr 22))))
                           (v := Vint (if parse_sequence_tag r then Int.one else Int.zero))
                           (vret := Vint (if parse_sequence_tag r then Int.one else Int.zero)).
                         *** reflexivity.
                         *** reflexivity.
                         *** reflexivity.
                         *** apply symbol_writeBit.
                         *** apply funct_writeBit.
                         *** apply eval_parse_sequence_tag; reflexivity.
                         *** apply cast_parse_sequence_tag.
                         *** exact Htag.
                     +++ eapply call_frame_writer_cast with (f := wide_writer W16)
                           (b := jet_symbol_block (wide_writer_id W16))
                           (vraw := Vlong (parse_sequence_payload r))
                           (v := Vlong (parse_sequence_payload r)) (vret := Vundef).
                         *** reflexivity.
                         *** reflexivity.
                         *** reflexivity.
                         *** exact (wide_writer_symbol W16).
                         *** exact (wide_writer_funct W16).
                         *** apply eval_parse_sequence_payload; reflexivity.
                         *** reflexivity.
                         *** exact Hpayload.
                 --- eapply call_frame_writer_cast with (f := f_skipBits)
                       (b := jet_symbol_block _skipBits)
                       (vraw := Vint (Int.repr 17))
                       (v := Vlong (Int64.repr 17)) (vret := Vundef).
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ reflexivity.
                     +++ apply symbol_skipBits.
                     +++ apply funct_skipBits.
                     +++ apply eval_Econst_int.
                     +++ reflexivity.
                     +++ exact Hbranch.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
