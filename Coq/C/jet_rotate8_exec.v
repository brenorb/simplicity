(** Complete actual left/right rotate_8 composition. The byte payload cast,
    scalar parameter casts and writer cast are retained explicitly. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_binary8_exec C.jet_binary_wide_exec C.jet_wide C.jet_read4_call.
Require Import C.jet_rotate8_helper C.jet_rotate8_count C.jet_rotate_count_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition rotate8_function (right : bool) :=
  if right then f_simplicity_right_rotate_8 else f_simplicity_left_rotate_8.
Definition rotate8_scalar_value (right : bool) r a :=
  rotate8_result r (if right then rotate8_reverse_amount a else a).
Definition rotate8_raw right r a := rotate8_scalar_value right (Int.zero_ext 8 r) (rotate8_amount a).
Definition rotate8_payload right r a := Int.zero_ext 8 (rotate8_raw right r a).
Definition rotate8_scalar_amount (right : bool) a := if right then rotate8_reverse_amount a else a.
Definition rotate8_scalar_count_expr (right : bool) :=
  if right then rotate8_reverse_amount_expr else Etempvar _amt tuchar.
Definition rotate8_scalar_call right := Scall (Some _t'3)
  (Evar _rotate_8 (Tfunction (Tcons tuchar (Tcons tuchar Tnil)) tuchar cc_default))
  [Etempvar _input tuchar; rotate8_scalar_count_expr right].
Lemma rotate8_helper_symbol : Genv.find_symbol (Clight.genv_genv ge0) _rotate_8 =
  Some (jet_symbol_block _rotate_8).
Proof. vm_compute; reflexivity. Qed.
Lemma rotate8_helper_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _rotate_8) Ptrofs.zero) = Some (Internal f_rotate_8).
Proof. vm_compute; reflexivity. Qed.
Lemma zero_ext8_unsigned_range r : 0 <= Int.unsigned (Int.zero_ext 8 r) < 256.
Proof.
  rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  change (0 <= Int.unsigned r mod 256 < 256); apply Z.mod_pos_bound; lia.
Qed.
Lemma exec_rotate8_scalar_call right bl le m r a :
  0 <= Int.unsigned r < 256 -> 0 <= Int.unsigned a < 8 ->
  le!_input = Some (Vint r) -> le!_amt = Some (Vint a) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (rotate8_scalar_call right)
    E0 (PTree.set _t'3 (Vint (rotate8_scalar_value right r a)) le) m Out_normal.
Proof.
  intros HR HA HI HM.
  assert (HB : 0 <= Int.unsigned (rotate8_scalar_amount right a) < 8).
  { destruct right; [unfold rotate8_scalar_amount, rotate8_reverse_amount; apply rotate8_amount_bounds|exact HA]. }
  assert (HE : eval_expr ge0 (e_one8 bl) le m (rotate8_scalar_count_expr right)
      (Vint (rotate8_scalar_amount right a))).
  { destruct right; [exact (@eval_rotate8_reverse_amount (e_one8 bl) le m a HA HM)|apply eval_Etempvar; exact HM]. }
  eapply exec_Scall with (vf := Vptr (jet_symbol_block _rotate_8) Ptrofs.zero)
    (vargs := [Vint r; Vint (rotate8_scalar_amount right a)]) (f := Internal f_rotate_8)
    (vres := Vint (rotate8_scalar_value right r a)).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply rotate8_helper_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HI.
    + change (Some (Vint (Int.zero_ext 8 r)) = Some (Vint r)).
      rewrite byte_carrier_cast_id by exact HR; reflexivity.
    + eapply eval_Econs.
      * exact HE.
      * assert (HT : typeof (rotate8_scalar_count_expr right) = tuchar) by (destruct right; reflexivity).
        rewrite HT. change (Some (Vint (Int.zero_ext 8 (rotate8_scalar_amount right a))) =
          Some (Vint (rotate8_scalar_amount right a))).
        rewrite byte_carrier_cast_id by lia; reflexivity.
      * apply eval_Enil.
  - apply rotate8_helper_funct.
  - reflexivity.
  - change (Clight2.eval_funcall ge0 m (Internal f_rotate_8)
      [Vint r; Vint (rotate8_scalar_amount right a)] E0 m
      (Vint (rotate8_result r (rotate8_scalar_amount right a)))).
    apply eval_rotate8_helper; assumption.
Qed.

Lemma rotate8_body right : (rotate8_function right).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (nibble_read _t'1) (Sset _amt
        (rotate8_amount_expr (Etempvar _t'1 tuchar))))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _input (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence
          (Ssequence (rotate8_scalar_call right)
            (frame_writer_call _simplicity_write8 tuchar tvoid (Etempvar _t'3 tuchar)))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct right; reflexivity. Qed.

Theorem eval_rotate8_composes env right m ma mc mr mr2 me mf bl bd dbase bs sbase bytes a r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read4) [Vptr bl Ptrofs.zero] E0 mr (Vint a) ->
  0 <= Int.unsigned a < 256 ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8)
    [Vptr bl Ptrofs.zero] E0 mr2 (Vint r) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (rotate8_payload right r a)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (rotate8_function right))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread4 Hamount Hread HW HF.
  set (le := le_arith8_layout env (rotate8_function right)
    bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase)).
  set (countle := PTree.set _amt (Vint (rotate8_amount a))
    (PTree.set _t'1 (Vint a) le)).
  set (inputle := PTree.set _input (Vint (Int.zero_ext 8 r)) (PTree.set _t'2 (Vint r) countle)).
  set (outputle := PTree.set _t'3 (Vint (rotate8_raw right r a)) inputle).
  eapply eval_funcall_internal with (e := e_one8 bl) (le1 := le) (le2 := outputle)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct right; reflexivity|destruct right; reflexivity| |exact HA].
    destruct right.
    all: change (list_disjoint [_dst; _src; _env] [_amt; _input; _t'3; _t'2; _t'1]).
    all: intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|H2]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite rotate8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_frame_jet_copy; eauto.
      unfold le, le_arith8_layout; rewrite PTree.gso by discriminate; apply PTree.gss.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := countle).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_nibble_read; exact Hread4.
        -- apply exec_set. apply eval_rotate8_amount;
             [left; reflexivity|apply eval_Etempvar; apply PTree.gss|exact Hamount].
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := inputle).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
           ++ apply call_binary8_read; exact Hread.
           ++ apply exec_set. eapply eval_Ecast with (v1 := Vint r).
              ** apply eval_Etempvar; apply PTree.gss.
              ** reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := outputle).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2) (le1 := outputle).
              ** apply exec_rotate8_scalar_call.
                 --- apply zero_ext8_unsigned_range.
                 --- apply rotate8_amount_bounds.
                 --- unfold inputle; apply PTree.gss.
                 --- unfold inputle, countle. repeat rewrite PTree.gso by discriminate; apply PTree.gss.
              ** eapply call_frame_writer_cast with (f := f_simplicity_write8)
                   (vraw := Vint (rotate8_raw right r a)) (v := Vint (rotate8_payload right r a))
                   (vret := Vundef).
                 --- destruct right; reflexivity.
                 --- unfold outputle, inputle, countle, le, le_arith8_layout.
                     repeat rewrite PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
                 --- destruct right; reflexivity.
                 --- apply symbol_write8.
                 --- apply funct_write8.
                 --- apply eval_Etempvar. unfold outputle; apply PTree.gss.
                 --- reflexivity.
                 --- exact HW.
           ++ apply exec_Sreturn_some; constructor.
  - destruct right; cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
