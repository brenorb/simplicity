(** Byte and/or/xor: actual promotions, truncation and complete C calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_wide.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8 C.jet_increment8_exec.
Require Import C.jet_add8_word C.jet_word_repr C.jet_binary_spec C.jet_binary_wide_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition binary8 k := match k with BAnd => f_simplicity_and_8 | BOr => f_simplicity_or_8 | BXor => f_simplicity_xor_8 end.
Definition binary8_raw k r t := binary_int k (Int.zero_ext 8 r) (Int.zero_ext 8 t).
Definition binary8_payload k r t := Int.zero_ext 8 (binary8_raw k r t).
Definition binary8_expr k := Ebinop (binary_clight_op k) (Etempvar _x tuchar) (Etempvar _y tuchar) tint.
Definition binary8_read result := Scall (Some result)
  (Evar _simplicity_read8 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tuchar cc_default))
  [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))].
Definition le_binary8_x env k bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (binary8 k) bd dofs bs sofs)).
Definition le_binary8_y env k bd dofs bs sofs r t :=
  PTree.set _y (Vint (Int.zero_ext 8 t)) (PTree.set _t'2 (Vint t) (le_binary8_x env k bd dofs bs sofs r)).

Lemma binary8_decode k w z :
  decode_word8 (Int64.repr (Int.unsigned (binary8_payload k (jet_read8.read8_result w) (jet_read8.read8_result z)))) =
    @binary_word_spec 3 k Alg.CoreFunSem (decode_word8 w, decode_word8 z).
Proof.
  unfold decode_word8 at 1. rewrite Int64.unsigned_repr by
    (pose proof (Int.unsigned_range_2 (binary8_payload k (jet_read8.read8_result w) (jet_read8.read8_result z)));
     change Int.max_unsigned with 4294967295 in *;
     change Int64.max_unsigned with 18446744073709551615; lia).
  unfold binary8_payload. rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  change (@fromZ (WordToZ 3) (Int.unsigned (binary8_raw k (jet_read8.read8_result w) (jet_read8.read8_result z)) mod 256) =
    @binary_word_spec 3 k Alg.CoreFunSem (decode_word8 w, decode_word8 z)).
  rewrite (word_fromZ_mod 3). unfold binary8_raw.
  apply binary_int_denotes; [change (8 <= 32); lia|apply read8_result_unsigned|apply read8_result_unsigned].
Qed.

Lemma binary8_body k : (binary8 k).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid (binary8_expr k))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. destruct k; reflexivity. Qed.

Lemma call_binary8_read result le m mr bl r :
  Clight2.eval_funcall ge0 m (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.exec_stmt ge0 (e_one8 bl) le m (binary8_read result)
    E0 (PTree.set result (Vint r) le) mr Out_normal.
Proof.
  intros Hread. eapply exec_Scall with (vf := Vptr block_read8 Ptrofs.zero)
    (vargs := [Vptr bl Ptrofs.zero]) (f := Internal f_simplicity_read8) (vres := Vint r).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|apply symbol_read8].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + eapply eval_Eaddrof. eapply eval_Evar_local; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply funct_read8.
  - reflexivity.
  - exact Hread.
Qed.

Lemma eval_binary8_expr k e le m r t :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  eval_expr ge0 e le m (binary8_expr k) (Vint (binary8_raw k r t)).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vint (Int.zero_ext 8 r)) (v2 := Vint (Int.zero_ext 8 t)).
  - eapply eval_Etempvar; exact HX.
  - eapply eval_Etempvar; exact HY.
  - destruct k; reflexivity.
Qed.

Lemma eval_binary8_composes env k m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (binary8_payload k r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (binary8 k))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (binary8 k) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_binary8_y env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k; reflexivity|destruct k; reflexivity| |exact HA].
    destruct k; change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite binary8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_binary8_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast.
           ++ eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (binary8_raw k r t)) (v := Vint (binary8_payload k r t)) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le_binary8_y, le_binary8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ apply eval_binary8_expr.
              ** unfold le_binary8_y, le_binary8_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_binary8_y. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k; cbn; split; solve [discriminate|reflexivity].
  - destruct k; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
