(** Actual multiply_8: unsigned byte-to-long casts, doubled-width writer,
    return and local cleanup. INTERNAL composition premises are discharged
    by the initial-only frame contract in jet_multiply8_layout.v. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_wide.
Require Import C.jet_read8.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8 C.jet_increment8_exec.
Require Import C.jet_wide_spec C.jet_add8 C.jet_add8_word C.jet_word_repr C.jet_binary8_exec C.jet_multiply_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition multiply8_arg r := Int64.repr (Int.unsigned r).
Definition multiply8_payload r t := Int64.mul (multiply8_arg r) (multiply8_arg t).
Definition multiply8_expr := Ebinop Omul (Etempvar _x tulong) (Etempvar _y tulong) tulong.
Definition le_multiply8_x env bd dofs bs sofs r :=
  PTree.set _x (Vlong (multiply8_arg r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env f_simplicity_multiply_8 bd dofs bs sofs)).
Definition le_multiply8_y env bd dofs bs sofs r t :=
  PTree.set _y (Vlong (multiply8_arg t)) (PTree.set _t'2 (Vint t)
    (le_multiply8_x env bd dofs bs sofs r)).

Lemma multiply8_arg_unsigned w :
  Int64.unsigned (multiply8_arg (read8_result w)) =
    @toZ (WordToZ 3) (decode_word8 w).
Proof.
  assert (Hz : Int.zero_ext 8 (read8_result w) = read8_result w).
  { unfold read8_result. rewrite Int.or_commut, Int.or_zero.
    rewrite Int.zero_ext_idem by lia. reflexivity. }
  pose proof (read8_result_unsigned w) as HR.
  unfold add8_u in HR. rewrite Hz in HR.
  unfold multiply8_arg. rewrite Int64.unsigned_repr; [exact HR|].
  pose proof (Int.unsigned_range_2 (read8_result w)).
  change Int.max_unsigned with 4294967295 in *.
  change Int64.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma multiply8_decode w z :
  decode_wide W16 (Int64.zero_ext 16 (multiply8_payload (read8_result w) (read8_result z))) =
    @multiply_word_spec 3 Alg.CoreFunSem (decode_word8 w, decode_word8 z).
Proof.
  unfold decode_wide. rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
  change (@fromZ (WordToZ 4)
    (Int64.unsigned (multiply8_payload (read8_result w) (read8_result z)) mod 65536) =
    @multiply_word_spec 3 Alg.CoreFunSem (decode_word8 w, decode_word8 z)).
  rewrite (word_fromZ_mod 4). apply multiply_int64_denotes.
  - change (16 <= 64); lia.
  - apply multiply8_arg_unsigned.
  - apply multiply8_arg_unsigned.
Qed.

Lemma multiply8_body : f_simplicity_multiply_8.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tulong)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tulong)))
        (Ssequence (frame_writer_call _simplicity_write16 tulong tvoid (multiply8_expr))
          (Sreturn (Some (Econst_int Int.one tint)))))).
Proof. reflexivity. Qed.

Lemma eval_multiply8_expr e le m r t :
  le!_x = Some (Vlong (multiply8_arg r)) -> le!_y = Some (Vlong (multiply8_arg t)) ->
  eval_expr ge0 e le m (multiply8_expr) (Vlong (multiply8_payload r t)).
Proof.
  intros HX HY. eapply eval_Ebinop with (v1 := Vlong (multiply8_arg r)) (v2 := Vlong (multiply8_arg t)).
  - eapply eval_Etempvar; exact HX.
  - eapply eval_Etempvar; exact HY.
  - reflexivity.
Qed.

Lemma eval_multiply8_composes env m ma mc mr mr2 me mf bl bd dbase bs sbase bytes r t :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_write16)
    [Vptr bd (Ptrofs.repr dbase); Vlong (multiply8_payload r t)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_multiply_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_multiply_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_multiply8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|[H2|[H2|H2]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite multiply8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_multiply8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
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
        -- eapply call_frame_writer_cast with (f := wide_writer W16)
             (vraw := Vlong (multiply8_payload r t)) (v := Vlong (multiply8_payload r t)) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le_multiply8_y, le_multiply8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply (wide_writer_symbol W16).
           ++ apply (wide_writer_funct W16).
           ++ apply eval_multiply8_expr.
              ** unfold le_multiply8_y, le_multiply8_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_multiply8_y. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
