(** Actual full_multiply_8: four unsigned byte-to-long casts, shared long
    expression, doubled-width write and cleanup. INTERNAL call composition. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_frame_layout.
Require Import C.jet_arith8_layout_exec C.jet_wide C.jet_binary_wide_exec.
Require Import C.jet_multiply_wide_exec C.jet_full_multiply_word C.jet_full_multiply_wide_exec.
Require Import C.jet_multiply8_exec C.jet_binary8_exec C.jet_spec C.jet_wide_spec C.jet_read8.
Require Import C.jet_word_repr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition full_multiply8_payload r t u v :=
  full_multiply_value (multiply8_arg r) (multiply8_arg t) (multiply8_arg u) (multiply8_arg v).
Definition le_full_multiply8_x env bd dofs bs sofs r :=
  PTree.set _x (Vlong (multiply8_arg r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env f_simplicity_full_multiply_8 bd dofs bs sofs)).
Definition le_full_multiply8_y env bd dofs bs sofs r t :=
  PTree.set _y (Vlong (multiply8_arg t)) (PTree.set _t'2 (Vint t)
    (le_full_multiply8_x env bd dofs bs sofs r)).
Definition le_full_multiply8_z env bd dofs bs sofs r t u :=
  PTree.set _z (Vlong (multiply8_arg u)) (PTree.set _t'3 (Vint u)
    (le_full_multiply8_y env bd dofs bs sofs r t)).
Definition le_full_multiply8_w env bd dofs bs sofs r t u v :=
  PTree.set _w (Vlong (multiply8_arg v)) (PTree.set _t'4 (Vint v)
    (le_full_multiply8_z env bd dofs bs sofs r t u)).

Lemma full_multiply8_decode a b c d :
  decode_wide W16 (Int64.zero_ext 16
    (full_multiply8_payload (read8_result a) (read8_result b) (read8_result c) (read8_result d))) =
    @fullMultiplier 3 Alg.CoreFunSem
      ((decode_word8 a, decode_word8 b), (decode_word8 c, decode_word8 d)).
Proof.
  unfold decode_wide. rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
  change (@fromZ (WordToZ 4)
    (Int64.unsigned (full_multiply8_payload (read8_result a) (read8_result b)
      (read8_result c) (read8_result d)) mod 65536) =
    @fullMultiplier 3 Alg.CoreFunSem
      ((decode_word8 a, decode_word8 b), (decode_word8 c, decode_word8 d))).
  rewrite (word_fromZ_mod 4). apply full_multiply_int64_denotes.
  - change (16 <= 64); lia.
  - apply multiply8_arg_unsigned.
  - apply multiply8_arg_unsigned.
  - apply multiply8_arg_unsigned.
  - apply multiply8_arg_unsigned.
Qed.

Lemma full_multiply8_body : f_simplicity_full_multiply_8.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tulong)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tulong)))
        (Ssequence
          (Ssequence (binary8_read _t'3) (Sset _z (Ecast (Etempvar _t'3 tuchar) tulong)))
          (Ssequence
            (Ssequence (binary8_read _t'4) (Sset _w (Ecast (Etempvar _t'4 tuchar) tulong)))
            (Ssequence (frame_writer_call (_simplicity_write16) tulong tvoid full_multiply_expr)
              (Sreturn (Some (Econst_int Int.one tint)))))))).
Proof. reflexivity. Qed.

Lemma eval_full_multiply8_composes env m ma mc mr mr2 mr3 mr4 me mf bl bd dbase bs sbase bytes r t u v :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr3 (Vint u) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr4 (Vint v) ->
  Clight2.eval_funcall ge0 mr4 (Internal f_simplicity_write16)
    [Vptr bd (Ptrofs.repr dbase); Vlong (full_multiply8_payload r t u v)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_full_multiply_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hread4 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_full_multiply_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_full_multiply8_w env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u v)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _y; _z; _w; _t'4; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      destruct H1 as [H1|[H1|[H1|H1]]];
      destruct H2 as [H2|[H2|[H2|[H2|[H2|[H2|[H2|[H2|H2]]]]]]]];
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite full_multiply8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_full_multiply8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        - apply call_binary8_read; exact Hread1.
        - apply exec_set. eapply eval_Ecast.
          + apply eval_Etempvar. rewrite PTree.gss; reflexivity.
          + reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
        (le1 := le_full_multiply8_y env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
        - apply call_binary8_read; exact Hread2.
        - apply exec_set. eapply eval_Ecast.
          + apply eval_Etempvar. rewrite PTree.gss; reflexivity.
          + reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3)
        (le1 := le_full_multiply8_z env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
        - apply call_binary8_read; exact Hread3.
        - apply exec_set. eapply eval_Ecast.
          + apply eval_Etempvar. rewrite PTree.gss; reflexivity.
          + reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr4)
        (le1 := le_full_multiply8_w env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u v).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr4).
        - apply call_binary8_read; exact Hread4.
        - apply exec_set. eapply eval_Ecast.
          + apply eval_Etempvar. rewrite PTree.gss; reflexivity.
          + reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
      * eapply call_frame_writer_cast with (f := wide_writer W16)
          (vraw := Vlong (full_multiply8_payload r t u v)) (v := Vlong (full_multiply8_payload r t u v)) (vret := Vundef).
        -- reflexivity.
        -- unfold le_full_multiply8_w, le_full_multiply8_z, le_full_multiply8_y,
             le_full_multiply8_x, le_arith8_layout.
           rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
        -- reflexivity.
        -- apply (wide_writer_symbol W16).
        -- apply (wide_writer_funct W16).
        -- apply eval_full_multiply_expr;
             unfold le_full_multiply8_w, le_full_multiply8_z, le_full_multiply8_y,
               le_full_multiply8_x;
             rewrite ?PTree.gso by discriminate; rewrite PTree.gss; reflexivity.
        -- reflexivity.
        -- exact Hwrite.
      * apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
