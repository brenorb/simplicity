(** Actual byte maj/xor_xor/ch promotions, casts and complete calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8_exec.
Require Import C.jet_add8_word C.jet_word_repr C.jet_binary_spec C.jet_binary_wide_exec C.jet_binary8_exec C.jet_ternary_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition ternary8 k := match k with TMaj => f_simplicity_maj_8 | TXorXor => f_simplicity_xor_xor_8 | TCh => f_simplicity_ch_8 end.
Definition ternary8_raw k r t u := ternary_int k (Int.zero_ext 8 r) (Int.zero_ext 8 t) (Int.zero_ext 8 u).
Definition ternary8_payload k r t u := Int.zero_ext 8 (ternary8_raw k r t u).
Definition int_bin k ty a b := Ebinop (binary_clight_op k) a b ty.
Definition ternary8_expr k := match k with
  | TMaj => int_bin BOr tint (int_bin BOr tint
      (int_bin BAnd tint (Etempvar _x tuchar) (Etempvar _y tuchar))
      (int_bin BAnd tint (Etempvar _y tuchar) (Etempvar _z tuchar)))
      (int_bin BAnd tint (Etempvar _z tuchar) (Etempvar _x tuchar))
  | TXorXor => int_bin BXor tint (int_bin BXor tint (Etempvar _x tuchar) (Etempvar _y tuchar)) (Etempvar _z tuchar)
  | TCh => int_bin BOr tuint (int_bin BAnd tint (Etempvar _x tuchar) (Etempvar _y tuchar))
      (int_bin BAnd tuint (Eunop Onotint
        (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tuchar) tuint) tuint) (Etempvar _z tuchar))
  end.
Definition le_ternary8_x env k bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env (ternary8 k) bd dofs bs sofs)).
Definition le_ternary8_y env k bd dofs bs sofs r t :=
  PTree.set _y (Vint (Int.zero_ext 8 t)) (PTree.set _t'2 (Vint t) (le_ternary8_x env k bd dofs bs sofs r)).
Definition le_ternary8_z env k bd dofs bs sofs r t u :=
  PTree.set _z (Vint (Int.zero_ext 8 u)) (PTree.set _t'3 (Vint u) (le_ternary8_y env k bd dofs bs sofs r t)).

Lemma ternary8_decode k w z v :
  decode_word8 (Int64.repr (Int.unsigned (ternary8_payload k
    (jet_read8.read8_result w) (jet_read8.read8_result z) (jet_read8.read8_result v)))) =
    @ternary_word_spec 3 k Alg.CoreFunSem (decode_word8 w, (decode_word8 z, decode_word8 v)).
Proof.
  unfold decode_word8 at 1. rewrite Int64.unsigned_repr by
    (pose proof (Int.unsigned_range_2 (ternary8_payload k
      (jet_read8.read8_result w) (jet_read8.read8_result z) (jet_read8.read8_result v)));
     change Int.max_unsigned with 4294967295 in *;
     change Int64.max_unsigned with 18446744073709551615; lia).
  unfold ternary8_payload. rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  change (@fromZ (WordToZ 3) (Int.unsigned (ternary8_raw k
    (jet_read8.read8_result w) (jet_read8.read8_result z) (jet_read8.read8_result v)) mod 256) =
    @ternary_word_spec 3 k Alg.CoreFunSem (decode_word8 w, (decode_word8 z, decode_word8 v))).
  rewrite (word_fromZ_mod 3). unfold ternary8_raw.
  apply ternary_int_denotes; [change (8 <= 32); lia| | |]; apply read8_result_unsigned.
Qed.

Lemma ternary8_body k : (ternary8 k).(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (binary8_read _t'1) (Sset _x (Ecast (Etempvar _t'1 tuchar) tuchar)))
      (Ssequence
        (Ssequence (binary8_read _t'2) (Sset _y (Ecast (Etempvar _t'2 tuchar) tuchar)))
        (Ssequence
          (Ssequence (binary8_read _t'3) (Sset _z (Ecast (Etempvar _t'3 tuchar) tuchar)))
          (Ssequence (frame_writer_call _simplicity_write8 tuchar tvoid (ternary8_expr k))
            (Sreturn (Some (Econst_int Int.one tint))))))).
Proof. destruct k; reflexivity. Qed.

Lemma eval_int_bin k ty e le m a b r t :
  In (typeof a) [tbool; tuchar; tint; tuint] -> In (typeof b) [tbool; tuchar; tint; tuint] ->
  eval_expr ge0 e le m a (Vint r) -> eval_expr ge0 e le m b (Vint t) ->
  eval_expr ge0 e le m (int_bin k ty a b) (Vint (binary_int k r t)).
Proof.
  intros HA HB HX HY. eapply eval_Ebinop; [exact HX|exact HY|].
  cbn in HA, HB. destruct HA as [HA|[HA|[HA|[HA|HA]]]];
    destruct HB as [HB|[HB|[HB|[HB|HB]]]]; try contradiction;
    rewrite <- HA, <- HB; destruct k; reflexivity.
Qed.

Lemma eval_ternary8_expr k e le m r t u :
  le!_x = Some (Vint (Int.zero_ext 8 r)) -> le!_y = Some (Vint (Int.zero_ext 8 t)) ->
  le!_z = Some (Vint (Int.zero_ext 8 u)) ->
  eval_expr ge0 e le m (ternary8_expr k) (Vint (ternary8_raw k r t u)).
Proof.
  intros HX HY HZ. destruct k; cbn [ternary8_expr ternary8_raw ternary_int].
  - apply (eval_int_bin BOr); try (solve [cbn; auto]).
    + apply (eval_int_bin BOr); try (solve [cbn; auto]);
        apply (eval_int_bin BAnd); try (solve [cbn; auto]); apply eval_Etempvar; assumption.
    + apply (eval_int_bin BAnd); try (solve [cbn; auto]); apply eval_Etempvar; assumption.
  - apply (eval_int_bin BXor); try (solve [cbn; auto]).
    + apply (eval_int_bin BXor); try (solve [cbn; auto]); apply eval_Etempvar; assumption.
    + apply eval_Etempvar; exact HZ.
  - apply (eval_int_bin BOr); try (solve [cbn; auto]).
    + apply (eval_int_bin BAnd); try (solve [cbn; auto]); apply eval_Etempvar; assumption.
    + apply (eval_int_bin BAnd); try (solve [cbn; auto]).
      * eapply eval_Eunop with (v1 := Vint (Int.mul Int.one (Int.zero_ext 8 r))).
        -- eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint (Int.zero_ext 8 r)).
           ++ apply eval_Econst_int.
           ++ apply eval_Etempvar; exact HX.
           ++ reflexivity.
        -- reflexivity.
      * apply eval_Etempvar; exact HZ.
Qed.

Lemma eval_ternary8_composes env k m ma mc mr mr2 mr3 me mf bl bd dbase bs sbase bytes r t u :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr2 (Vint t) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr3 (Vint u) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (ternary8_payload k r t u)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal (ternary8 k))
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread1 Hread2 Hread3 Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env (ternary8 k) bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_ternary8_z env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t u)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [destruct k; reflexivity|destruct k; reflexivity| |exact HA].
    destruct k; change (list_disjoint [_dst; _src; _env] [_x; _y; _z; _t'3; _t'2; _t'1]);
      intros id1 id2 H1 H2 Heq; cbn in H1, H2; subst id2;
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end;
      try contradiction; vm_compute in H1, H2; congruence.
  - rewrite ternary8_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto. destruct k; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_ternary8_x env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_binary8_read. exact Hread1.
        -- apply exec_set. eapply eval_Ecast.
           ++ eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2)
          (le1 := le_ternary8_y env k bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r t).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
          - apply call_binary8_read. exact Hread2.
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
          - apply call_binary8_read. exact Hread3.
          - apply exec_set. eapply eval_Ecast.
            + eapply eval_Etempvar. rewrite PTree.gss. reflexivity.
            + reflexivity. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (ternary8_raw k r t u)) (v := Vint (ternary8_payload k r t u)) (vret := Vundef).
           ++ reflexivity.
           ++ unfold le_ternary8_z, le_ternary8_y, le_ternary8_x, le_arith8_layout.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ apply eval_ternary8_expr.
              ** unfold le_ternary8_z, le_ternary8_y, le_ternary8_x.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_ternary8_z, le_ternary8_y.
                 rewrite !PTree.gso by discriminate. rewrite PTree.gss. reflexivity.
              ** unfold le_ternary8_z. rewrite PTree.gss. reflexivity.
           ++ destruct k; reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - destruct k; cbn; split; solve [discriminate|reflexivity].
  - destruct k; change (Mem.free_list me [(bl, 0, 16)] = Some mf); cbn; rewrite HF; reflexivity.
Qed.
