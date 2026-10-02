(** Actual right_pad_low_1_8 promoted shift and both byte casts. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_complement1_exec C.jet_increment8_exec C.jet_spec C.jet_write8.
Require Import C.jet_word_decode C.jet_pad_bit_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition le_right_pad_bit8 env bd dofs bs sofs bit :=
  PTree.set _bit (Vint (bit_int bit)) (PTree.set _t'1 (Vint (bit_int bit))
    (le_arith8_layout env f_simplicity_right_pad_low_1_8 bd dofs bs sofs)).

Definition right_pad_bit8_arg bit := Int.shl (bit_int bit) (Int.repr 7).
Definition right_pad_bit8_expr :=
  Ecast (Ebinop Oshl (Ecast (Etempvar _bit tbool) tuchar)
    (Ebinop Osub (Econst_int (Int.repr 8) tint) (Econst_int Int.one tint) tint) tint) tuchar.
Lemma right_pad_bit8_guard : Int.ltu (Int.repr 7) Int.iwordsize = Datatypes.true.
Proof. reflexivity. Qed.
Lemma eval_right_pad_bit8_expr e le m bit :
  le!_bit = Some (Vint (bit_int bit)) ->
  eval_expr ge0 e le m right_pad_bit8_expr (Vint (right_pad_bit8_arg bit)).
Proof.
  intros HB. unfold right_pad_bit8_expr, right_pad_bit8_arg.
  eapply eval_Ecast with (v1 := Vint (Int.shl (bit_int bit) (Int.repr 7))).
  - eapply eval_Ebinop with (v1 := Vint (bit_int bit)) (v2 := Vint (Int.repr 7)).
    + eapply eval_Ecast with (v1 := Vint (bit_int bit)).
      * eapply eval_Etempvar; exact HB.
      * unfold bit_int; destruct bit; reflexivity.
    + eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
    + change ((if Int.ltu (Int.repr 7) Int.iwordsize
        then Some (Vint (Int.shl (bit_int bit) (Int.repr 7))) else None) =
        Some (Vint (Int.shl (bit_int bit) (Int.repr 7)))).
      rewrite right_pad_bit8_guard; reflexivity.
  - unfold bit_int; destruct bit; reflexivity.
Qed.

Lemma eval_right_pad_bit8_composes env m ma mc mr me mf bl bd dbase bs sbase bytes bit :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_readBit) [Vptr bl Ptrofs.zero] E0 mr (Vint (bit_int bit)) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (right_pad_bit8_arg bit)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_right_pad_low_1_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_right_pad_low_1_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_right_pad_bit8 env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_bit; _t'1]).
    intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - unfold f_simplicity_right_pad_low_1_8; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_right_pad_bit8 env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) bit).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- apply call_bit_jet_read. exact Hread.
        -- apply exec_set. eapply eval_Ecast with (v1 := Vint (bit_int bit)).
           ++ eapply eval_Etempvar; reflexivity.
           ++ unfold bit_int. destruct bit; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (right_pad_bit8_arg bit)) (v := Vint (right_pad_bit8_arg bit))
             (vret := Vundef).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ apply eval_right_pad_bit8_expr; reflexivity.
           ++ unfold right_pad_bit8_arg, bit_int; destruct bit; reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
