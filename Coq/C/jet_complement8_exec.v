(** The byte jet's promotions and casts, and its complete function boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Word C.jets C.jet_exec C.jet_one8 C.jet_spec C.jet_wide.
Require Import C.jet_frame_layout C.jet_arith8_layout_exec C.jet_increment8 C.jet_increment8_exec.
Require Import C.jet_add8 C.jet_add8_word C.jet_word_repr C.jet_complement_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition complement8_payload r := Int.zero_ext 8 (Int.not (Int.zero_ext 8 r)).
Definition complement8_expr :=
  Eunop Onotint (Ebinop Omul (Econst_int Int.one tuint) (Etempvar _x tuchar) tuint) tuint.
Definition le_complement8_x env bd dofs bs sofs r :=
  PTree.set _x (Vint (Int.zero_ext 8 r)) (PTree.set _t'1 (Vint r)
    (le_arith8_layout env f_simplicity_complement_8 bd dofs bs sofs)).

Lemma complement8_decode w :
  decode_word8 (Int64.repr (Int.unsigned (complement8_payload (jet_read8.read8_result w)))) =
    @complement_spec 3 Alg.CoreFunSem (decode_word8 w).
Proof.
  unfold decode_word8 at 1. rewrite Int64.unsigned_repr by
    (pose proof (Int.unsigned_range_2 (complement8_payload (jet_read8.read8_result w)));
     change Int.max_unsigned with 4294967295 in *;
     change Int64.max_unsigned with 18446744073709551615; lia).
  unfold complement8_payload. rewrite Int.zero_ext_mod by (change (0 <= 8 < 32); lia).
  change (@fromZ (WordToZ 3)
    (Int.unsigned (Int.not (Int.zero_ext 8 (jet_read8.read8_result w))) mod 256) =
    @complement_spec 3 Alg.CoreFunSem (decode_word8 w)).
  rewrite (word_fromZ_mod 3).
  apply complement_int_denotes; [change (8 <= 32); lia|].
  exact (read8_result_unsigned w).
Qed.

Lemma eval_complement8_expr m e le r :
  le!_x = Some (Vint (Int.zero_ext 8 r)) ->
  eval_expr ge0 e le m complement8_expr (Vint (Int.not (Int.zero_ext 8 r))).
Proof.
  intros HX. unfold complement8_expr. eapply eval_Eunop with (v1 := Vint (Int.zero_ext 8 r)).
  - eapply eval_Ebinop with (v1 := Vint Int.one) (v2 := Vint (Int.zero_ext 8 r)).
    + apply eval_Econst_int.
    + eapply eval_Etempvar; exact HX.
    + change (Some (Vint (Int.mul Int.one (Int.zero_ext 8 r))) = Some (Vint (Int.zero_ext 8 r))).
      rewrite Int.mul_commut, Int.mul_one. reflexivity.
  - reflexivity.
Qed.

Lemma eval_complement8_composes env m ma mc mr me mf bl bd dbase bs sbase bytes r :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma, bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Clight2.eval_funcall ge0 mc (Internal f_simplicity_read8) [Vptr bl Ptrofs.zero] E0 mr (Vint r) ->
  Clight2.eval_funcall ge0 mr (Internal f_simplicity_write8)
    [Vptr bd (Ptrofs.repr dbase); Vint (complement8_payload r)] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_complement_8)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HB HS HD HA Hbytes SC Hread Hwrite HF.
  eapply ClightBigstep.eval_funcall_internal with (e := e_one8 bl)
    (le1 := le_arith8_layout env f_simplicity_complement_8 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase))
    (le2 := le_complement8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply entry_frame_jet; [reflexivity|reflexivity| |exact HA].
    change (list_disjoint [_dst; _src; _env] [_x; _t'1]).
    intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    destruct H1 as [H1|[H1|[H1|H1]]]; destruct H2 as [H2|[H2|H2]];
      try contradiction; vm_compute in H1, H2; congruence.
  - unfold f_simplicity_complement_8; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_frame_jet_copy; eauto; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr)
        (le1 := le_complement8_x env bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase) r).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr).
        -- eapply call_increment8_read; [apply symbol_read8|apply funct_read8|exact Hread].
        -- apply exec_set. eapply eval_Ecast.
           ++ eapply eval_Etempvar; reflexivity.
           ++ reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me).
        -- eapply call_frame_writer_cast with (f := f_simplicity_write8)
             (vraw := Vint (Int.not (Int.zero_ext 8 r)))
             (v := Vint (complement8_payload r)) (vret := Vundef).
           ++ reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ apply symbol_write8.
           ++ apply funct_write8.
           ++ apply eval_complement8_expr. reflexivity.
           ++ reflexivity.
           ++ exact Hwrite.
        -- apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl, 0, 16)] = Some mf). cbn; rewrite HF; reflexivity.
Qed.
