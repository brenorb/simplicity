(** Generated DivMod128_64 branch execution. Helper/writer premises here are
    composition rules, to be discharged by the initial-only public contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_writeBit C.jet_wide C.jet_one8.
Require Import C.jet_arith8_layout_exec C.jet_binary_wide_exec C.jet_readBit_layout.
Require Import C.jet_divmod128_entry C.jet_divmod128_spec C.jet_divmod128_expr.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod128_body_tail :=
  match f_simplicity_div_mod_128_64.(fn_body) with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ t)))) => t
  | _ => Sskip end.
Definition divmod128_valid_debug :=
  match divmod128_body_tail with
  | Ssequence (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence check _)) _)) _ => check
  | _ => Sskip end.
Definition divmod128_valid_stmt :=
  Ssequence (divmod128_helper_call _qh _ah _am)
    (Ssequence divmod128_valid_debug
      (Ssequence
        (Ssequence (Sset _t'9 (Evar _r tulong)) (divmod128_helper_call _ql _t'9 _al))
        (Ssequence
          (Ssequence (Sset _t'8 (Evar _qh tulong))
            (frame_writer_call _simplicity_write32 tulong tvoid (Etempvar _t'8 tulong)))
          (Ssequence
            (Ssequence (Sset _t'7 (Evar _ql tulong))
              (frame_writer_call _simplicity_write32 tulong tvoid (Etempvar _t'7 tulong)))
            (Ssequence (Sset _t'6 (Evar _r tulong))
              (frame_writer_call _simplicity_write64 tulong tvoid (Etempvar _t'6 tulong))))))).
Definition divmod128_invalid_expr := Ecast (Eunop Oneg (Econst_int Int.one tint) tint) tulong.
Definition divmod128_invalid_stmt :=
  Ssequence (frame_writer_call _simplicity_write64 tulong tvoid divmod128_invalid_expr)
    (frame_writer_call _simplicity_write64 tulong tvoid divmod128_invalid_expr).
Definition divmod128_branch_stmt :=
  Sifthenelse (Etempvar _t'5 tint) divmod128_valid_stmt divmod128_invalid_stmt.

Lemma divmod128_body : f_simplicity_div_mod_128_64.(fn_body) =
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence (wide_binary_read W64 _t'1) (Sset _ah (Etempvar _t'1 tulong)))
      (Ssequence
        (Ssequence (wide_binary_read W32 _t'2) (Sset _am (Etempvar _t'2 tulong)))
        (Ssequence
          (Ssequence (wide_binary_read W32 _t'3) (Sset _al (Etempvar _t'3 tulong)))
          (Ssequence
            (Ssequence (wide_binary_read W64 _t'4) (Sset _b (Etempvar _t'4 tulong)))
            (Ssequence (Ssequence divmod128_guard_stmt divmod128_branch_stmt)
              (Sreturn (Some (Econst_int Int.one tint)))))))).
Proof. reflexivity. Qed.

Definition divmod128_valid_env le r1 qh ql rf :=
  PTree.set _t'6 (Vlong rf) (PTree.set _t'7 (Vlong ql)
    (PTree.set _t'8 (Vlong qh) (PTree.set _t'9 (Vlong r1) le))).
Ltac divmod128_lookup :=
  repeat first [rewrite PTree.gss | rewrite PTree.gso by discriminate]; first [reflexivity | assumption].

Lemma exec_divmod128_valid_composes le m m1 m2 mw1 mw2 mf bl bqh bql br bd dbase ah am al b r1 qh ql rf :
  le!_ah = Some (Vlong ah) -> le!_am = Some (Vlong am) -> le!_al = Some (Vlong al) ->
  le!_b = Some (Vlong b) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall ge0 m (Internal f_div_mod_96_64)
    [Vptr bqh Ptrofs.zero; Vptr br Ptrofs.zero; Vlong ah; Vlong am; Vlong b] E0 m1 Vundef ->
  Mem.load Mint64 m1 br 0 = Some (Vlong r1) ->
  Clight2.eval_funcall ge0 m1 (Internal f_div_mod_96_64)
    [Vptr bql Ptrofs.zero; Vptr br Ptrofs.zero; Vlong r1; Vlong al; Vlong b] E0 m2 Vundef ->
  Mem.load Mint64 m2 bqh 0 = Some (Vlong qh) ->
  Clight2.eval_funcall ge0 m2 (Internal f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong qh] E0 mw1 Vundef ->
  Mem.load Mint64 mw1 bql 0 = Some (Vlong ql) ->
  Clight2.eval_funcall ge0 mw1 (Internal f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong ql] E0 mw2 Vundef ->
  Mem.load Mint64 mw2 br 0 = Some (Vlong rf) ->
  Clight2.eval_funcall ge0 mw2 (Internal f_simplicity_write64)
    [Vptr bd (Ptrofs.repr dbase); Vlong rf] E0 mf Vundef ->
  Clight2.exec_stmt ge0 (divmod128_env bl bqh bql br) le m divmod128_valid_stmt E0
    (divmod128_valid_env le r1 qh ql rf) mf Out_normal.
Proof.
  intros HA HAM HAL HB HD HC1 HR1 HC2 HQH HW1 HQL HW2 HRF HW3.
  unfold divmod128_valid_stmt.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
  - eapply call_divmod128_helper; try eassumption; reflexivity.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
    + apply exec_writeBit_debug_loop.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2)
        (le1 := PTree.set _t'9 (Vlong r1) le).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1)
          (le1 := PTree.set _t'9 (Vlong r1) le).
        -- apply exec_set. eapply eval_divmod128_local; [reflexivity|exact HR1].
        -- eapply call_divmod128_helper; try reflexivity; try exact HC2; divmod128_lookup.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw1)
          (le1 := PTree.set _t'8 (Vlong qh) (PTree.set _t'9 (Vlong r1) le)).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m2)
             (le1 := PTree.set _t'8 (Vlong qh) (PTree.set _t'9 (Vlong r1) le)).
           ++ apply exec_set. eapply eval_divmod128_local; [reflexivity|exact HQH].
           ++ eapply call_frame_writer with (bd := bd) (dofs := Ptrofs.repr dbase)
                (f := f_simplicity_write32) (b := jet_symbol_block _simplicity_write32)
                (v := Vlong qh) (vret := Vundef); try reflexivity.
              ** divmod128_lookup.
              ** apply eval_Etempvar. divmod128_lookup.
              ** exact HW1.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw2)
             (le1 := PTree.set _t'7 (Vlong ql) (PTree.set _t'8 (Vlong qh) (PTree.set _t'9 (Vlong r1) le))).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw1)
                (le1 := PTree.set _t'7 (Vlong ql) (PTree.set _t'8 (Vlong qh) (PTree.set _t'9 (Vlong r1) le))).
              ** apply exec_set. eapply eval_divmod128_local; [reflexivity|exact HQL].
              ** eapply call_frame_writer with (bd := bd) (dofs := Ptrofs.repr dbase)
                   (f := f_simplicity_write32) (b := jet_symbol_block _simplicity_write32)
                   (v := Vlong ql) (vret := Vundef); try reflexivity.
                 --- divmod128_lookup.
                 --- apply eval_Etempvar. divmod128_lookup.
                 --- exact HW2.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw2)
                (le1 := divmod128_valid_env le r1 qh ql rf).
              ** apply exec_set. eapply eval_divmod128_local; [reflexivity|exact HRF].
              ** eapply call_frame_writer with (bd := bd) (dofs := Ptrofs.repr dbase)
                   (f := f_simplicity_write64) (b := jet_symbol_block _simplicity_write64)
                   (v := Vlong rf) (vret := Vundef); try reflexivity.
                 --- unfold divmod128_valid_env. divmod128_lookup.
                 --- apply eval_Etempvar. unfold divmod128_valid_env. divmod128_lookup.
                 --- exact HW3.
Qed.

Definition divmod128_read_set le id tmp w :=
  PTree.set id (Vlong w) (PTree.set tmp (Vlong w) le).
Definition divmod128_read_env le ah am al b :=
  divmod128_read_set
    (divmod128_read_set (divmod128_read_set (divmod128_read_set le _ah _t'1 ah) _am _t'2 am)
      _al _t'3 al) _b _t'4 b.

Lemma eval_divmod128_composes env m ma mb mc md mcopy mr1 mr2 mr3 mr4 me mf
    bl bqh bql br bd dbase bs sbase bytes ah am al b lef :
  C.jet_frame_layout.frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 8 = (mb,bqh) ->
  Mem.alloc mb 0 8 = (mc,bql) -> Mem.alloc mc 0 8 = (md,br) ->
  Mem.loadbytes md bs sbase 16 = Some bytes -> Mem.storebytes md bl 0 bytes = Some mcopy ->
  Clight2.eval_funcall ge0 mcopy (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr1 (Vlong ah) ->
  Clight2.eval_funcall ge0 mr1 (Internal f_simplicity_read32) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong am) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_simplicity_read32) [Vptr bl Ptrofs.zero] E0 mr3 (Vlong al) ->
  Clight2.eval_funcall ge0 mr3 (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr4 (Vlong b) ->
  Clight2.exec_stmt ge0 (divmod128_env bl bqh bql br)
    (PTree.set _t'5 (Vint (bit_int (divmod128_guard ah b)))
      (divmod128_read_env (divmod128_temps env bd dbase bs sbase) ah am al b))
    mr4 divmod128_branch_stmt E0 lef me Out_normal ->
  Mem.free_list me (blocks_of_env ge0 (divmod128_env bl bqh bql br)) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_div_mod_128_64)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HSbase HAlign Hfresh HA HB HC HD Hbytes Hcopy Hread1 Hread2 Hread3 Hread4 Hbranch Hfree.
  set (le0 := divmod128_temps env bd dbase bs sbase).
  set (le1 := divmod128_read_set le0 _ah _t'1 ah).
  set (le2 := divmod128_read_set le1 _am _t'2 am).
  set (le3 := divmod128_read_set le2 _al _t'3 al).
  set (le4 := divmod128_read_set le3 _b _t'4 b).
  eapply eval_funcall_internal with (e := divmod128_env bl bqh bql br) (le1 := le0) (le2 := lef)
    (m1 := md) (m2 := me) (out := Out_return (Some (Vint Int.one,tint))).
  - eapply divmod128_entry; eassumption.
  - rewrite divmod128_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mcopy).
    + eapply exec_divmod128_source_copy; try eassumption; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mr1).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr1).
        -- apply (call_divmod128_read W64); exact Hread1.
        -- apply exec_set. apply eval_Etempvar. apply PTree.gss.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mr2).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
           ++ apply (call_divmod128_read W32); exact Hread2.
           ++ apply exec_set. apply eval_Etempvar. apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mr3).
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr3).
              ** apply (call_divmod128_read W32); exact Hread3.
              ** apply exec_set. apply eval_Etempvar. apply PTree.gss.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mr4).
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr4).
                 --- apply (call_divmod128_read W64); exact Hread4.
                 --- apply exec_set. apply eval_Etempvar. apply PTree.gss.
              ** eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := lef) (m1 := me).
                 --- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0)
                       (le1 := PTree.set _t'5 (Vint (bit_int (divmod128_guard ah b))) le4) (m1 := mr4).
                     +++ apply exec_divmod128_guard_stmt.
                         *** unfold le4, le3, le2, le1, divmod128_read_set. divmod128_lookup.
                         *** unfold le4, divmod128_read_set. divmod128_lookup.
                     +++ exact Hbranch.
                 --- apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - exact Hfree.
Qed.

Lemma eval_divmod128_invalid_expr e le m : eval_expr ge0 e le m divmod128_invalid_expr
    (Vlong (Int64.repr Int64.max_unsigned)).
Proof.
  eapply eval_Ecast with (v1 := Vint Int.mone).
  - eapply eval_Eunop with (v1 := Vint Int.one); [apply eval_Econst_int|reflexivity].
  - change (Some (Vlong (Int64.repr (-1))) = Some (Vlong (Int64.repr Int64.max_unsigned))).
    f_equal. f_equal. apply Int64.eqm_samerepr. exists (-1). reflexivity.
Qed.

Lemma exec_divmod128_invalid_composes e le m m1 mf bd dbase :
  e!_simplicity_write64 = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_write64)
    [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr Int64.max_unsigned)] E0 m1 Vundef ->
  Clight2.eval_funcall ge0 m1 (Internal f_simplicity_write64)
    [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr Int64.max_unsigned)] E0 mf Vundef ->
  Clight2.exec_stmt ge0 e le m divmod128_invalid_stmt E0 le mf Out_normal.
Proof.
  intros HE HD HW1 HW2. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
  all: eapply call_frame_writer with (bd := bd) (dofs := Ptrofs.repr dbase)
    (f := f_simplicity_write64) (b := jet_symbol_block _simplicity_write64)
    (v := Vlong (Int64.repr Int64.max_unsigned)) (vret := Vundef); try assumption; try reflexivity.
  all: first [apply (wide_writer_symbol W64) | apply (wide_writer_funct W64) | apply eval_divmod128_invalid_expr].
Qed.
