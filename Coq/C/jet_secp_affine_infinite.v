(** Whole original affine conversion on its infinity branch, including both
    unused local allocations, the actual clear calls, early return and frees.
    Source coordinates need not be initialized; the source flag is nonzero. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_fns
  C.jet_secp_fe_nv C.jet_secp_curve_frame C.jet_secp_curve_statements
  C.jet_secp_gej_affine_arithmetic C.jet_secp_gej_affine_entry C.jet_secp_gej_affine_finish
  C.jet_secp_affine_set_infinity C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition affine_infinite_temps br bp flag :=
  PTree.set _t'1 (Vint flag) (affine_entry_temps br bp).

Lemma exec_affine_infinite_flag le m mf bp br b2 b3 flag :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
  Mem.load Mint32 m bp 120=Some (Vint flag) -> flag<>Int.zero ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_infinity)
    [Vptr br Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m affine_flag_statement
    E0 (PTree.set _t'1 (Vint flag) le) mf (Out_return None).
Proof.
  intros Point Result Flag Nonzero Call.
  unfold affine_flag_statement;cbn [fn_body].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'1 (Vint flag) le).
  - apply exec_Sset.
    destruct (affine_point_layout _infinity 120 ltac:(right;right;right;left;reflexivity))
      as (co & Cenv & Offset).
    eapply eval_Elvalue with (loc:=bp) (ofs:=Ptrofs.repr 120) (bf:=Full).
    + rewrite <-(Ptrofs.add_zero_l (Ptrofs.repr 120)).
      eapply eval_Efield_struct with (co:=co) (delta:=120).
      * eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact Point|apply deref_loc_copy;reflexivity].
      * reflexivity.
      * exact Cenv.
      * exact Offset.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Flag].
  - eapply exec_Sifthenelse with (v1:=Vint flag) (b:=true).
    + apply eval_Etempvar;apply PTree.gss.
    + unfold bool_val;rewrite Int.eq_false by exact Nonzero;reflexivity.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf)
        (le1:=PTree.set _t'1 (Vint flag) le).
      * change (Clight2.exec_stmt secp_ge (affine_local_env b2 b3)
          (PTree.set _t'1 (Vint flag) le) m
          (curve_call _secp256k1_ge_set_infinity f_secp256k1_ge_set_infinity None
            [Etempvar _r (tptr curve_ge_type)]) E0 (PTree.set _t'1 (Vint flag) le) mf Out_normal).
        eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero]) (v:=Vundef).
        -- unfold secp_pure;repeat (first [left;reflexivity|right]).
        -- reflexivity.
        -- eapply eval_Econs.
           ++ apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Result.
           ++ reflexivity.
           ++ constructor.
        -- exact Call.
      * constructor.
Qed.

Theorem eval_affine_infinite_owned m bp br flag : bp<>br -> flag<>Int.zero ->
  Mem.load Mint32 m bp 120=Some (Vint flag) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_gej_var)
    [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero] E0 mf Vundef /\
  fe_at mf br 0 (repeat Int64.zero 5) /\ fe_at mf br 40 (repeat Int64.zero 5) /\
  Mem.load Mint32 mf br 80=Some (Vint Int.one) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
  lframe (fun b _=>b<>br) m mf /\ readonly_preserved m mf.
Proof.
  intros Separate Nonzero Flag FP FR.
  destruct (Mem.alloc m 0 40) as (m1,b2) eqn:A1.
  destruct (Mem.alloc m1 0 40) as (ma,b3) eqn:A2.
  pose proof (affine_helper_entry m m1 ma b2 b3 br bp A1 A2) as Entry.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ A1) as Fresh2.
  assert (Fresh3:~Mem.valid_block m b3).
  { intro Valid;apply (Mem.fresh_block_alloc _ _ _ _ _ A2);eapply Mem.valid_block_alloc;eassumption. }
  assert (N23:b2<>b3).
  { intro Same;apply (Mem.fresh_block_alloc _ _ _ _ _ A2);rewrite <-Same;eapply Mem.valid_new_block;exact A1. }
  assert (ValidP:Mem.valid_block m bp) by (eapply Mem.perm_valid_block;apply (FP 0);lia).
  assert (ValidR:Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FR 0);lia).
  assert (P2:bp<>b2) by congruence.
  assert (P3:bp<>b3) by congruence.
  assert (R2:br<>b2) by congruence.
  assert (R3:br<>b3) by congruence.
  assert (AllocFrame:lframe (fun _ _=>True) m ma).
  { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
  assert (FlagA:Mem.load Mint32 ma bp 120=Some (Vint flag)).
  { rewrite (proj1 AllocFrame);[exact Flag|exact ValidP|intros;exact I]. }
  assert (FRA:Mem.range_perm ma br 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FR|exact AllocFrame|intros;exact I]. }
  assert (FPA:Mem.range_perm ma bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FP|exact AllocFrame|intros;exact I]. }
  assert (F2A:Mem.range_perm ma b2 0 40 Cur Freeable).
  { intros pos Range;eapply Mem.perm_alloc_1;[exact A2|];eapply Mem.perm_alloc_2;eassumption. }
  assert (F3A:Mem.range_perm ma b3 0 40 Cur Freeable).
  { intros pos Range;eapply Mem.perm_alloc_2;eassumption. }
  destruct (eval_affine_set_infinity_owned ma br FRA)
    as (ms & Setter & X & Y & FlagS & FRS & SetFrame & SetReadonly).
  assert (FPS:Mem.range_perm ms bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FPA|exact SetFrame|intros;exact Separate]. }
  assert (F2S:Mem.range_perm ms b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F2A|exact SetFrame|intros;congruence]. }
  assert (F3S:Mem.range_perm ms b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3A|exact SetFrame|intros;congruence]. }
  destruct (free_list_exists [(b2,0,40);(b3,0,40)] ms) as (mf & Free & Unchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [Eq|[Eq|Nil]];[inversion Eq;subst;exact F2S|inversion Eq;subst;exact F3S|contradiction].
  - assert (FreeFrame:lframe (fun b _=>b<>b2 /\ b<>b3) ms mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos [Not2 Not3] Valid;cbn;intuition congruence. }
    assert (XF:fe_at mf br 0 (repeat Int64.zero 5)).
    { eapply curve_keep_field_range;[reflexivity|exact X|exact FreeFrame|intros;split;assumption]. }
    assert (YF:fe_at mf br 40 (repeat Int64.zero 5)).
    { eapply curve_keep_field_range;[reflexivity|exact Y|exact FreeFrame|intros;split;assumption]. }
    assert (FlagF:Mem.load Mint32 mf br 80=Some (Vint Int.one)).
    { rewrite (proj1 FreeFrame);[exact FlagS|eapply Mem.perm_valid_block;apply (FRS 0);lia|intros;split;assumption]. }
    assert (FPF:Mem.range_perm mf bp 0 128 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FPS|exact FreeFrame|intros;split;assumption]. }
    assert (FRF:Mem.range_perm mf br 0 88 Cur Freeable).
    { eapply curve_keep_free;[lia|exact FRS|exact FreeFrame|intros;split;assumption]. }
    assert (Frame:lframe (fun b _=>b<>br) m mf).
    { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>br).
      - eapply lframe_trans.
        + eapply lframe_implies;[exact AllocFrame|intros;exact I].
        + eapply lframe_trans.
          * eapply lframe_implies;[exact SetFrame|];intros b pos [Valid Outside] _;exact Outside.
          * eapply lframe_implies;[exact FreeFrame|];intros b pos [Valid Outside] _;split;congruence.
      - intros b pos Outside Valid;split;assumption. }
    exists mf;split.
    + eapply eval_funcall_internal with (e:=affine_local_env b2 b3) (le1:=affine_entry_temps br bp)
        (le2:=affine_infinite_temps br bp flag) (m1:=ma) (m2:=ms) (out:=Out_return None).
      * exact Entry.
      * rewrite affine_entry_source;apply exec_Sseq_2;[|discriminate].
        apply (exec_affine_infinite_flag (affine_entry_temps br bp) ma ms bp br b2 b3 flag);
          [reflexivity|reflexivity|exact FlagA|exact Nonzero|exact Setter].
      * reflexivity.
      * rewrite affine_local_blocks;exact Free.
    + split;[exact XF|];split;[exact YF|];split;[exact FlagF|];split;[exact FPF|];
        split;[exact FRF|];split;[exact Frame|].
      eapply preserved_trans;[eapply entry_preserved;exact Entry|].
      eapply preserved_trans;[exact SetReadonly|eapply freelist_preserved;exact Free].
Qed.
