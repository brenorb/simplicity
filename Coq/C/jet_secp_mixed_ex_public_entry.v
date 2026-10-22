(** Actual four-local entry and freeing order of the original extended jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_public_copy
  C.jet_secp_mixed_public_entry C.jet_secp_mixed_ex_public_body.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma mixed_ex_public_entry v_env m ma mb mc md bl bp ba br bd dbase bs sbase :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,bp) ->
  Mem.alloc mb 0 88=(mc,ba) -> Mem.alloc mc 0 40=(md,br) ->
  function_entry2 secp_ge f_simplicity_gej_ge_add_ex
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (mixed_ex_public_env bl bp ba br) (secp_public_temps v_env bd dbase bs sbase) md.
Proof.
  intros HA HB HC HD;constructor.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - cbn;repeat constructor;cbn;intuition discriminate.
  - intros x y HX HY Hxy;cbn in HX,HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;subst;
      first [contradiction|vm_compute in Hxy;discriminate|congruence].
  - eapply alloc_variables_cons with (m1:=ma) (b1:=bl);[exact HA|].
    eapply alloc_variables_cons with (m1:=mb) (b1:=bp);[exact HB|].
    eapply alloc_variables_cons with (m1:=mc) (b1:=ba);[exact HC|].
    eapply alloc_variables_cons with (m1:=md) (b1:=br);[exact HD|constructor].
  - reflexivity.
Qed.

Lemma mixed_ex_allocations_frame P m ma mb mc md bl bp ba br :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,bp) ->
  Mem.alloc mb 0 88=(mc,ba) -> Mem.alloc mc 0 40=(md,br) -> lframe P m md.
Proof.
  intros HA HB HC HD;eapply lframe_trans.
  - exact (mixed_allocations_frame P m ma mb mc bl bp ba HA HB HC).
  - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact HD.
Qed.

Lemma mixed_ex_allocations_free m ma mb mc md bl bp ba br :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,bp) ->
  Mem.alloc mb 0 88=(mc,ba) -> Mem.alloc mc 0 40=(md,br) ->
  Mem.range_perm md bl 0 16 Cur Freeable /\ Mem.range_perm md bp 0 128 Cur Freeable /\
  Mem.range_perm md ba 0 88 Cur Freeable /\ Mem.range_perm md br 0 40 Cur Freeable.
Proof.
  intros HA HB HC HD.
  destruct (mixed_allocations_free m ma mb mc bl bp ba HA HB HC) as (FL & FP & FA).
  repeat split;intros pos HP.
  - eapply Mem.perm_alloc_1;[exact HD|apply FL;exact HP].
  - eapply Mem.perm_alloc_1;[exact HD|apply FP;exact HP].
  - eapply Mem.perm_alloc_1;[exact HD|apply FA;exact HP].
  - eapply Mem.perm_alloc_2;[exact HD|exact HP].
Qed.

Lemma mixed_ex_allocations_fresh m ma mb mc md bl bp ba br :
  Mem.alloc m 0 16=(ma,bl) -> Mem.alloc ma 0 128=(mb,bp) ->
  Mem.alloc mb 0 88=(mc,ba) -> Mem.alloc mc 0 40=(md,br) ->
  (~Mem.valid_block m bl /\ ~Mem.valid_block m bp /\ ~Mem.valid_block m ba /\ ~Mem.valid_block m br) /\
  NoDup [bl;bp;ba;br].
Proof.
  intros HA HB HC HD.
  destruct (mixed_allocations_fresh m ma mb mc bl bp ba HA HB HC) as (NL & NP & NA & SPL & SAL & SPA).
  destruct (mixed_allocations_free m ma mb mc bl bp ba HA HB HC) as (FL & FP & FA).
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HD) as NR.
  assert (VL : Mem.valid_block mc bl) by (eapply Mem.perm_valid_block;apply (FL 0);lia).
  assert (VP : Mem.valid_block mc bp) by (eapply Mem.perm_valid_block;apply (FP 0);lia).
  assert (VA : Mem.valid_block mc ba) by (eapply Mem.perm_valid_block;apply (FA 0);lia).
  assert (SLR : bl<>br) by (intro HE;apply NR;rewrite <-HE;exact VL).
  assert (SPR : bp<>br) by (intro HE;apply NR;rewrite <-HE;exact VP).
  assert (SAR : ba<>br) by (intro HE;apply NR;rewrite <-HE;exact VA).
  split.
  - repeat split;try assumption;intro HV;apply NR.
    eapply Mem.valid_block_alloc;[exact HC|].
    eapply Mem.valid_block_alloc;[exact HB|].
    eapply Mem.valid_block_alloc;[exact HA|exact HV].
  - repeat constructor;cbn [In];intuition congruence.
Qed.

Lemma mixed_ex_public_blocks bl bp ba br :
  blocks_of_env secp_ge (mixed_ex_public_env bl bp ba br)=
    [(bl,0,16);(bp,0,128);(ba,0,88);(br,0,40)].
Proof. reflexivity. Qed.

Lemma mixed_ex_free_public_locals m bl bp ba br : NoDup [bl;bp;ba;br] ->
  Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
  Mem.range_perm m ba 0 88 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable ->
  exists mf, Mem.free_list m (blocks_of_env secp_ge (mixed_ex_public_env bl bp ba br))=Some mf /\
    lframe (fun b _=>b<>bl /\ b<>bp /\ b<>ba /\ b<>br) m mf.
Proof.
  intros Sep FL FP FA FR.
  destruct (free_list_exists [(bl,0,16);(bp,0,128);(ba,0,88);(br,0,40)] m) as (mf & Free & Frame).
  - repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep.
    cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [H|[H|[H|[H|H]]]];
      try contradiction;inversion H;subst;assumption.
  - exists mf;split;[rewrite mixed_ex_public_blocks;exact Free|].
    eapply lframe_implies;[apply lframe_unchanged;exact Frame|].
    intros b pos (NL & NP & NA & NR) HV;cbn;intuition congruence.
Qed.
