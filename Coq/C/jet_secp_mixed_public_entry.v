(** The original public mixed addition allocates a frame, a point and an affine point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Events Values.
Require Import C.jet_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_public_copy.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_public_env (bl bp bc : block) : env :=
  PTree.set _b (bc,Tstruct __6121 noattr)
    (PTree.set _a (bp,Tstruct __6123 noattr)
      (PTree.set _src (bl,Tstruct _frameItem noattr) empty_env)).

Lemma mixed_public_entry v_env m ma mb mc bl bp bc bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,bp) -> Mem.alloc mb 0 88 = (mc,bc) ->
  function_entry2 secp_ge f_simplicity_gej_ge_add
    [Vptr bd (Ptrofs.repr dbase);Vptr bs (Ptrofs.repr sbase);v_env] m
    (mixed_public_env bl bp bc) (secp_public_temps v_env bd dbase bs sbase) mc.
Proof.
  intros HA HB HC; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma,bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := bp).
      * change (Mem.alloc ma 0 128 = (mb,bp)); exact HB.
      * eapply alloc_variables_cons with (m1 := mc) (b1 := bc).
        -- change (Mem.alloc mb 0 88 = (mc,bc)); exact HC.
        -- constructor.
  - reflexivity.
Qed.

Lemma mixed_public_blocks bl bp bc :
  blocks_of_env secp_ge (mixed_public_env bl bp bc) = [(bl,0,16);(bp,0,128);(bc,0,88)].
Proof. reflexivity. Qed.

Lemma mixed_free_public_locals m bl bp bc : bp <> bl -> bc <> bl -> bp <> bc ->
  Mem.range_perm m bl 0 16 Cur Freeable -> Mem.range_perm m bp 0 128 Cur Freeable ->
  Mem.range_perm m bc 0 88 Cur Freeable ->
  exists mf, Mem.free_list m (blocks_of_env secp_ge (mixed_public_env bl bp bc)) = Some mf /\
    lframe (fun b _ => b <> bp /\ b <> bc /\ b <> bl) m mf.
Proof.
  intros HPL HCL HPC HL HP HC.
  destruct (free_list_exists [(bl,0,16);(bp,0,128);(bc,0,88)] m) as (mf & HF & HU).
  - cbn; repeat constructor; cbn; intuition congruence.
  - intros b lo hi [H|[H|[H|H]]];
      [inversion H; subst; exact HL|inversion H; subst; exact HP|inversion H; subst; exact HC|contradiction].
  - exists mf; split; [rewrite mixed_public_blocks; exact HF|].
    eapply lframe_implies; [apply lframe_unchanged; exact HU|].
    intros b pos [HNP [HNC HNL]] HV; cbn; intuition congruence.
Qed.

Lemma mixed_allocations_fresh m ma mb mc bl bp bc :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,bp) -> Mem.alloc mb 0 88 = (mc,bc) ->
  ~ Mem.valid_block m bl /\ ~ Mem.valid_block m bp /\ ~ Mem.valid_block m bc /\
  bp <> bl /\ bc <> bl /\ bp <> bc.
Proof.
  intros HA HB HC.
  pose proof (Mem.valid_new_block _ _ _ _ _ HA) as VL.
  pose proof (Mem.valid_new_block _ _ _ _ _ HB) as VP.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as NL.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HB) as NP.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HC) as NC.
  assert (VL' : Mem.valid_block mb bl) by (eapply Mem.valid_block_alloc; eassumption).
  repeat split; intros HE; try exact (NL HE).
  - apply NP; eapply Mem.valid_block_alloc; eassumption.
  - apply NC; eapply Mem.valid_block_alloc; [exact HB|]; eapply Mem.valid_block_alloc; eassumption.
  - apply NP; rewrite HE; exact VL.
  - apply NC; rewrite HE; exact VL'.
  - apply NC; rewrite <- HE; exact VP.
Qed.

Lemma mixed_allocations_free m ma mb mc bl bp bc :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,bp) -> Mem.alloc mb 0 88 = (mc,bc) ->
  Mem.range_perm mc bl 0 16 Cur Freeable /\ Mem.range_perm mc bp 0 128 Cur Freeable /\
  Mem.range_perm mc bc 0 88 Cur Freeable.
Proof.
  intros HA HB HC; repeat split; intros pos HPos.
  - eapply Mem.perm_alloc_1; [exact HC|]; eapply Mem.perm_alloc_1; [exact HB|];
      eapply Mem.perm_alloc_2; eassumption.
  - eapply Mem.perm_alloc_1; [exact HC|]; eapply Mem.perm_alloc_2; eassumption.
  - eapply Mem.perm_alloc_2; eassumption.
Qed.

Lemma mixed_allocations_frame P m ma mb mc bl bp bc :
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 128 = (mb,bp) -> Mem.alloc mb 0 88 = (mc,bc) ->
  C.jet_sx_mem.lframe P m mc.
Proof.
  intros HA HB HC; eapply C.jet_sx_mem.lframe_trans.
  - apply C.jet_sx_mem.lframe_unchanged; eapply Mem.alloc_unchanged_on; exact HA.
  - eapply C.jet_sx_mem.lframe_trans;
      apply C.jet_sx_mem.lframe_unchanged; eapply Mem.alloc_unchanged_on; eassumption.
Qed.
