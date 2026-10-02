(** Derive the actual four LP64 local allocations and their initial memory
    contracts. All old blocks remain framed; no allocation is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition divmod128_local_distinct (bl bqh bql br : block) :=
  bl <> bqh /\ bl <> bql /\ bl <> br /\ bqh <> bql /\ bqh <> br /\ bql <> br.
Definition divmod128_local_permissions m bl bqh bql br :=
  Mem.range_perm m bl 0 16 Cur Freeable /\ Mem.range_perm m bqh 0 8 Cur Freeable /\
  Mem.range_perm m bql 0 8 Cur Freeable /\ Mem.range_perm m br 0 8 Cur Freeable.

Theorem allocate_divmod128_locals m :
  exists ma mb mc md bl bqh bql br,
    Mem.alloc m 0 16 = (ma,bl) /\ Mem.alloc ma 0 8 = (mb,bqh) /\
    Mem.alloc mb 0 8 = (mc,bql) /\ Mem.alloc mc 0 8 = (md,br) /\
    divmod128_local_distinct bl bqh bql br /\ divmod128_local_permissions md bl bqh bql br /\
    (forall bb, Mem.valid_block m bb -> bb <> bl /\ bb <> bqh /\ bb <> bql /\ bb <> br) /\
    (forall chunk bb ofs, Mem.valid_block m bb -> Mem.load chunk md bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm md bb ofs kind p).
Proof.
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 8) as [mb bqh] eqn:HB.
  destruct (Mem.alloc mb 0 8) as [mc bql] eqn:HC.
  destruct (Mem.alloc mc 0 8) as [md br] eqn:HD.
  assert (HVa : forall bb, Mem.valid_block m bb -> Mem.valid_block ma bb).
  { intros bb HV. eapply Mem.valid_block_alloc; eauto. }
  assert (HVb : forall bb, Mem.valid_block ma bb -> Mem.valid_block mb bb).
  { intros bb HV. eapply Mem.valid_block_alloc; eauto. }
  assert (HVc : forall bb, Mem.valid_block mb bb -> Mem.valid_block mc bb).
  { intros bb HV. eapply Mem.valid_block_alloc; eauto. }
  assert (HL : Mem.valid_block ma bl) by (eapply Mem.valid_new_block; exact HA).
  assert (HQH : Mem.valid_block mb bqh) by (eapply Mem.valid_new_block; exact HB).
  assert (HQL : Mem.valid_block mc bql) by (eapply Mem.valid_new_block; exact HC).
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as FLA.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HB) as FHB.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HC) as FQC.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HD) as FRD.
  assert (Hdistinct : divmod128_local_distinct bl bqh bql br).
  { repeat split; intro HE; subst; eauto. }
  assert (Hlocals : divmod128_local_permissions md bl bqh bql br).
  { repeat split; intros ofs Hrange.
    - eapply Mem.perm_alloc_1; [exact HD|]. eapply Mem.perm_alloc_1; [exact HC|].
      eapply Mem.perm_alloc_1; [exact HB|]. eapply Mem.perm_alloc_2; eauto.
    - eapply Mem.perm_alloc_1; [exact HD|]. eapply Mem.perm_alloc_1; [exact HC|].
      eapply Mem.perm_alloc_2; eauto.
    - eapply Mem.perm_alloc_1; [exact HD|]. eapply Mem.perm_alloc_2; eauto.
    - eapply Mem.perm_alloc_2; eauto. }
  exists ma, mb, mc, md, bl, bqh, bql, br.
  do 6 (split; [first [reflexivity | assumption]|]). split.
  - intros bb HV. repeat split; intro HE; subst; eauto.
  - split.
    + intros chunk bb ofs HV.
      erewrite Mem.load_alloc_unchanged; [|exact HD|apply HVc, HVb, HVa; exact HV].
      erewrite Mem.load_alloc_unchanged; [|exact HC|apply HVb, HVa; exact HV].
      erewrite Mem.load_alloc_unchanged; [|exact HB|apply HVa; exact HV].
      eapply Mem.load_alloc_unchanged; eauto.
    + intros bb ofs kind p HP. eapply Mem.perm_alloc_1; [exact HD|].
      eapply Mem.perm_alloc_1; [exact HC|]. eapply Mem.perm_alloc_1; [exact HB|].
      eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma divmod128_local_slots_writable m bl bqh bql br :
  divmod128_local_permissions m bl bqh bql br ->
  Mem.valid_access m Mint64 bl 8 Writable /\ Mem.valid_access m Mint64 bqh 0 Writable /\
  Mem.valid_access m Mint64 bql 0 Writable /\ Mem.valid_access m Mint64 br 0 Writable.
Proof.
  intros (PL & PH & PQ & PR). repeat split.
  - intros ofs Hrange. eapply Mem.perm_implies; [apply PL; cbn in Hrange; lia|constructor].
  - exists 1. reflexivity.
  - intros ofs Hrange. eapply Mem.perm_implies; [apply PH; exact Hrange|constructor].
  - exists 0. reflexivity.
  - intros ofs Hrange. eapply Mem.perm_implies; [apply PQ; exact Hrange|constructor].
  - exists 0. reflexivity.
  - intros ofs Hrange. eapply Mem.perm_implies; [apply PR; exact Hrange|constructor].
  - exists 0. reflexivity.
Qed.
