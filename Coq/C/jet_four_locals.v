(** Shared four-local allocation/cleanup facts, parameterized by actual sizes.
    Calls and struct-copy consumers still prove their concrete Clight entry. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition four_local_distinct (a b c d : block) :=
  a <> b /\ a <> c /\ a <> d /\ b <> c /\ b <> d /\ c <> d.
Definition four_local_permissions m a na b nb c nc d nd :=
  Mem.range_perm m a 0 na Cur Freeable /\ Mem.range_perm m b 0 nb Cur Freeable /\
  Mem.range_perm m c 0 nc Cur Freeable /\ Mem.range_perm m d 0 nd Cur Freeable.

Theorem allocate_four_locals m na nb nc nd : exists ma mb mc md a b c d,
  Mem.alloc m 0 na = (ma,a) /\ Mem.alloc ma 0 nb = (mb,b) /\
  Mem.alloc mb 0 nc = (mc,c) /\ Mem.alloc mc 0 nd = (md,d) /\
  four_local_distinct a b c d /\ four_local_permissions md a na b nb c nc d nd /\
  (forall x, Mem.valid_block m x -> x <> a /\ x <> b /\ x <> c /\ x <> d) /\
  (forall chunk x ofs, Mem.valid_block m x -> Mem.load chunk md x ofs = Mem.load chunk m x ofs) /\
  (forall x ofs kind p, Mem.perm m x ofs kind p -> Mem.perm md x ofs kind p).
Proof.
  destruct (Mem.alloc m 0 na) as (ma & a) eqn:HA.
  destruct (Mem.alloc ma 0 nb) as (mb & b) eqn:HB.
  destruct (Mem.alloc mb 0 nc) as (mc & c) eqn:HC.
  destruct (Mem.alloc mc 0 nd) as (md & d) eqn:HD.
  assert (HVa : forall x, Mem.valid_block m x -> Mem.valid_block ma x) by (intros; eapply Mem.valid_block_alloc; eauto).
  assert (HVb : forall x, Mem.valid_block ma x -> Mem.valid_block mb x) by (intros; eapply Mem.valid_block_alloc; eauto).
  assert (HVc : forall x, Mem.valid_block mb x -> Mem.valid_block mc x) by (intros; eapply Mem.valid_block_alloc; eauto).
  assert (VA : Mem.valid_block ma a) by (eapply Mem.valid_new_block; exact HA).
  assert (VB : Mem.valid_block mb b) by (eapply Mem.valid_new_block; exact HB).
  assert (VC : Mem.valid_block mc c) by (eapply Mem.valid_new_block; exact HC).
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as FA.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HB) as FB.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HC) as FC.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HD) as FD.
  assert (Hsep : four_local_distinct a b c d) by (repeat split; intro H; subst; eauto).
  assert (HP : four_local_permissions md a na b nb c nc d nd).
  { repeat split; intros ofs H.
    - eapply Mem.perm_alloc_1; [exact HD|]. eapply Mem.perm_alloc_1; [exact HC|].
      eapply Mem.perm_alloc_1; [exact HB|]. eapply Mem.perm_alloc_2; eauto.
    - eapply Mem.perm_alloc_1; [exact HD|]. eapply Mem.perm_alloc_1; [exact HC|]. eapply Mem.perm_alloc_2; eauto.
    - eapply Mem.perm_alloc_1; [exact HD|]. eapply Mem.perm_alloc_2; eauto.
    - eapply Mem.perm_alloc_2; eauto. }
  exists ma, mb, mc, md, a, b, c, d. do 6 (split; [first [reflexivity|assumption]|]). split.
  - intros x HV. repeat split; intro H; subst; eauto.
  - split.
    + intros chunk x ofs HV.
      erewrite Mem.load_alloc_unchanged; [|exact HD|apply HVc, HVb, HVa; exact HV].
      erewrite Mem.load_alloc_unchanged; [|exact HC|apply HVb, HVa; exact HV].
      erewrite Mem.load_alloc_unchanged; [|exact HB|apply HVa; exact HV]. eapply Mem.load_alloc_unchanged; eauto.
    + intros x ofs kind p H. eapply Mem.perm_alloc_1; [exact HD|].
      eapply Mem.perm_alloc_1; [exact HC|]. eapply Mem.perm_alloc_1; [exact HB|]. eapply Mem.perm_alloc_1; eauto.
Qed.

Theorem free_four_locals m a na b nb c nc d nd :
  four_local_distinct a b c d -> four_local_permissions m a na b nb c nc d nd ->
  exists mf, Mem.free_list m [(a,0,na);(b,0,nb);(c,0,nc);(d,0,nd)] = Some mf /\
    (forall chunk x ofs, x <> a -> x <> b -> x <> c -> x <> d -> Mem.load chunk mf x ofs = Mem.load chunk m x ofs) /\
    (forall x ofs kind p, x <> a -> x <> b -> x <> c -> x <> d -> Mem.perm m x ofs kind p -> Mem.perm mf x ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros (Nab & Nac & Nad & Nbc & Nbd & Ncd) (PA & PB & PC & PD).
  destruct (Mem.range_perm_free m a 0 na PA) as (ma & FA).
  assert (PB1 : Mem.range_perm ma b 0 nb Cur Freeable).
  { intros ofs H. eapply Mem.perm_free_1; [exact FA|auto|apply PB; exact H]. }
  assert (PC1 : Mem.range_perm ma c 0 nc Cur Freeable).
  { intros ofs H. eapply Mem.perm_free_1; [exact FA|auto|apply PC; exact H]. }
  assert (PD1 : Mem.range_perm ma d 0 nd Cur Freeable).
  { intros ofs H. eapply Mem.perm_free_1; [exact FA|auto|apply PD; exact H]. }
  destruct (Mem.range_perm_free ma b 0 nb PB1) as (mb & FB).
  assert (PC2 : Mem.range_perm mb c 0 nc Cur Freeable).
  { intros ofs H. eapply Mem.perm_free_1; [exact FB|auto|apply PC1; exact H]. }
  assert (PD2 : Mem.range_perm mb d 0 nd Cur Freeable).
  { intros ofs H. eapply Mem.perm_free_1; [exact FB|auto|apply PD1; exact H]. }
  destruct (Mem.range_perm_free mb c 0 nc PC2) as (mc & FC).
  assert (PD3 : Mem.range_perm mc d 0 nd Cur Freeable).
  { intros ofs H. eapply Mem.perm_free_1; [exact FC|auto|apply PD2; exact H]. }
  destruct (Mem.range_perm_free mc d 0 nd PD3) as (mf & FD).
  exists mf. split; [cbn [Mem.free_list]; rewrite FA, FB, FC, FD; reflexivity|]. split.
  - intros chunk x ofs NA NB NC ND.
    erewrite Mem.load_free; [|exact FD|auto]. erewrite Mem.load_free; [|exact FC|auto].
    erewrite Mem.load_free; [|exact FB|auto]. erewrite Mem.load_free; [reflexivity|exact FA|auto].
  - split.
    + intros x ofs kind p NA NB NC ND H. eapply Mem.perm_free_1; [exact FD|auto|].
      eapply Mem.perm_free_1; [exact FC|auto|]. eapply Mem.perm_free_1; [exact FB|auto|]. eapply Mem.perm_free_1; eauto.
    + rewrite (Mem.nextblock_free _ _ _ _ _ FD), (Mem.nextblock_free _ _ _ _ _ FC),
        (Mem.nextblock_free _ _ _ _ _ FB), (Mem.nextblock_free _ _ _ _ _ FA); reflexivity.
Qed.
