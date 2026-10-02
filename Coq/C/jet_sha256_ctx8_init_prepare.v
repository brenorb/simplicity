(** Initial-only preparation of the public context initializer: four fresh
    locals, actual source copy, complete initializer and actual context copy. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_four_locals C.jet_frame_layout C.jet_frame_copy_layout.
Require Import C.jet_sha256_iv_init C.jet_uint32_array_init C.jet_sha256_init_layout C.jet_struct_copy_loads.
Require Import C.jet_bitmachine_rep.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem prepare_sha256_ctx8_init m bs sbase source edge rc :
  frame_fields_at m bs sbase source edge rc ->
  exists ma mb mc md ms mi mx bl bi bc br srcbytes ctxbytes,
    Mem.alloc m 0 16 = (ma,bl) /\ Mem.alloc ma 0 32 = (mb,bi) /\
    Mem.alloc mb 0 88 = (mc,bc) /\ Mem.alloc mc 0 88 = (md,br) /\
    Mem.loadbytes md bs sbase 16 = Some srcbytes /\ Mem.storebytes md bl 0 srcbytes = Some ms /\
    Clight2.eval_funcall ge0 ms (Internal f_sha256_init) [Vptr br Ptrofs.zero; Vptr bi Ptrofs.zero] E0 mi Vundef /\
    Mem.loadbytes mi br 0 88 = Some ctxbytes /\ Mem.storebytes mi bc 0 ctxbytes = Some mx /\
    four_local_distinct bl bi bc br /\ four_local_permissions mx bl 16 bi 32 bc 88 br 88 /\
    (forall b, Mem.valid_block m b -> b <> bl /\ b <> bi /\ b <> bc /\ b <> br) /\
    Mem.load Mptr mx bc 0 = Some (Vptr bi Ptrofs.zero) /\
    Mem.load Mint64 mx bc 8 = Some (Vlong Int64.zero) /\
    Mem.load Mint8unsigned mx bc 80 = Some (Vint Int.zero) /\
    uint32_array_at mx bi 0 sha256_iv_words /\
    (forall chunk b ofs, Mem.valid_block m b -> Mem.load chunk mx b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mx b ofs kind p).
Proof.
  intros [HSE HSO]. assert (HS : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  destruct (allocate_four_locals m 16 32 88 88)
    as (ma & mb & mc & md & bl & bi & bc & br & AS & AI & AC & AR & Hsep & Hlocals & Hfresh & HLoads & HPerm).
  destruct Hsep as (Nsi & Nsc & Nsr & Nic & Nir & Ncr).
  destruct Hlocals as (PS & PI & PC & PR).
  assert (HEd : Mem.load Mptr md bs sbase = Some (Vptr source (Ptrofs.repr edge)))
    by (rewrite HLoads by exact HS; exact HSE).
  assert (HOd : Mem.load Mint64 md bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite HLoads by exact HS; exact HSO).
  destruct (frame_loadbytes_at md bs sbase _ _ HEd HOd) as (srcbytes & HSrc).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HSrc) as HSrcLen.
  assert (PSC : Mem.range_perm md bl 0 (0 + Z.of_nat (length srcbytes)) Cur Writable).
  { rewrite HSrcLen. change (Mem.range_perm md bl 0 16 Cur Writable).
    intros ofs H; eapply Mem.perm_implies; [apply PS; exact H|constructor]. }
  destruct (Mem.range_perm_storebytes md bl 0 srcbytes PSC) as (ms & SrcCopy).
  assert (HPs : forall b ofs kind p, Mem.perm md b ofs kind p -> Mem.perm ms b ofs kind p).
  { intros b ofs kind p H; eapply Mem.perm_storebytes_1; eauto. }
  assert (PIS : Mem.range_perm ms bi 0 32 Cur Writable).
  { intros ofs H; apply HPs; eapply Mem.perm_implies; [apply PI; exact H|constructor]. }
  assert (PRS : Mem.range_perm ms br 0 88 Cur Writable).
  { intros ofs H; apply HPs; eapply Mem.perm_implies; [apply PR; exact H|constructor]. }
  destruct (eval_sha256_init_layout ms br bi 0 ltac:(congruence) ltac:(lia)
    ltac:(change (32 <= 18446744073709551615); lia) ltac:(exists 0; reflexivity) PRS PIS)
    as (mi & HInit & HOutI & HCounterI & HOverflowI & HArrayI & HInitLoads & HInitPerm & HInitValid).
  assert (PRI : Mem.range_perm mi br 0 88 Cur Readable).
  { intros ofs H; apply HInitPerm; eapply Mem.perm_implies; [apply PRS; exact H|constructor]. }
  destruct (Mem.range_perm_loadbytes mi br 0 88 PRI) as (ctxbytes & HCtx).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HCtx) as HCtxLen.
  assert (PCC : Mem.range_perm mi bc 0 (0 + Z.of_nat (length ctxbytes)) Cur Writable).
  { rewrite HCtxLen. change (Mem.range_perm mi bc 0 88 Cur Writable).
    intros ofs H; apply HInitPerm, HPs; eapply Mem.perm_implies; [apply PC; exact H|constructor]. }
  destruct (Mem.range_perm_storebytes mi bc 0 ctxbytes PCC) as (mx & CtxCopy).
  assert (HCtxNew : Mem.loadbytes mx bc 0 88 = Some ctxbytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ CtxCopy) as H; rewrite HCtxLen in H; exact H. }
  assert (HOutX : Mem.load Mptr mx bc 0 = Some (Vptr bi Ptrofs.zero)).
  { eapply equal_loadbytes_field with (m1 := mi) (b1 := br) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 0) (bytes := ctxbytes); [lia|change (8 <= 88); lia|exact HCtx|exact HCtxNew|
      change (8 | 0); exists 0; reflexivity|exact HOutI]. }
  assert (HCounterX : Mem.load Mint64 mx bc 8 = Some (Vlong Int64.zero)).
  { eapply equal_loadbytes_field with (m1 := mi) (b1 := br) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 8) (bytes := ctxbytes); [lia|change (16 <= 88); lia|exact HCtx|exact HCtxNew|
      change (8 | 8); exists 1; reflexivity|exact HCounterI]. }
  assert (HOverflowX : Mem.load Mint8unsigned mx bc 80 = Some (Vint Int.zero)).
  { eapply equal_loadbytes_field with (m1 := mi) (b1 := br) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 80) (bytes := ctxbytes); [lia|change (81 <= 88); lia|exact HCtx|exact HCtxNew|
      change (1 | 80); exists 80; reflexivity|exact HOverflowI]. }
  assert (HLocalX : four_local_permissions mx bl 16 bi 32 bc 88 br 88).
  { repeat split; intros ofs H.
    all: eapply Mem.perm_storebytes_1; [exact CtxCopy|apply HInitPerm, HPs].
    all: first [apply PS|apply PI|apply PC|apply PR]; exact H. }
  exists ma, mb, mc, md, ms, mi, mx, bl, bi, bc, br, srcbytes, ctxbytes.
  do 9 (split; [first [reflexivity|assumption]|]). split; [repeat split; assumption|].
  split; [exact HLocalX|]. split; [exact Hfresh|]. do 3 (split; [assumption|]). split.
  - intros i v Hv. erewrite Mem.load_storebytes_other; [exact (HArrayI i v Hv)|exact CtxCopy|left; exact Nic].
  - split.
    + intros chunk b ofs HV. destruct (Hfresh b HV) as (Ns & Ni & Nc & Nr).
      assert (HVm : Mem.valid_block ms b).
      { eapply Mem.storebytes_valid_block_1; [exact SrcCopy|].
        eapply Mem.valid_block_alloc; [exact AR|]. eapply Mem.valid_block_alloc; [exact AC|].
        eapply Mem.valid_block_alloc; [exact AI|]. eapply Mem.valid_block_alloc; eauto. }
      erewrite Mem.load_storebytes_other; [|exact CtxCopy|left; exact Nc].
      rewrite HInitLoads by auto. erewrite Mem.load_storebytes_other; [apply HLoads; exact HV|exact SrcCopy|left; exact Ns].
    + intros b ofs kind p H. eapply Mem.perm_storebytes_1; [exact CtxCopy|apply HInitPerm, HPs, HPerm; exact H].
Qed.
