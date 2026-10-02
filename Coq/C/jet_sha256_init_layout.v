(** Complete actual sha256_init helper from initial destination/IV permissions.
    Its private compound allocation, every store, By_copy return and free are
    derived here; no intermediate execution is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_sha256_iv_init C.jet_uint32_array_init.
Require Import C.jet_sha256_init_exec C.jet_sha256_init_fields_layout C.jet_struct_copy_loads.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_sha256_init_layout m br bi input :
  br <> bi -> 0 <= input -> input + 32 <= Ptrofs.max_unsigned -> (4 | input) ->
  Mem.range_perm m br 0 88 Cur Writable -> Mem.range_perm m bi input (input + 32) Cur Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_sha256_init) [Vptr br Ptrofs.zero; Vptr bi (Ptrofs.repr input)] E0 mf Vundef /\
    Mem.load Mptr mf br 0 = Some (Vptr bi (Ptrofs.repr input)) /\
    Mem.load Mint64 mf br 8 = Some (Vlong Int64.zero) /\
    Mem.load Mint8unsigned mf br 80 = Some (Vint Int.zero) /\
    uint32_array_at mf bi input sha256_iv_words /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> br \/ ofs + size_chunk chunk <= 0 \/ 88 <= ofs) ->
      (b <> bi \/ ofs + size_chunk chunk <= input \/ input + 32 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros Hri HI HM HA PR PI.
  assert (VR : Mem.valid_block m br) by (eapply Mem.perm_valid_block; apply (PR 0); lia).
  assert (VI : Mem.valid_block m bi) by (eapply Mem.perm_valid_block; apply (PI input); lia).
  destruct (Mem.alloc m 0 88) as (ma & bc) eqn:HC.
  assert (HFresh : forall b, Mem.valid_block m b -> bc <> b).
  { intros b HV HE; subst b; exact (Mem.fresh_block_alloc _ _ _ _ _ HC HV). }
  assert (Hcr : bc <> br) by auto. assert (Hci : bc <> bi) by auto.
  assert (PIA : Mem.range_perm ma bi input (input + 32) Cur Writable).
  { intros ofs H; eapply Mem.perm_alloc_1; [exact HC|apply PI; exact H]. }
  destruct (eval_sha256_iv_init_layout ma bi input HI HM HA PIA)
    as (mi & HInit & HArray & HInitLoads & HInitPerm & HInitValid).
  assert (PC : Mem.range_perm mi bc 0 88 Cur Writable).
  { intros ofs H; apply HInitPerm. eapply Mem.perm_implies;
      [eapply Mem.perm_alloc_2; eauto|constructor]. }
  destruct (exec_sha_ctx_fields_layout (sha_init_env bc) (sha_init_temps br bi input) mi bc bi (Ptrofs.repr input)
    ltac:(unfold sha_init_env; apply Maps.PTree.gss)
    ltac:(unfold sha_init_temps; apply Maps.PTree.gss) PC)
    as (mz & HFields & HO & HCounter & HOverflow & HFieldLoads & HFieldPerm & HFieldValid).
  assert (PCRead : Mem.range_perm mz bc 0 88 Cur Readable).
  { intros ofs H; apply HFieldPerm. eapply Mem.perm_implies; [apply PC; exact H|constructor]. }
  destruct (Mem.range_perm_loadbytes mz bc 0 88 PCRead) as (bytes & HBytes).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HBytes) as HLen.
  assert (PRZ : Mem.range_perm mz br 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLen. change (Mem.range_perm mz br 0 88 Cur Writable).
    intros ofs H; apply HFieldPerm, HInitPerm. eapply Mem.perm_alloc_1; [exact HC|apply PR; exact H]. }
  destruct (Mem.range_perm_storebytes mz br 0 bytes PRZ) as (me & HCopy).
  assert (HNewBytes : Mem.loadbytes me br 0 88 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HCopy) as H; rewrite HLen in H; exact H. }
  assert (HOutCopy : Mem.load Mptr me br 0 = Some (Vptr bi (Ptrofs.repr input))).
  { eapply equal_loadbytes_field with (m1 := mz) (b1 := bc) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 0) (bytes := bytes); [lia|change (8 <= 88); lia|exact HBytes|exact HNewBytes|
      change (8 | 0); exists 0; reflexivity|exact HO]. }
  assert (HCounterCopy : Mem.load Mint64 me br 8 = Some (Vlong Int64.zero)).
  { eapply equal_loadbytes_field with (m1 := mz) (b1 := bc) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 8) (bytes := bytes); [lia|change (16 <= 88); lia|exact HBytes|exact HNewBytes|
      change (8 | 8); exists 1; reflexivity|exact HCounter]. }
  assert (HOverflowCopy : Mem.load Mint8unsigned me br 80 = Some (Vint Int.zero)).
  { eapply equal_loadbytes_field with (m1 := mz) (b1 := bc) (base1 := 0) (base2 := 0)
      (n := 88) (delta := 80) (bytes := bytes); [lia|change (81 <= 88); lia|exact HBytes|exact HNewBytes|
      change (1 | 80); exists 80; reflexivity|exact HOverflow]. }
  assert (PCFree : Mem.range_perm me bc 0 88 Cur Freeable).
  { intros ofs H; eapply Mem.perm_storebytes_1; [exact HCopy|apply HFieldPerm, HInitPerm].
    eapply Mem.perm_alloc_2; eauto. }
  destruct (Mem.range_perm_free me bc 0 88 PCFree) as (mf & HFree).
  exists mf. split; [eapply eval_sha256_init_composes; eauto|]. split.
  - erewrite Mem.load_free; [exact HOutCopy|exact HFree|auto].
  - split.
    + erewrite Mem.load_free; [exact HCounterCopy|exact HFree|auto].
    + split.
      * erewrite Mem.load_free; [exact HOverflowCopy|exact HFree|auto].
      * split.
        -- intros i v Hv. erewrite Mem.load_free; [|exact HFree|auto].
           erewrite Mem.load_storebytes_other; [|exact HCopy|left; congruence].
           rewrite HFieldLoads by (left; congruence). exact (HArray i v Hv).
        -- split.
           ++ intros chunk b ofs HV HR HI'. assert (Hbc : b <> bc) by (intro H; apply (HFresh b HV); congruence).
              erewrite Mem.load_free; [|exact HFree|left; exact Hbc].
              erewrite Mem.load_storebytes_other; [|exact HCopy|rewrite HLen; exact HR].
              rewrite HFieldLoads by (left; exact Hbc). rewrite HInitLoads by exact HI'.
              eapply Mem.load_alloc_unchanged; eauto.
           ++ split.
              ** intros b ofs kind p H. assert (Hbc : b <> bc).
                 { intro E. apply (HFresh b); [eapply Mem.perm_valid_block; exact H|congruence]. }
                 eapply Mem.perm_free_1; [exact HFree|left; exact Hbc|].
                 eapply Mem.perm_storebytes_1; [exact HCopy|apply HFieldPerm, HInitPerm].
                 eapply Mem.perm_alloc_1; eauto.
              ** intros b H. eapply Mem.valid_block_free_1; [exact HFree|].
                 eapply Mem.storebytes_valid_block_1; [exact HCopy|apply HFieldValid, HInitValid].
                 eapply Mem.valid_block_alloc; eauto.
Qed.
