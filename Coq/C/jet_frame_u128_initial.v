(** Shared initial allocation/copy lifecycle for public jets with a by-value
    source frame and a uint128 local. No allocation or copy is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Memory.
Require Import C.jet_frame_layout C.jet_frame_copy_layout C.jet_bitmachine_rep C.jet_multiply64_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition frame_u128_local_permissions m bl br :=
  Mem.range_perm m bl 0 16 Cur Freeable /\ Mem.range_perm m br 0 16 Cur Freeable.

Lemma frame_u128_permissions_preserved m mf bl br :
  (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) ->
  frame_u128_local_permissions m bl br -> frame_u128_local_permissions mf bl br.
Proof. intros HP [PL PR]. split; intros ofs Hrange; apply HP; [apply PL|apply PR]; exact Hrange. Qed.

Theorem allocate_frame_u128_locals m : exists ma mb bl br,
  Mem.alloc m 0 16 = (ma,bl) /\ Mem.alloc ma 0 16 = (mb,br) /\ bl <> br /\
  frame_u128_local_permissions mb bl br /\
  (forall bb, Mem.valid_block m bb -> bb <> bl /\ bb <> br) /\
  (forall chunk bb ofs, Mem.valid_block m bb -> Mem.load chunk mb bb ofs = Mem.load chunk m bb ofs) /\
  (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mb bb ofs kind p).
Proof.
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:HA.
  destruct (Mem.alloc ma 0 16) as [mb br] eqn:HB.
  assert (HV : forall bb, Mem.valid_block m bb -> Mem.valid_block ma bb).
  { intros bb H. eapply Mem.valid_block_alloc; eauto. }
  assert (Hbl : Mem.valid_block ma bl) by (eapply Mem.valid_new_block; exact HA).
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as FLA.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HB) as FRB.
  exists ma, mb, bl, br. split; [reflexivity|]. split; [exact HB|]. split; [congruence|]. split.
  - split; intros ofs Hrange.
    + eapply Mem.perm_alloc_1; [exact HB|]. eapply Mem.perm_alloc_2; eauto.
    + eapply Mem.perm_alloc_2; eauto.
  - split.
    + intros bb H. split; intro E; subst; eauto.
    + split.
      * intros chunk bb ofs H. erewrite Mem.load_alloc_unchanged; [|exact HB|apply HV; exact H].
        eapply Mem.load_alloc_unchanged; eauto.
      * intros bb ofs kind p H. eapply Mem.perm_alloc_1; [exact HB|]. eapply Mem.perm_alloc_1; eauto.
Qed.

Lemma frame_u128_slots_writable m bl br : frame_u128_local_permissions m bl br ->
  Mem.valid_access m Mint64 bl 8 Writable /\ Mem.valid_access m Mint64 br 0 Writable /\
  Mem.valid_access m Mint64 br 8 Writable.
Proof.
  intros [PL PR]. repeat split.
  - intros ofs Hrange. eapply Mem.perm_implies; [apply PL; cbn in Hrange; lia|constructor].
  - exists 1; reflexivity.
  - intros ofs Hrange. eapply Mem.perm_implies; [apply PR; cbn in Hrange; lia|constructor].
  - exists 0; reflexivity.
  - intros ofs Hrange. eapply Mem.perm_implies; [apply PR; cbn in Hrange; lia|constructor].
  - exists 1; reflexivity.
Qed.

Theorem initialize_frame_u128_input m bs sbase bi edge rc :
  frame_fields_at m bs sbase bi edge rc ->
  exists ma mb mc bl br bytes,
    Mem.alloc m 0 16 = (ma,bl) /\ Mem.alloc ma 0 16 = (mb,br) /\
    Mem.loadbytes mb bs sbase 16 = Some bytes /\ Mem.storebytes mb bl 0 bytes = Some mc /\
    bl <> br /\ frame_fields_at mc bl 0 bi edge rc /\ frame_u128_local_permissions mc bl br /\
    (forall bb, Mem.valid_block m bb -> bb <> bl /\ bb <> br) /\
    (forall chunk bb ofs, Mem.valid_block m bb -> Mem.load chunk mc bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mc bb ofs kind p).
Proof.
  intros [HE HO]. assert (HS : Mem.valid_block m bs) by (eapply load_valid_block; exact HE).
  destruct (allocate_frame_u128_locals m) as (ma & mb & bl & br & HA & HB & Hsep & Hlocals & Hfresh & Hload & Hperm).
  assert (HEb : Mem.load Mptr mb bs sbase = Some (Vptr bi (Ptrofs.repr edge))).
  { rewrite Hload by exact HS. exact HE. }
  assert (HOb : Mem.load Mint64 mb bs (sbase + 8) = Some (Vlong (Int64.repr rc))).
  { rewrite Hload by exact HS. exact HO. }
  destruct (frame_loadbytes_at mb bs sbase _ _ HEb HOb) as [bytes Hbytes].
  pose proof (Mem.loadbytes_length _ _ _ _ _ Hbytes) as Hlen.
  assert (PC : Mem.range_perm mb bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hlen. change (Mem.range_perm mb bl 0 16 Cur Writable).
    intros ofs Hrange. eapply Mem.perm_implies; [apply (proj1 Hlocals); exact Hrange|constructor]. }
  destruct (Mem.range_perm_storebytes mb bl 0 bytes PC) as [mc HC].
  destruct (frame_copy_fields_at mb mc bs sbase bl bytes _ _ Hbytes HC HEb HOb) as [HLE HLO].
  assert (HCopyPerm : forall bb ofs kind p, Mem.perm mb bb ofs kind p -> Mem.perm mc bb ofs kind p).
  { intros bb ofs kind p H. eapply Mem.perm_storebytes_1; eauto. }
  exists ma, mb, mc, bl, br, bytes. do 5 (split; [assumption|]). split; [split; assumption|]. split.
  - eapply frame_u128_permissions_preserved; eauto.
  - split; [exact Hfresh|]. split.
    + intros chunk bb ofs HV. destruct (Hfresh bb HV) as [Nl Nr].
      erewrite Mem.load_storebytes_other; [apply Hload; exact HV|exact HC|auto].
    + intros bb ofs kind p H. apply HCopyPerm, Hperm; exact H.
Qed.

Theorem free_frame_u128_locals m bl br : bl <> br -> frame_u128_local_permissions m bl br ->
  exists mf, Mem.free_list m (blocks_of_env C.jet_exec.ge0 (e_frame_u128 bl br)) = Some mf /\
    (forall chunk bb ofs, bb <> bl -> bb <> br -> Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, bb <> bl -> bb <> br -> Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros Hsep [PL PR]. destruct (Mem.range_perm_free m bl 0 16 PL) as [mi HL].
  assert (PRi : Mem.range_perm mi br 0 16 Cur Freeable).
  { intros ofs Hrange. eapply Mem.perm_free_1; [exact HL|left; congruence|apply PR; exact Hrange]. }
  destruct (Mem.range_perm_free mi br 0 16 PRi) as [mf HR].
  exists mf. split.
  - change (Mem.free_list m [(bl,0,16);(br,0,16)] = Some mf). cbn [Mem.free_list]. rewrite HL, HR; reflexivity.
  - split.
    + intros chunk bb ofs Nl Nr. erewrite Mem.load_free; [|exact HR|auto].
      erewrite Mem.load_free; [reflexivity|exact HL|auto].
    + split.
      * intros bb ofs kind p Nl Nr H. eapply Mem.perm_free_1; [exact HR|auto|].
        eapply Mem.perm_free_1; [exact HL|auto|exact H].
      * rewrite (Mem.nextblock_free _ _ _ _ _ HR), (Mem.nextblock_free _ _ _ _ _ HL). reflexivity.
Qed.
