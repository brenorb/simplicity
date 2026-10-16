(** Compose a presence bit, initialization of a fresh local object, and a
    payload write; discharge the local memory changes through the actual free. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_sequence_step.
Require Import C.jet_elements_effects C.jet_elements_wrapper.
Require Import C.jet_bitmachine_rep.
Require Import C.jet_encoding.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma local_alloc_load_other m ma bc sz chunk b ofs :
  Mem.alloc m 0 sz = (ma, bc) -> b <> bc ->
  Mem.load chunk ma b ofs = Mem.load chunk m b ofs.
Proof.
  intros A Hneq. destruct (Mem.load chunk ma b ofs) as [v|] eqn:HL.
  - pose proof (Mem.valid_access_alloc_inv _ _ _ _ _ A _ _ _ _
      (Mem.load_valid_access _ _ _ _ _ HL)) as HV.
    destruct (eq_block b bc); [congruence|].
    rewrite <- HL. eapply Mem.load_alloc_unchanged; [exact A|].
    eapply Mem.valid_access_valid_block, Mem.valid_access_implies; [exact HV|constructor].
  - destruct (Mem.load chunk m b ofs) as [v|] eqn:HM; [|reflexivity].
    pose proof (Mem.load_alloc_other _ _ _ _ _ A _ _ _ _ HM). congruence.
Qed.

Lemma local_alloc_load_outside m ma bc sz chunk ofs :
  Mem.alloc m 0 sz = (ma, bc) ->
  ofs + size_chunk chunk <= 0 \/ sz <= ofs -> Mem.load chunk ma bc ofs = None.
Proof.
  intros A HD. destruct (Mem.load chunk ma bc ofs) as [v|] eqn:HL; [|reflexivity].
  pose proof (Mem.valid_access_alloc_inv _ _ _ _ _ A _ _ _ _
    (Mem.load_valid_access _ _ _ _ _ HL)) as HV.
  destruct (eq_block bc bc); [|congruence].
  pose proof (size_chunk_pos chunk). destruct HV as [H0 [HM _]]. exfalso; lia.
Qed.

Lemma local_free_load_restored m ma me mf bc sz :
  0 < sz -> Mem.alloc m 0 sz = (ma, bc) -> Mem.free me bc 0 sz = Some mf ->
  (forall chunk ofs, ofs + size_chunk chunk <= 0 \/ sz <= ofs ->
     Mem.load chunk me bc ofs = Mem.load chunk ma bc ofs) ->
  forall chunk ofs, Mem.load chunk mf bc ofs = Mem.load chunk m bc ofs.
Proof.
  intros HS A F HO chunk ofs.
  assert (HM : Mem.load chunk m bc ofs = None).
  { destruct (Mem.load chunk m bc ofs) as [v|] eqn:HL; [|reflexivity].
    exfalso. apply (Mem.fresh_block_alloc _ _ _ _ _ A).
    eapply load_valid_block; exact HL. }
  rewrite HM. destruct (Mem.load chunk mf bc ofs) as [v|] eqn:HL; [|reflexivity].
  pose proof (Mem.valid_access_free_inv_2 _ _ _ _ _ F _ _ _
    (Mem.load_valid_access _ _ _ _ _ HL)) as HD.
  assert (HOutside : ofs + size_chunk chunk <= 0 \/ sz <= ofs) by lia.
  pose proof (Mem.load_free_2 _ _ _ _ _ F _ _ _ _ HL) as HB.
  rewrite HO in HB by exact HOutside.
  rewrite (local_alloc_load_outside _ _ _ _ _ _ A HOutside) in HB. discriminate.
Qed.

Theorem write_effect_local_alloc m ma mb mi me mf bc sz bf base bw edge cursor n bit cells :
  0 < sz -> 0 <= n ->
  Mem.alloc m 0 sz = (ma, bc) -> Mem.free me bc 0 sz = Some mf ->
  write_frame_at m bf base bw edge cursor (1 + n) ->
  write_effect ma mb bf base bw edge cursor 1 [Some bit] ->
  (forall chunk b ofs, b <> bc \/ ofs + size_chunk chunk <= 0 \/ sz <= ofs ->
     Mem.load chunk mi b ofs = Mem.load chunk mb b ofs) ->
  (forall b ofs kind p, Mem.perm mb b ofs kind p -> Mem.perm mi b ofs kind p) ->
  (forall b, Mem.valid_block mb b -> Mem.valid_block mi b) ->
  write_effect mi me bf base bw edge (cursor - 1) n cells ->
  write_effect m mf bf base bw edge cursor (1 + n) ([Some bit] ++ cells).
Proof.
  intros HS Hn A F HF W1 HI PI VI W2.
  pose proof W1 as (O1 & P1 & Fields1 & L1 & PM1 & V1).
  pose proof W2 as (O2 & P2 & Fields2 & L2 & PM2 & V2).
  pose proof HF as [_ [[HDE HDO] _]].
  destruct (write_frame_at_head m bf base bw edge cursor (1 + n) ltac:(lia) HF)
    as (_ & _ & _ & old & HOld).
  assert (Fresh : forall b, Mem.valid_block m b -> bc <> b).
  { intros b HV HEq. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ A HV). }
  assert (Hcd : bc <> bf).
  { apply Fresh. eapply load_valid_block; exact HDE. }
  assert (Hcw : bc <> bw).
  { apply Fresh. eapply load_valid_block; exact HOld. }
  assert (HFa : write_frame_at ma bf base bw edge cursor (1 + n)).
  { eapply write_frame_at_preserved with (m := m).
    - intros chunk b ofs v _ HL. eapply Mem.load_alloc_other; eauto.
    - intros; eapply Mem.perm_alloc_1; eauto.
    - exact HF. }
  pose proof HFa as [_ [_ [_ [HC _]]]].
  assert (KI : forall ofs w, Mem.load Mint64 mb bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mi bw ofs = Some (Vlong w)).
  { intros ofs w HL. rewrite HI; [exact HL|left; congruence]. }
  assert (KFree : forall chunk b ofs, b <> bc -> Mem.load chunk mf b ofs = Mem.load chunk me b ofs).
  { intros; eapply Mem.load_free; [exact F|left; assumption]. }
  assert (Output : frame_output_cells_at me bw edge cursor ([Some bit] ++ cells)).
  { apply frame_output_cells_at_app. split.
    - eapply frame_output_cells_prefix_preserved with (m := mi) (bf := bf) (base := base)
        (cursor := cursor - 1) (low := edge + 8 * ((cursor - 1 - n) / 64)).
      + intros i Hi. pose proof HFa as [_ [_ [_ [_ [_ [_ HW]]]]]].
        destruct (HW (Z.of_nat i) ltac:(cbn [length] in Hi; lia)) as (_ & _ & HD & _). exact HD.
      + cbn [length]. lia.
      + exact P2.
      + exact L2.
      + eapply frame_output_cells_load_preserved; [exact KI|exact O1].
    - cbn [length]. exact O2. }
  assert (P1I : write_prefix_at ma mi bw edge cursor).
  { eapply write_prefix_at_preserved with (mr := ma) (me := mb);
      [intros; assumption|exact KI|exact P1]. }
  assert (Prefix : write_prefix_at ma me bw edge cursor).
  { eapply write_prefix_at_chain with (mi := mi) (bf := bf) (base := base)
      (next := cursor - 1) (low := edge + 8 * ((cursor - 1 - n) / 64));
      [apply (write_frame_at_head_separate ma bf base bw edge cursor (1 + n) ltac:(lia) HFa)|lia|
       exact P1I|exact P2|exact L2]. }
  assert (KLocal : forall chunk ofs, ofs + size_chunk chunk <= 0 \/ sz <= ofs ->
    Mem.load chunk me bc ofs = Mem.load chunk ma bc ofs).
  { intros chunk ofs HD. rewrite (L2 chunk bc ofs ltac:(left; exact Hcd) ltac:(left; exact Hcw)).
    rewrite HI by tauto. apply L1; [left; exact Hcd|left; exact Hcw]. }
  assert (Kbc : forall chunk ofs, Mem.load chunk mf bc ofs = Mem.load chunk m bc ofs)
    by (eapply local_free_load_restored; eauto).
  split.
  - eapply frame_output_cells_load_preserved; [|exact Output].
    intros ofs w HL. rewrite KFree; [exact HL|congruence].
  - split.
    + eapply write_prefix_at_preserved with (mr := ma) (me := me).
      * intros; eapply Mem.load_alloc_other; eauto.
      * intros ofs w HL. rewrite KFree; [exact HL|congruence].
      * exact Prefix.
    + split.
      * destruct Fields2 as [HEdge HCursor]. split; rewrite KFree by congruence;
          replace (cursor - (1 + n)) with (cursor - 1 - n) by lia; assumption.
      * split.
        -- intros chunk b ofs HD HW. destruct (eq_block b bc) as [Eq|Hneq]; [subst b; apply Kbc|].
           rewrite KFree by exact Hneq.
           assert (HW2 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - 1 - n) / 64) \/
             write_word_address edge (cursor - 1) + 8 <= ofs).
           { destruct HW as [H|[H|H]]; [left; exact H|right; left; replace (cursor - 1 - n) with (cursor - (1+n)) by lia; exact H|].
             right; right. unfold write_word_address in *. pose proof (Z.div_le_mono (cursor - 1 - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia. }
           rewrite (L2 chunk b ofs HD HW2). rewrite HI by (left; exact Hneq).
           assert (HW1 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - 1) / 64) \/
             write_word_address edge cursor + 8 <= ofs).
           { destruct HW as [H|[H|H]]; [left; exact H| |right; right; exact H].
             right; left. pose proof (Z.div_le_mono (cursor - (1+n)) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia. }
           rewrite (L1 chunk b ofs HD HW1). eapply local_alloc_load_other; eauto.
        -- split.
           ++ intros b ofs kind p HP. eapply Mem.perm_free_1; [exact F| |].
              ** left. intro Eq; subst b. apply (Fresh bc (Mem.perm_valid_block _ _ _ _ _ HP)); reflexivity.
              ** apply PM2, PI, PM1. eapply Mem.perm_alloc_1; eauto.
           ++ intros b HV. eapply Mem.valid_block_free_1; [exact F|].
              apply V2, VI, V1. eapply Mem.valid_block_alloc; eauto.
Qed.
