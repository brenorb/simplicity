(** Write effects up to one private block.

    A static helper with an addressable local allocates a block, may store
    into it between output writes, and frees it on return.  The effect
    relation [write_effect] compares all loads outside the output ranges,
    so it cannot hold across such stores; [write_effect_x bl] is the same
    relation with the loads of [bl] left unconstrained.  It composes like
    [write_effect], is stable under changes confined to [bl], and closes to
    a plain [write_effect] around the allocation and release of [bl],
    provided the execution adds no permission to [bl]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_sequence_step C.jet_encoding.
Require Import C.jet_elements_effects C.jet_elements_wrapper.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition write_effect_x (bl : block) (m mf : mem) (bf : block) (base : Z) (bw : block)
    (edge cursor count : Z) (cells : list Cell) : Prop :=
  frame_output_cells_at mf bw edge cursor cells /\
  write_prefix_at m mf bw edge cursor /\
  frame_fields_at mf bf base bw edge (cursor - count) /\
  (forall chunk b ofs, b <> bl ->
    (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
    (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - count) / 64) \/
      write_word_address edge cursor + 8 <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block mf b).

Lemma write_effect_to_x bl m mf bf base bw edge cursor count cells :
  write_effect m mf bf base bw edge cursor count cells ->
  write_effect_x bl m mf bf base bw edge cursor count cells.
Proof.
  intros (O & P & F & L & Pm & V). repeat (split; [assumption|]). split; [|split; assumption].
  intros chunk b ofs _ H1 H2. exact (L chunk b ofs H1 H2).
Qed.

(** A change confined to [bl] after the effect. *)
Lemma write_effect_x_step bl m m1 m1' bf base bw edge cursor count cells :
  bl <> bf -> bl <> bw ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk m1' b ofs = Mem.load chunk m1 b ofs) ->
  (forall b ofs kind p, Mem.perm m1 b ofs kind p -> Mem.perm m1' b ofs kind p) ->
  (forall b, Mem.valid_block m1 b -> Mem.valid_block m1' b) ->
  write_effect_x bl m m1 bf base bw edge cursor count cells ->
  write_effect_x bl m m1' bf base bw edge cursor count cells.
Proof.
  intros Hf Hw HL HP HV (O & P & F & L & Pm & V).
  split.
  { eapply frame_output_cells_load_preserved; [|exact O].
    intros ofs w Hl. rewrite HL by exact (not_eq_sym Hw). exact Hl. }
  split.
  { eapply write_prefix_at_preserved with (mr := m) (me := m1); [intros ofs w Hl; exact Hl| |exact P].
    intros ofs w Hl. rewrite HL by exact (not_eq_sym Hw). exact Hl. }
  split.
  { destruct F as [HE HC]. split; rewrite HL by exact (not_eq_sym Hf); assumption. }
  split.
  { intros chunk b ofs Hb H1 H2. rewrite HL by exact Hb. exact (L chunk b ofs Hb H1 H2). }
  split; [intros b ofs kind p H; exact (HP _ _ _ _ (Pm _ _ _ _ H))|].
  intros b H. exact (HV _ (V _ H)).
Qed.

Lemma write_effect_x_seq bl m m1 m2 bf base bw edge cursor n1 n2 cells1 cells2 :
  Z.of_nat (length cells1) = n1 -> 0 <= n2 ->
  write_frame_at m bf base bw edge cursor (n1 + n2) ->
  write_effect_x bl m m1 bf base bw edge cursor n1 cells1 ->
  write_effect m1 m2 bf base bw edge (cursor - n1) n2 cells2 ->
  write_effect_x bl m m2 bf base bw edge cursor (n1 + n2) (cells1 ++ cells2).
Proof.
  intros HL1 Hn2 HFrame (O1 & P1 & F1 & L1 & Pm1 & V1) (O2 & P2 & F2 & L2 & Pm2 & V2).
  pose proof HFrame as [HB [HF [HE [HC [HM [PD HW]]]]]].
  assert (Hn1 : 0 <= n1) by (rewrite <- HL1; lia).
  assert (Hdiv1 : (cursor - n1 - n2) / 64 <= (cursor - n1) / 64)
    by (apply Z.div_le_mono; lia).
  assert (Hdiv2 : write_word_address edge (cursor - n1) <= write_word_address edge cursor).
  { unfold write_word_address. pose proof (Z.div_le_mono (cursor - n1 - 1) (cursor - 1) 64
      ltac:(lia) ltac:(lia)). lia. }
  split.
  - apply frame_output_cells_at_app. split.
    + eapply frame_output_cells_prefix_preserved with (m := m1) (bf := bf) (base := base)
        (cursor := cursor - n1) (low := edge + 8 * ((cursor - n1 - n2) / 64)).
      * intros i Hi. destruct (HW (Z.of_nat i) ltac:(lia)) as (_ & _ & HD & _). exact HD.
      * rewrite HL1. lia.
      * exact P2.
      * exact L2.
      * exact O1.
    + rewrite HL1. exact O2.
  - split.
    + destruct (Z.eq_dec (n1 + n2) 0) as [Hzero|Hpositive].
      * assert (Hn10 : n1 = 0) by lia. assert (Hn20 : n2 = 0) by lia.
        replace (cursor - n1) with cursor in P2 by lia.
        intros old Hold. destruct (P1 old Hold) as (middle & Hmiddle & Hsame).
        destruct (P2 middle Hmiddle) as (last & Hlast & Hnew).
        exists last. split; [exact Hlast|].
        intros i Hi Houtside. rewrite Hnew; [apply Hsame; assumption|exact Hi|exact Houtside].
      * eapply write_prefix_at_chain with (mi := m1) (next := cursor - n1)
        (low := edge + 8 * ((cursor - n1 - n2) / 64)).
        -- exact (write_frame_at_head_separate m bf base bw edge cursor
             (n1 + n2) ltac:(lia) HFrame).
        -- lia.
        -- exact P1.
        -- exact P2.
        -- exact L2.
    + split.
      * replace (cursor - (n1 + n2)) with (cursor - n1 - n2) by lia. exact F2.
      * split.
        -- intros chunk b ofs Hbl Hbf Hbw.
           replace (cursor - (n1 + n2)) with (cursor - n1 - n2) in Hbw by lia.
           assert (Hbw2 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - n1 - n2) / 64) \/
             write_word_address edge (cursor - n1) + 8 <= ofs).
           { destruct Hbw as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; lia]. }
           assert (Hbw1 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - n1) / 64) \/
             write_word_address edge cursor + 8 <= ofs).
           { destruct Hbw as [H|[H|H]]; [left; exact H|right; left; lia|right; right; exact H]. }
           rewrite (L2 chunk b ofs Hbf Hbw2). apply (L1 chunk b ofs Hbl Hbf Hbw1).
        -- split.
           ++ intros b ofs kind p HP. apply Pm2, Pm1; exact HP.
           ++ intros b HV. apply V2, V1; exact HV.
Qed.

(** Around the allocation and release of the private block. *)
Lemma write_effect_x_close bl lo hi m m1 me mf bf base bw edge cursor count cells :
  Mem.alloc m lo hi = (m1, bl) -> bl <> bf -> bl <> bw ->
  write_effect_x bl m1 me bf base bw edge cursor count cells ->
  (forall ofs kind p, Mem.perm me bl ofs kind p -> lo <= ofs < hi) ->
  Mem.free me bl lo hi = Some mf ->
  write_effect m mf bf base bw edge cursor count cells.
Proof.
  intros HA Hf Hw (O & P & F & L & Pm & V) HPerm HF.
  assert (Hfresh : ~ Mem.valid_block m bl) by exact (Mem.fresh_block_alloc _ _ _ _ _ HA).
  assert (HFl : forall chunk b ofs, b <> bl -> Mem.load chunk mf b ofs = Mem.load chunk me b ofs).
  { intros chunk b ofs Hb. eapply Mem.load_free; [exact HF|left; exact Hb]. }
  assert (HAl : forall chunk b ofs, b <> bl -> Mem.load chunk m1 b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hb. destruct (Mem.load chunk m b ofs) as [v|] eqn:Hl.
    - eapply Mem.load_alloc_other; eauto.
    - destruct (Mem.load chunk m1 b ofs) as [v|] eqn:Hl1; [|reflexivity].
      exfalso. pose proof (Mem.load_valid_access _ _ _ _ _ Hl1) as [Hr Hal].
      assert (Hv : Mem.valid_access m chunk b ofs Readable).
      { split; [|exact Hal]. intros o Ho. eapply Mem.perm_alloc_4; [exact HA|exact (Hr o Ho)|exact Hb]. }
      destruct (Mem.valid_access_load _ _ _ _ Hv) as [v' Hv']. congruence. }
  split.
  { eapply frame_output_cells_load_preserved; [|exact O].
    intros ofs w Hl. rewrite HFl by exact (not_eq_sym Hw). exact Hl. }
  split.
  { eapply write_prefix_at_preserved with (mr := m1) (me := me); [| |exact P].
    - intros ofs w Hl. rewrite HAl by exact (not_eq_sym Hw). exact Hl.
    - intros ofs w Hl. rewrite HFl by exact (not_eq_sym Hw). exact Hl. }
  split.
  { destruct F as [HE HC]. split; rewrite HFl by exact (not_eq_sym Hf); assumption. }
  split.
  { intros chunk b ofs H1 H2. destruct (peq b bl) as [->|Hb].
    - assert (N1 : Mem.load chunk m bl ofs = None).
      { destruct (Mem.load chunk m bl ofs) as [v|] eqn:Hl; [|reflexivity]. exfalso. apply Hfresh.
        pose proof (Mem.load_valid_access _ _ _ _ _ Hl) as [Hr _].
        eapply Mem.perm_valid_block. apply (Hr ofs). pose proof (size_chunk_pos chunk). lia. }
      assert (N2 : Mem.load chunk mf bl ofs = None).
      { destruct (Mem.load chunk mf bl ofs) as [v|] eqn:Hl; [|reflexivity]. exfalso.
        pose proof (Mem.load_valid_access _ _ _ _ _ Hl) as [Hr _].
        assert (Hp : Mem.perm mf bl ofs Cur Readable)
          by (apply (Hr ofs); pose proof (size_chunk_pos chunk); lia).
        pose proof (Mem.perm_free_3 _ _ _ _ _ HF _ _ _ _ Hp) as Hpe.
        exact (Mem.perm_free_2 _ _ _ _ _ HF ofs Cur Readable (HPerm _ _ _ Hpe) Hp). }
      rewrite N1, N2. reflexivity.
    - rewrite HFl by exact Hb. rewrite (L chunk b ofs Hb H1 H2). exact (HAl chunk b ofs Hb). }
  split.
  { intros b ofs kind p H.
    assert (Hb : b <> bl) by (intro; subst; apply Hfresh; eapply Mem.perm_valid_block; exact H).
    eapply Mem.perm_free_1; [exact HF|left; exact Hb|].
    apply Pm. eapply Mem.perm_alloc_1; eauto. }
  intros b H. eapply Mem.valid_block_free_1; [exact HF|]. apply V. eapply Mem.valid_block_alloc; eauto.
Qed.
