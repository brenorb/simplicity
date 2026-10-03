(** Output effect of a call that writes [count] cells at [cursor]: the written
    cells, preservation of the earlier prefix word, the destination cursor,
    framing of every other load, and monotone permissions / valid blocks.
    [write_effect_seq] composes two successive writes into one effect for the
    concatenated cells; all helper contracts of the Bitcoin getters have this
    exact shape. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout.
Require Import C.jet_output_layout C.jet_output_sequence_step C.jet_encoding.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition write_effect (m mf : mem) (bf : block) (base : Z) (bw : block)
    (edge cursor count : Z) (cells : list Cell) : Prop :=
  frame_output_cells_at mf bw edge cursor cells /\
  write_prefix_at m mf bw edge cursor /\
  frame_fields_at mf bf base bw edge (cursor - count) /\
  loads_outside_ranges m mf bf (base + 8) (base + 16) bw
    (edge + 8 * ((cursor - count) / 64)) (write_word_address edge cursor + 8) /\
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block mf b).

Lemma write_effect_nil m bf base bw edge cursor :
  frame_fields_at m bf base bw edge cursor ->
  (exists old, Mem.load Mint64 m bw (write_word_address edge cursor) = Some (Vlong old)) ->
  write_effect m m bf base bw edge cursor 0 [].
Proof.
  intros HF [old HO]. split.
  { intros i c Hi. destruct i; discriminate. }
  split.
  { intros old' HL. exists old'. split; [exact HL|]. unfold word_outside_eq; intros; reflexivity. }
  split.
  { replace (cursor - 0) with cursor by lia. exact HF. }
  split; [unfold loads_outside_ranges; intros; reflexivity|]. split; auto.
Qed.

Lemma write_effect_seq m m1 m2 bf base bw edge cursor n1 n2 cells1 cells2 :
  Z.of_nat (length cells1) = n1 -> 0 <= n2 ->
  write_frame_at m bf base bw edge cursor (n1 + n2) ->
  write_effect m m1 bf base bw edge cursor n1 cells1 ->
  write_effect m1 m2 bf base bw edge (cursor - n1) n2 cells2 ->
  write_effect m m2 bf base bw edge cursor (n1 + n2) (cells1 ++ cells2).
Proof.
  intros HL1 Hn2 HFrame (O1 & P1 & F1 & L1 & Pm1 & V1) (O2 & P2 & F2 & L2 & Pm2 & V2).
  pose proof HFrame as [HB [HF [HE [HC [HM [HD [PD HW]]]]]]].
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
      * exact HD.
      * rewrite HL1. lia.
      * exact P2.
      * exact L2.
      * exact O1.
    + rewrite HL1. exact O2.
  - split.
    + eapply write_prefix_at_chain with (mi := m1) (next := cursor - n1)
        (low := edge + 8 * ((cursor - n1 - n2) / 64)).
      * exact HD.
      * lia.
      * exact P1.
      * exact P2.
      * exact L2.
    + split.
      * replace (cursor - (n1 + n2)) with (cursor - n1 - n2) by lia. exact F2.
      * split.
        -- intros chunk b ofs Hbf Hbw.
           replace (cursor - (n1 + n2)) with (cursor - n1 - n2) in Hbw by lia.
           assert (Hbw2 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - n1 - n2) / 64) \/
             write_word_address edge (cursor - n1) + 8 <= ofs).
           { destruct Hbw as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; lia]. }
           assert (Hbw1 : b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - n1) / 64) \/
             write_word_address edge cursor + 8 <= ofs).
           { destruct Hbw as [H|[H|H]]; [left; exact H|right; left; lia|right; right; exact H]. }
           rewrite (L2 chunk b ofs Hbf Hbw2). apply (L1 chunk b ofs Hbf Hbw1).
        -- split.
           ++ intros b ofs kind p HP. apply Pm2, Pm1; exact HP.
           ++ intros b HV. apply V2, V1; exact HV.
Qed.

(** After one write effect the remaining cells are still a writable frame. *)
Lemma write_frame_at_after_effect m mf bf base bw edge cursor n count cells :
  Z.of_nat (length cells) = n -> 0 <= count ->
  write_frame_at m bf base bw edge cursor (n + count) ->
  write_effect m mf bf base bw edge cursor n cells ->
  write_frame_at mf bf base bw edge (cursor - n) count.
Proof.
  intros HL Hcount HF (O & P & F & L & Pm & V).
  pose proof HF as [HB [HFl [HE [HC [HM [HD [PD HW]]]]]]].
  assert (Hn : 0 <= n) by (rewrite <- HL; lia).
  assert (HV : forall chunk b ofs p, Mem.valid_access m chunk b ofs p ->
    Mem.valid_access mf chunk b ofs p).
  { intros chunk b ofs p [HR HA]. split; [|exact HA]. intros addr HA'. apply Pm. apply HR; exact HA'. }
  split; [exact HB|]. split; [exact F|]. split; [exact HE|]. split; [lia|]. split; [lia|].
  split; [exact HD|]. split; [auto|].
  intros i Hi. cbn zeta.
  assert (Haddr : write_cell_address edge (cursor - n) i = write_cell_address edge cursor (i + n)).
  { unfold write_cell_address. replace (cursor - n - 1 - i) with (cursor - 1 - (i + n)) by lia. reflexivity. }
  rewrite Haddr. destruct (HW (i + n) ltac:(lia)) as [HA0 [HA [PW [old Hold]]]].
  split; [exact HA0|]. split; [exact HA|]. split; [auto|].
  set (addr := write_cell_address edge cursor (i + n)) in *.
  assert (Haddr_def : addr = edge + 8 * ((cursor - 1 - (i + n)) / 64)) by reflexivity.
  assert (Hmono : (cursor - 1 - (i + n)) / 64 <= (cursor - n) / 64)
    by (apply Z.div_le_mono; lia).
  destruct (Z_le_dec (addr + 8) (edge + 8 * ((cursor - n) / 64))) as [Hlow|Hnl].
  - exists old. rewrite L; [exact Hold|left; exact (not_eq_sym HD)|right; left; exact Hlow].
  - destruct (Z_le_dec (write_word_address edge cursor + 8) addr) as [Hhigh|Hnh].
    + exists old. rewrite L; [exact Hold|left; exact (not_eq_sym HD)|right; right; exact Hhigh].
    + (* addr lies in the written word range *)
      unfold write_word_address in Hnh.
      assert (Hk : (cursor - 1 - (i + n)) / 64 = (cursor - n) / 64) by lia.
      destruct (Z.eq_dec n 0) as [Hn0|Hn1].
      * destruct (write_frame_at_head m bf base bw edge cursor (n + count) ltac:(lia) HF)
          as [_ [_ [_ [w0 Hw0]]]].
        destruct (P w0 Hw0) as [w [Hw _]]. exists w.
        replace addr with (write_word_address edge cursor); [exact Hw|].
        unfold write_word_address. rewrite Haddr_def.
        pose proof (Z.div_le_mono (cursor - 1) (cursor - n) 64 ltac:(lia) ltac:(lia)) as Hge.
        lia.
      * assert (HlenN : (Z.to_nat (n - 1) < length cells)%nat) by lia.
        destruct (nth_error cells (Z.to_nat (n - 1))) as [c|] eqn:Hc;
          [|apply nth_error_None in Hc; lia].
        specialize (O (Z.to_nat (n - 1)) c Hc).
        replace (cursor - 1 - Z.of_nat (Z.to_nat (n - 1))) with (cursor - n) in O by lia.
        assert (Hbit : exists bit, frame_output_bit_at mf bw edge (cursor - n) bit).
        { destruct c as [bit|]; cbn [cell_matches] in O; [exists bit; exact O|exact O]. }
        destruct Hbit as [bit [_ [w [Hw _]]]]. exists w.
        replace addr with (edge + 8 * ((cursor - n) / 64)); [exact Hw|].
        rewrite Haddr_def, Hk. reflexivity.
Qed.

(** Lifting an effect across a step that changes only one private block [bl]
    (the local copy of the source frame, whose cursor a reader advances). *)
Lemma write_effect_lift m1 m2 mf bl bf base bw edge cursor n cells :
  bl <> bf -> bl <> bw ->
  (forall chunk b ofs, b <> bl -> Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs) ->
  (forall b ofs kind p, Mem.perm m1 b ofs kind p -> Mem.perm m2 b ofs kind p) ->
  (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b) ->
  write_effect m2 mf bf base bw edge cursor n cells ->
  frame_output_cells_at mf bw edge cursor cells /\
  write_prefix_at m1 mf bw edge cursor /\
  frame_fields_at mf bf base bw edge (cursor - n) /\
  (forall chunk b ofs, b <> bl ->
    (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
    (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - n) / 64) \/
      write_word_address edge cursor + 8 <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m1 b ofs) /\
  (forall b ofs kind p, Mem.perm m1 b ofs kind p -> Mem.perm mf b ofs kind p) /\
  (forall b, Mem.valid_block m1 b -> Mem.valid_block mf b).
Proof.
  intros Hf Hw HL HP HV (O & P & F & L & Pm & V).
  split; [exact O|]. split.
  - eapply write_prefix_at_preserved with (mr := m2) (me := mf).
    + intros ofs w Hl. rewrite HL by exact (not_eq_sym Hw). exact Hl.
    + intros ofs w Hl. exact Hl.
    + exact P.
  - split; [exact F|]. split.
    + intros chunk b ofs Hb H1 H2. rewrite (L chunk b ofs H1 H2). apply HL; exact Hb.
    + split; [intros b ofs kind p H; apply Pm, HP; exact H|].
      intros b H; apply V, HV; exact H.
Qed.
