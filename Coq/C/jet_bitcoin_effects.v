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
