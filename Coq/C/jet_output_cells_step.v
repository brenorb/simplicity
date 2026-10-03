(** Recover writable continuation after a nonempty encoded cell sequence,
    including the partially written boundary word. This is memory composition
    only; consumers must derive actual execution and its output observations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory.
Require Import Simplicity.BitMachine.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_encoding.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma output_cells_last_word m bw edge cursor (cells : list Cell) :
  (0 < length cells)%nat -> frame_output_cells_at m bw edge cursor cells ->
  exists w, Mem.load Mint64 m bw
    (edge + 8 * ((cursor - Z.of_nat (length cells)) / 64)) = Some (Vlong w).
Proof.
  intros HN HO.
  destruct (nth_error cells (length cells - 1)) as [c|] eqn:HE.
  - specialize (HO _ _ HE). destruct c as [bit|]; cbn [cell_matches] in HO.
    + destruct HO as [_ [w [HL _]]]. exists w.
      replace (cursor - 1 - Z.of_nat (length cells - 1)) with
        (cursor - Z.of_nat (length cells)) in HL by lia. exact HL.
    + destruct HO as [bit [_ [w [HL _]]]]. exists w.
      replace (cursor - 1 - Z.of_nat (length cells - 1)) with
        (cursor - Z.of_nat (length cells)) in HL by lia. exact HL.
  - apply nth_error_None in HE; lia.
Qed.

Theorem write_frame_at_after_cells m mf bf base bw edge cursor cells tail :
  (0 < length cells)%nat -> 0 <= tail ->
  write_frame_at m bf base bw edge cursor (Z.of_nat (length cells) + tail) ->
  frame_fields_at mf bf base bw edge (cursor - Z.of_nat (length cells)) ->
  frame_output_cells_at mf bw edge cursor cells ->
  loads_outside_ranges m mf bf (base + 8) (base + 16)
    bw (edge + 8 * ((cursor - Z.of_nat (length cells)) / 64)) (write_word_address edge cursor + 8) ->
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) ->
  write_frame_at mf bf base bw edge (cursor - Z.of_nat (length cells)) tail.
Proof.
  intros HN HT [HB [HF [HE [HC [HM [HD [PD HW]]]]]]] HF' HO HL HP.
  destruct (output_cells_last_word mf bw edge cursor cells HN HO) as [last HLast].
  assert (HV : forall chunk b ofs p, Mem.valid_access m chunk b ofs p ->
    Mem.valid_access mf chunk b ofs p).
  { intros chunk b ofs p [HR HA]. split; [|exact HA]. intros addr HA'; apply HP, HR; exact HA'. }
  split; [exact HB|]. split; [exact HF'|]. split; [exact HE|]. split; [lia|].
  split; [lia|]. split; [exact HD|]. split; [auto|]. intros i Hi.
  assert (Haddr : write_cell_address edge (cursor - Z.of_nat (length cells)) i =
    write_cell_address edge cursor (i + Z.of_nat (length cells))).
  { unfold write_cell_address; f_equal; f_equal; f_equal; lia. }
  rewrite Haddr. destruct (HW (i + Z.of_nat (length cells)) ltac:(lia)) as [HA0 [HA [PW [old Hold]]]].
  split; [exact HA0|]. split; [exact HA|]. split; [apply HV; exact PW|].
  destruct (Z.eq_dec (write_cell_address edge cursor (i + Z.of_nat (length cells)))
    (edge + 8 * ((cursor - Z.of_nat (length cells)) / 64))) as [Heq|Hneq].
  - rewrite Heq. exists last; exact HLast.
  - exists old. rewrite HL; [exact Hold|left; congruence|right; left].
    unfold write_cell_address in Hneq |- *.
    pose proof (Z.div_le_mono (cursor - 1 - (i + Z.of_nat (length cells)))
      (cursor - Z.of_nat (length cells)) 64 ltac:(lia) ltac:(lia)).
    change (size_chunk Mint64) with 8. lia.
Qed.
