(** Advancing a writable frame after one actual bit store. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Integers AST Memory.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Import Values Mem.
Local Open Scope Z_scope.

Lemma write_frame_at_shorter m bf base bw edge cursor count shorter :
  0 <= shorter <= count ->
  write_frame_at m bf base bw edge cursor count -> write_frame_at m bf base bw edge cursor shorter.
Proof.
  intros HS [HB [HF [HE [HC [HM [PD HW]]]]]].
  split; [exact HB|]. split; [exact HF|]. split; [exact HE|]. split; [lia|].
  split; [exact HM|]. split; [exact PD|]. intros i Hi; apply HW; lia.
Qed.

Lemma write_frame_at_after_bit m mf bf base bw edge cursor count w :
  0 <= count -> write_frame_at m bf base bw edge cursor (count + 1) ->
  frame_fields_at mf bf base bw edge (cursor - 1) ->
  Mem.load Mint64 mf bw (write_word_address edge cursor) = Some (Vlong w) ->
  loads_outside_ranges m mf bf (base + 8) (base + 16)
    bw (write_word_address edge cursor) (write_word_address edge cursor + 8) ->
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) ->
  write_frame_at mf bf base bw edge (cursor - 1) count.
Proof.
  intros Hcount [HB [HF [HE [HC [HM [PD HW]]]]]] HF' Hhead Houtside HP.
  assert (HV : forall chunk b ofs p, Mem.valid_access m chunk b ofs p -> Mem.valid_access mf chunk b ofs p).
  { intros chunk b ofs p [HR HA]. split; [|exact HA]. intros addr HA'. apply HP. apply HR; exact HA'. }
  split; [exact HB|]. split; [exact HF'|]. split; [exact HE|]. split; [lia|].
  split; [lia|]. split; [auto|].
  intros i Hi. cbn zeta.
  assert (Haddr : write_cell_address edge (cursor - 1) i = write_cell_address edge cursor (i + 1)).
  { unfold write_cell_address. replace (cursor - 1 - 1 - i) with (cursor - 1 - (i + 1)) by lia. reflexivity. }
  rewrite Haddr. destruct (HW (i + 1) ltac:(lia)) as [HA0 [HA [HDataSep [PW [old HL]]]]].
  split; [exact HA0|]. split; [exact HA|]. split; [exact HDataSep|]. split; [auto|].
  assert (Hcursorsep : bw <> bf \/ write_cell_address edge cursor (i + 1) + 8 <= base + 8 \/
      base + 16 <= write_cell_address edge cursor (i + 1)).
  { destruct HDataSep as [HD|[HD|HD]]; [left; congruence|right; left; lia|right; right; exact HD]. }
  destruct (Z.eq_dec (write_cell_address edge cursor (i + 1)) (write_word_address edge cursor)) as [Heq | Hneq].
  - rewrite Heq. exists w; exact Hhead.
  - exists old. rewrite Houtside; [exact HL|exact Hcursorsep|].
    right. unfold write_cell_address, write_word_address in Hneq |- *.
    change (edge + 8 * ((cursor - 1 - (i + 1)) / 64) + 8 <= edge + 8 * ((cursor - 1) / 64) \/
      edge + 8 * ((cursor - 1) / 64) + 8 <= edge + 8 * ((cursor - 1 - (i + 1)) / 64)).
    lia.
Qed.

Lemma write_layout_previous_inside edge cursor :
  1 < write_word_shift cursor ->
  write_word_shift (cursor - 1) = write_word_shift cursor - 1 /\
  write_word_address edge (cursor - 1) = write_word_address edge cursor.
Proof.
  intros HK. pose proof (Z.div_mod (cursor - 1) 64 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (cursor - 1) 64 ltac:(lia)) as HR.
  unfold write_word_shift in HK.
  assert (HQ : (cursor - 1 - 1) / 64 = (cursor - 1) / 64).
  { symmetry. apply Z.div_unique with (r := (cursor - 1) mod 64 - 1); lia. }
  assert (HM : (cursor - 1 - 1) mod 64 = (cursor - 1) mod 64 - 1).
  { symmetry. apply Z.mod_unique with (q := (cursor - 1) / 64); lia. }
  unfold write_word_shift, write_word_address. rewrite HQ, HM. split; [lia|reflexivity].
Qed.

Lemma write_layout_previous_boundary edge cursor :
  write_word_shift cursor = 1 ->
  write_word_shift (cursor - 1) = 64 /\
  write_word_address edge (cursor - 1) = write_word_address edge cursor - 8.
Proof.
  intros HK. pose proof (Z.div_mod (cursor - 1) 64 ltac:(lia)) as Hdiv.
  unfold write_word_shift in HK.
  assert (HQ : (cursor - 1 - 1) / 64 = (cursor - 1) / 64 - 1).
  { symmetry. apply Z.div_unique with (r := 63); lia. }
  assert (HM : (cursor - 1 - 1) mod 64 = 63).
  { symmetry. apply Z.mod_unique with (q := (cursor - 1) / 64 - 1); lia. }
  unfold write_word_shift, write_word_address. rewrite HQ, HM. split; lia.
Qed.
