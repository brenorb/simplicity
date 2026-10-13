(** The frame premises of the shared jet contracts are constructible.

    The local contracts ([jet_local_spec], [jet_separated_local_spec] and the
    SHA-unit shapes) take a represented input frame and a writable output
    frame as premises.  These are legitimate input requirements only if a
    caller can establish them for *every* input of the jet's type.  This
    module proves that it can: from an arbitrary memory, four allocations and
    aligned 64-bit stores into the fresh blocks yield a memory in which

    - an input frame record points at a buffer holding any given cell list
      (in particular [encode a] for any [a : A]) at read cursor 0,
    - an output frame record points at an initialized, writable buffer for any
      requested number of cells,
    - the copy-separation premise of [jet_separated_local_spec] holds,

    and every load from a block of the original memory is unchanged.  The
    only side conditions are the representability bounds already present in
    the contracts (sizes at most [Int64.max_unsigned]).  Hence no accepted
    frame-only contract is vacuous on any input, and none of its frame
    premises excludes a value of its input type. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Zbits Integers AST Memory Values.
Require Import Simplicity.BitMachine.
Require Import C.jet_word_repr C.jet_frame_spec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

(** ** Packing bits into a machine word *)

Fixpoint z_of_bits (n : nat) (f : Z -> bool) (i : Z) : Z :=
  match n with
  | O => 0
  | S n' => Zshiftin (f i) (z_of_bits n' f (i + 1))
  end.

Lemma z_of_bits_testbit n f : forall i j,
  0 <= j < Z.of_nat n -> Z.testbit (z_of_bits n f i) j = f (i + j).
Proof.
  induction n as [|n IH]; intros i j Hj; [exfalso; cbn in Hj; lia|].
  cbn [z_of_bits]. rewrite Ztestbit_shiftin by lia.
  destruct (zeq j 0) as [->|Hne]; [rewrite Z.add_0_r; reflexivity|].
  rewrite IH by lia. f_equal. lia.
Qed.

Lemma z_of_bits_range n f : forall i, 0 <= z_of_bits n f i < two_power_nat n.
Proof.
  induction n as [|n IH]; intros i;
    [cbn [z_of_bits]; change (two_power_nat 0) with 1; lia|].
  cbn [z_of_bits]. rewrite Zshiftin_spec, two_power_nat_S.
  specialize (IH (i + 1)). destruct (f i); lia.
Qed.

Definition packed_word (f : Z -> bool) : int64 := Int64.repr (z_of_bits 64 f 0).

Lemma packed_word_testbit f j :
  0 <= j < 64 -> Z.testbit (Int64.unsigned (packed_word f)) j = f j.
Proof.
  intros Hj. unfold packed_word.
  pose proof (z_of_bits_range 64 f 0) as HR.
  change (two_power_nat 64) with Int64.modulus in HR.
  rewrite Int64.unsigned_repr by (unfold Int64.max_unsigned; lia).
  rewrite z_of_bits_testbit by (cbn; lia). reflexivity.
Qed.

(** ** A fresh block holding a run of 64-bit values *)

Lemma store_word_run : forall (vs : list val) m b base,
  (forall i, (i < length vs)%nat ->
    Mem.valid_access m Mint64 b (base + 8 * Z.of_nat i) Writable) ->
  exists m',
    (forall i v, nth_error vs i = Some v ->
      Mem.load Mint64 m' b (base + 8 * Z.of_nat i) = Some (Val.load_result Mint64 v)) /\
    (forall chunk b' ofs, b' <> b \/ ofs + size_chunk chunk <= base ->
      Mem.load chunk m' b' ofs = Mem.load chunk m b' ofs) /\
    (forall b' ofs k p, Mem.perm m' b' ofs k p <-> Mem.perm m b' ofs k p) /\
    (forall b', Mem.valid_block m' b' <-> Mem.valid_block m b').
Proof.
  induction vs as [|v vs IH]; intros m b base HVA.
  - exists m. split; [intros [|i] v H; discriminate H|]. repeat split; tauto.
  - pose proof (HVA 0%nat ltac:(cbn; lia)) as HV0.
    rewrite Z.mul_0_r, Z.add_0_r in HV0.
    destruct (Mem.valid_access_store m Mint64 b base v HV0) as [m1 HS].
    destruct (IH m1 b (base + 8)) as (m' & HL & HO & HP & HVB).
    { intros i Hi. eapply Mem.store_valid_access_1; [exact HS|].
      replace (base + 8 + 8 * Z.of_nat i) with (base + 8 * Z.of_nat (S i)) by lia.
      apply HVA. cbn [length]. lia. }
    exists m'. split; [|split; [|split]].
    + intros [|i] w Hw.
      * injection Hw as <-. rewrite Z.mul_0_r, Z.add_0_r.
        rewrite HO by (right; change (size_chunk Mint64) with 8; lia).
        exact (Mem.load_store_same _ _ _ _ _ _ HS).
      * replace (base + 8 * Z.of_nat (S i)) with (base + 8 + 8 * Z.of_nat i) by lia.
        exact (HL i w Hw).
    + intros chunk b' ofs Hcond.
      rewrite HO by (destruct Hcond as [H|H]; [left; exact H|right; lia]).
      eapply Mem.load_store_other; [exact HS|].
      destruct Hcond as [H|H]; [left; exact H|right; left; exact H].
    + intros b' ofs k p. rewrite HP. split; intros H.
      * eapply Mem.perm_store_2; eauto.
      * eapply Mem.perm_store_1; eauto.
    + intros b'. rewrite HVB. split; intros H.
      * eapply Mem.store_valid_block_2; eauto.
      * eapply Mem.store_valid_block_1; eauto.
Qed.

Lemma alloc_word_run (m : mem) (vs : list val) :
  exists m' b,
    ~ Mem.valid_block m b /\ Mem.valid_block m' b /\
    (forall i v, nth_error vs i = Some v ->
      Mem.load Mint64 m' b (8 * Z.of_nat i) = Some (Val.load_result Mint64 v)) /\
    (forall i, (i < length vs)%nat ->
      Mem.valid_access m' Mint64 b (8 * Z.of_nat i) Writable) /\
    Mem.range_perm m' b 0 (8 * Z.of_nat (length vs)) Cur Freeable /\
    (forall chunk b' ofs, Mem.valid_block m b' ->
      Mem.load chunk m' b' ofs = Mem.load chunk m b' ofs) /\
    (forall chunk b' ofs p, Mem.valid_block m b' ->
      Mem.valid_access m chunk b' ofs p -> Mem.valid_access m' chunk b' ofs p) /\
    (forall b' ofs k p, Mem.valid_block m b' ->
      Mem.perm m' b' ofs k p -> Mem.perm m b' ofs k p) /\
    (forall b', Mem.valid_block m b' -> Mem.valid_block m' b').
Proof.
  destruct (Mem.alloc m 0 (8 * Z.of_nat (length vs))) as [m1 b] eqn:HA.
  assert (HVA : forall i, (i < length vs)%nat ->
      Mem.valid_access m1 Mint64 b (0 + 8 * Z.of_nat i) Writable).
  { intros i Hi. eapply Mem.valid_access_implies with (p1 := Freeable); [|constructor].
    eapply Mem.valid_access_alloc_same; [exact HA|lia|change (size_chunk Mint64) with 8; lia|].
    apply Z.divide_add_r; [apply Z.divide_0_r|].
    change (align_chunk Mint64) with 8. apply Z.divide_factor_l. }
  destruct (store_word_run vs m1 b 0 HVA) as (m' & HL & HO & HP & HVB).
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ HA) as HFresh.
  exists m', b. split; [exact HFresh|]. split.
  { apply HVB. eapply Mem.valid_new_block; exact HA. }
  split; [intros i v H; exact (HL i v H)|]. split.
  { intros i Hi. destruct (HVA i Hi) as [HR HAl]. split; [|exact HAl].
    intros ofs Hofs. apply HP. apply HR. exact Hofs. }
  split.
  { intros ofs Hofs. apply HP. eapply Mem.perm_alloc_2; [exact HA|exact Hofs]. }
  split.
  { intros chunk b' ofs HV. rewrite HO by (left; intros ->; exact (HFresh HV)).
    eapply Mem.load_alloc_unchanged; [exact HA|exact HV]. }
  split.
  { intros chunk b' ofs p HV [HR HAl]. split; [|exact HAl].
    intros o Ho. apply HP. eapply Mem.perm_alloc_1; [exact HA|]. apply HR. exact Ho. }
  split.
  { intros b' ofs k p HV HPerm. eapply Mem.perm_alloc_4; [exact HA|apply HP; exact HPerm|].
    intros ->. exact (HFresh HV). }
  intros b' HV. apply HVB. eapply Mem.valid_block_alloc; [exact HA|exact HV].
Qed.

(** ** The input buffer *)

Definition cell_bit (cells : list Cell) (q : Z) : bool :=
  match nth_error cells (Z.to_nat q) with
  | Some (Some b) => b
  | _ => false
  end.

(** Word [k] of the MSB-first stream. *)
Definition input_word (cells : list Cell) (k : Z) : val :=
  Vlong (packed_word (fun j => cell_bit cells (64 * k + 63 - j))).

(** The buffer contents in address order: the stream's first word is stored
    just below the edge. *)
Definition input_run (cells : list Cell) : list val :=
  let words := Z.to_nat (frame_words (Z.of_nat (length cells))) in
  map (fun s => input_word cells (Z.of_nat (words - 1 - s))) (List.seq 0 words).

Lemma input_run_length cells :
  length (input_run cells) = Z.to_nat (frame_words (Z.of_nat (length cells))).
Proof. unfold input_run. rewrite map_length, seq_length. reflexivity. Qed.

Lemma input_run_represents_at m bi (base : Z) (cells : list Cell) :
  Z.of_nat (length cells) <= Int64.max_unsigned ->
  0 <= base ->
  base + 8 * frame_words (Z.of_nat (length cells)) <= Ptrofs.max_unsigned ->
  (forall i v, nth_error (input_run cells) i = Some v ->
    Mem.load Mint64 m bi (base + 8 * Z.of_nat i) = Some (Val.load_result Mint64 v)) ->
  frame_input_cells_at m bi (base + 8 * frame_words (Z.of_nat (length cells))) 0 cells.
Proof.
  intros HMax HBase HEnd HLoads i c Hc.
  set (N := Z.of_nat (length cells)) in *.
  set (words := frame_words N) in *.
  assert (Hi : (i < length cells)%nat) by (apply nth_error_Some; congruence).
  destruct (frame_words_bounds N ltac:(unfold N; lia)) as [HW0 HW].
  fold words in HW0, HW.
  set (q := 0 + Z.of_nat i).
  assert (Hq : 0 <= q < N) by (unfold q, N; lia).
  assert (Hk : 0 <= q / 64 < words).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  pose proof (Z.mod_pos_bound q 64 ltac:(lia)) as Hmod.
  pose proof (Z.div_mod q 64 ltac:(lia)) as Hdm.
  set (s := Z.to_nat (words - 1 - q / 64)).
  assert (Hs : (s < Z.to_nat words)%nat) by (unfold s; lia).
  assert (Hnth : nth_error (input_run cells) s = Some (input_word cells (q / 64))).
  { unfold input_run. fold N. fold words. rewrite nth_error_map.
    rewrite nth_error_seq_in by exact Hs. unfold Datatypes.option_map. do 2 f_equal.
    unfold s. lia. }
  pose proof (HLoads s _ Hnth) as HL.
  assert (HP : frame_input_bit_at m bi (base + 8 * words) q (cell_bit cells q)).
  { unfold frame_input_bit_at.
    assert (HM : Int64.max_unsigned = 18446744073709551615) by reflexivity.
    split; [lia|]. split; [lia|].
    eexists. split.
    - replace (base + 8 * words - 8 * (1 + q / 64)) with (base + 8 * Z.of_nat s)
        by (unfold s; lia).
      exact HL.
    - rewrite packed_word_testbit by lia. f_equal. lia. }
  assert (Hbit : cell_bit cells q = match c with Some b => b | None => false end).
  { unfold cell_bit, q. rewrite Z.add_0_l, Nat2Z.id, Hc. reflexivity. }
  destruct c as [b|]; cbn [cell_matches].
  - rewrite <- Hbit. exact HP.
  - eexists. exact HP.
Qed.

Lemma input_run_represents m bi (cells : list Cell) :
  Z.of_nat (length cells) <= Int64.max_unsigned ->
  (forall i v, nth_error (input_run cells) i = Some v ->
    Mem.load Mint64 m bi (8 * Z.of_nat i) = Some (Val.load_result Mint64 v)) ->
  frame_input_cells_at m bi (8 * frame_words (Z.of_nat (length cells))) 0 cells.
Proof.
  intros HMax HLoads.
  destruct (frame_words_bounds (Z.of_nat (length cells)) ltac:(lia)) as [_ HW].
  assert (HM : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  assert (HPM : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  exact (input_run_represents_at m bi 0 cells HMax ltac:(lia) ltac:(lia) HLoads).
Qed.

(** ** The output buffer *)

Definition output_run (count : Z) : list val :=
  repeat (Vlong Int64.zero) (Z.to_nat (frame_words count)).

Lemma nth_error_repeat_in {T} (x : T) n i :
  (i < n)%nat -> nth_error (repeat x n) i = Some x.
Proof.
  revert i. induction n as [|n IH]; intros i Hi; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma output_run_frame m bd bw count :
  0 <= count <= Int64.max_unsigned -> bd <> bw ->
  Mem.load Mptr m bd 0 = Some (Vptr bw (Ptrofs.repr 0)) ->
  Mem.load Mint64 m bd 8 = Some (Vlong (Int64.repr count)) ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  (forall i v, nth_error (output_run count) i = Some v ->
    Mem.load Mint64 m bw (8 * Z.of_nat i) = Some (Val.load_result Mint64 v)) ->
  (forall i, (i < length (output_run count))%nat ->
    Mem.valid_access m Mint64 bw (8 * Z.of_nat i) Writable) ->
  write_frame_at m bd 0 bw 0 count count.
Proof.
  intros HCount HNe HPtr HCur HRec HLoads HAccess.
  assert (HM : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  assert (HPM : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  split; [split; [lia|lia]|].
  split; [split; [exact HPtr|exact HCur]|].
  split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HRec|].
  intros i Hi. cbv zeta. unfold write_cell_address. rewrite Z.add_0_l.
  set (sz := (count - 1 - i) / 64).
  assert (Hsz : 0 <= sz < frame_words count).
  { unfold sz, frame_words. split; [apply Z.div_pos; lia|].
    replace (count + 63) with (count - 1 + 1 * 64) by lia. rewrite Z.div_add by lia.
    pose proof (Z.div_le_mono (count - 1 - i) (count - 1) 64 ltac:(lia) ltac:(lia)). lia. }
  destruct (frame_words_bounds count ltac:(lia)) as [_ HW].
  assert (Hs : (Z.to_nat sz < Z.to_nat (frame_words count))%nat) by lia.
  assert (Haddr : 8 * sz = 8 * Z.of_nat (Z.to_nat sz)) by lia.
  split; [lia|]. split; [lia|].
  split; [left; exact HNe|]. split.
  - rewrite Haddr. apply HAccess. unfold output_run. rewrite repeat_length. exact Hs.
  - exists Int64.zero. rewrite Haddr.
    exact (HLoads _ _ (nth_error_repeat_in (Vlong Int64.zero) _ _ Hs)).
Qed.

(** ** Construction of both frames *)

Theorem jet_frames_constructible (m0 : mem) (cells : list Cell) (count : Z) :
  Z.of_nat (length cells) <= Int64.max_unsigned ->
  0 <= count <= Int64.max_unsigned ->
  exists m bd bs bi bw edge,
    frame_base_valid 0 /\ (8 | 0) /\
    frame_fields_at m bs 0 bi edge 0 /\
    frame_input_cells_at m bi edge 0 cells /\
    write_frame_at m bd 0 bw 0 count count /\
    (bd <> bi /\ bd <> bw /\ bd <> bs /\ bi <> bw /\ bs <> bi /\ bs <> bw) /\
    (forall b, Mem.valid_block m0 b ->
      Mem.valid_block m b /\ b <> bd /\ b <> bs /\ b <> bi /\ b <> bw /\
      (forall chunk ofs, Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
      (forall ofs k p, Mem.perm m b ofs k p -> Mem.perm m0 b ofs k p)).
Proof.
  intros HCells HCount.
  set (edge := 8 * frame_words (Z.of_nat (length cells))).
  destruct (alloc_word_run m0 (input_run cells))
    as (m1 & bi & HF1 & HV1 & HL1 & _ & _ & HO1 & _ & HQ1 & HVB1).
  destruct (alloc_word_run m1 (output_run count))
    as (m2 & bw & HF2 & HV2 & HL2 & HA2 & _ & HO2 & _ & HQ2 & HVB2).
  destruct (alloc_word_run m2 [Vptr bi (Ptrofs.repr edge); Vlong (Int64.repr 0)])
    as (m3 & bs & HF3 & HV3 & HL3 & _ & _ & HO3 & HP3 & HQ3 & HVB3).
  destruct (alloc_word_run m3 [Vptr bw (Ptrofs.repr 0); Vlong (Int64.repr count)])
    as (m4 & bd & HF4 & HV4 & HL4 & HA4 & _ & HO4 & HP4 & HQ4 & HVB4).
  assert (Hbi2 : Mem.valid_block m2 bi) by (apply HVB2; exact HV1).
  assert (Hbi3 : Mem.valid_block m3 bi) by (apply HVB3; exact Hbi2).
  assert (Hbw3 : Mem.valid_block m3 bw) by (apply HVB3; exact HV2).
  assert (Ndbi : bd <> bi) by (intros ->; exact (HF4 Hbi3)).
  assert (Ndbw : bd <> bw) by (intros ->; exact (HF4 Hbw3)).
  assert (Ndbs : bd <> bs) by (intros ->; exact (HF4 HV3)).
  assert (Nbibw : bi <> bw) by (intros ->; exact (HF2 HV1)).
  assert (Nsbi : bs <> bi) by (intros ->; exact (HF3 Hbi2)).
  assert (Nsbw : bs <> bw) by (intros ->; exact (HF3 HV2)).
  exists m4, bd, bs, bi, bw, edge.
  split; [split; [lia|assert (Ptrofs.max_unsigned = 18446744073709551615) by reflexivity; lia]|].
  split; [apply Z.divide_0_r|].
  split.
  { split.
    - rewrite HO4 by exact HV3. exact (HL3 0%nat _ eq_refl).
    - rewrite HO4 by exact HV3. exact (HL3 1%nat _ eq_refl). }
  split.
  { apply input_run_represents; [exact HCells|].
    intros i v Hnth. rewrite HO4 by exact Hbi3. rewrite HO3 by exact Hbi2.
    rewrite HO2 by exact HV1. exact (HL1 i v Hnth). }
  split.
  { apply output_run_frame; [exact HCount|exact Ndbw| | | | |].
    - exact (HL4 0%nat _ eq_refl).
    - exact (HL4 1%nat _ eq_refl).
    - exact (HA4 1%nat ltac:(cbn; lia)).
    - intros i v Hnth. rewrite HO4 by exact Hbw3. rewrite HO3 by exact HV2.
      exact (HL2 i v Hnth).
    - intros i Hi. apply HP4; [exact Hbw3|]. apply HP3; [exact HV2|]. exact (HA2 i Hi). }
  split; [repeat split; assumption|].
  intros b Hb.
  assert (Hb1 : Mem.valid_block m1 b) by (apply HVB1; exact Hb).
  assert (Hb2 : Mem.valid_block m2 b) by (apply HVB2; exact Hb1).
  assert (Hb3 : Mem.valid_block m3 b) by (apply HVB3; exact Hb2).
  split; [apply HVB4; exact Hb3|].
  split; [intros ->; exact (HF4 Hb3)|]. split; [intros ->; exact (HF3 Hb2)|].
  split; [intros ->; exact (HF1 Hb)|]. split; [intros ->; exact (HF2 Hb1)|].
  split.
  - intros chunk ofs. rewrite HO4 by exact Hb3. rewrite HO3 by exact Hb2.
    rewrite HO2 by exact Hb1. apply HO1. exact Hb.
  - intros ofs k p HPerm. apply (HQ1 b ofs k p Hb). apply (HQ2 b ofs k p Hb1).
    apply (HQ3 b ofs k p Hb2). exact (HQ4 b ofs k p Hb3 HPerm).
Qed.
