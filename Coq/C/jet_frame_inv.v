(** State of the input and output frames of a jet while its body runs,
    insensitive to changes of memory outside the frame blocks.  It is the
    invariant under which the frame helpers act as oracles of the symbolic
    executor. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_output_sequence_step C.jet_encoding C.jet_bitcoin_effects.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Section FINV.
Variables (m0 : mem) (bd : block) (dbase : Z) (bw : block) (outedge cursor N : Z) (bi : block).

(** The frame blocks, as far as they exist initially. *)
Definition fext (b : block) : Prop := (b = bd \/ b = bw \/ b = bi) /\ Mem.valid_block m0 b.

Definition eqext (m m' : mem) : Prop := lframe (fun b _ => fext b) m m'.

(** The effect of the writes so far, restricted to the frame blocks. *)
Definition weffE (m : mem) (n : Z) (cells : list Cell) : Prop :=
  frame_output_cells_at m bw outedge cursor cells /\
  write_prefix_at m0 m bw outedge cursor /\
  frame_fields_at m bd dbase bw outedge (cursor - n) /\
  (forall chunk b ofs, fext b ->
     (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
     (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - n) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
     Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
  (forall b ofs k p, fext b -> Mem.perm m0 b ofs k p -> Mem.perm m b ofs k p).

Definition finv (m : mem) (w : bool) (outs : list Cell) : Prop :=
  (forall b, fext b -> Mem.valid_block m b) /\
  write_frame_at m0 bd dbase bw outedge cursor N /\
  Z.of_nat (length outs) <= N /\
  weffE m (Z.of_nat (length outs)) outs /\
  (w = false -> outs = [] /\ eqext m0 m).

Hypothesis HF0 : write_frame_at m0 bd dbase bw outedge cursor N.

Lemma fext_bd : fext bd.
Proof.
  split; [left; reflexivity|].
  destruct HF0 as (_ & _ & _ & _ & _ & _ & [Hp _] & _).
  eapply Mem.perm_valid_block. apply (Hp (dbase + 8)). simpl. lia.
Qed.

Lemma load_valid m chunk b ofs v : Mem.load chunk m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intros H. apply Mem.load_valid_access in H. destruct H as [Hp _].
  eapply Mem.perm_valid_block. apply (Hp ofs). pose proof (size_chunk_pos chunk). lia.
Qed.

Lemma finv_init : finv m0 false [].
Proof.
  split; [intros b [_ H]; exact H|]. split; [exact HF0|].
  destruct HF0 as (HB & HFl & HE & HC & HM & HD & PD & HW).
  split; [simpl; lia|]. split.
  - split; [intros i c Hi; destruct i; discriminate|].
    split; [intros old HL; exists old; split; [exact HL|unfold word_outside_eq; intros; reflexivity]|].
    split; [simpl; replace (cursor - 0) with cursor by lia; exact HFl|].
    split; [reflexivity|auto].
  - intros _. split; [reflexivity|apply lframe_refl].
Qed.

Lemma output_cells_transfer m m' cells :
  (cells <> [] -> forall ofs, Mem.load Mint64 m' bw ofs = Mem.load Mint64 m bw ofs) ->
  frame_output_cells_at m bw outedge cursor cells -> frame_output_cells_at m' bw outedge cursor cells.
Proof.
  intros HL H i c Hi. specialize (H i c Hi).
  assert (Hne : cells <> []) by (intros ->; destruct i; discriminate).
  specialize (HL Hne).
  unfold frame_output_bit_at in *.
  destruct c as [bit|]; cbn [cell_matches] in *.
  - destruct H as (Hq & w & Hw & Hb). split; [exact Hq|]. exists w. rewrite HL. auto.
  - destruct H as (bit & Hq & w & Hw & Hb). exists bit. split; [exact Hq|]. exists w. rewrite HL. auto.
Qed.

Lemma bw_valid : 0 < N -> Mem.valid_block m0 bw.
Proof.
  intros HN.
  destruct (write_frame_at_head m0 bd dbase bw outedge cursor N HN HF0) as (_ & _ & _ & w & Hw).
  exact (load_valid _ _ _ _ _ Hw).
Qed.

Lemma finv_stable m m' w outs :
  finv m w outs -> eqext m m' -> finv m' w outs.
Proof.
  intros (HV & HF & HN & (O & P & F & L & Pm) & Hw) (EL & EP & EV).
  assert (EL' : forall chunk b ofs, fext b -> Mem.load chunk m' b ofs = Mem.load chunk m b ofs).
  { intros chunk b ofs Hb. apply EL; [exact (HV b Hb)|intros; exact Hb]. }
  split; [intros b Hb; apply EV; apply HV; exact Hb|]. split; [exact HF|]. split; [exact HN|].
  split.
  - split.
    { apply (output_cells_transfer m m'); [|exact O]. intros Hne ofs. apply EL'.
      split; [right; left; reflexivity|].
      apply bw_valid. destruct outs; [congruence|simpl in HN; lia]. }
    split.
    { intros old Hold. destruct (P old Hold) as (w1 & Hw1 & Ho). exists w1. split; [|exact Ho].
      rewrite EL'; [exact Hw1|]. split; [right; left; reflexivity|exact (load_valid _ _ _ _ _ Hold)]. }
    split.
    { destruct F as [F1 F2]. split; rewrite EL' by exact fext_bd; assumption. }
    split.
    { intros chunk b ofs Hb H1 H2. rewrite EL' by exact Hb. apply L; assumption. }
    intros b ofs k p Hb Hp. apply EP; [exact (HV b Hb)|exact Hb|]. apply Pm; assumption.
  - intros Hwf. destruct (Hw Hwf) as [-> E]. split; [reflexivity|].
    eapply lframe_trans; [exact E|]. split; [exact EL|]. split; [exact EP|exact EV].
Qed.

(** While nothing has been written, the input is as initially. *)
Lemma finv_input m outs edge rc inp :
  finv m false outs ->
  frame_input_cells_at m0 bi edge rc inp -> frame_input_cells_at m bi edge rc inp.
Proof.
  intros (_ & _ & _ & _ & Hw) H. destruct (Hw eq_refl) as [_ (EL0 & _ & _)].
  assert (EL : forall chunk b ofs, fext b -> Mem.load chunk m b ofs = Mem.load chunk m0 b ofs).
  { intros chunk b ofs Hb. apply EL0; [exact (proj2 Hb)|intros; exact Hb]. }
  intros i c Hi. specialize (H i c Hi). unfold frame_input_bit_at in *.
  destruct c as [bit|]; cbn [cell_matches] in *.
  - destruct H as (Hq & He & w & Hl & Hb). split; [exact Hq|]. split; [exact He|]. exists w.
    rewrite EL; [auto|]. split; [right; right; reflexivity|exact (load_valid _ _ _ _ _ Hl)].
  - destruct H as (bit & Hq & He & w & Hl & Hb). exists bit. split; [exact Hq|]. split; [exact He|]. exists w.
    rewrite EL; [auto|]. split; [right; right; reflexivity|exact (load_valid _ _ _ _ _ Hl)].
Qed.

Lemma write_frame_at_le m count count' :
  0 <= count' <= count -> write_frame_at m bd dbase bw outedge cursor count ->
  write_frame_at m bd dbase bw outedge cursor count'.
Proof.
  intros Hc (HB & HFl & HE & HC & HM & HD & PD & HW).
  split; [exact HB|]. split; [exact HFl|]. split; [exact HE|]. split; [lia|]. split; [exact HM|].
  split; [exact HD|]. split; [exact PD|]. intros i Hi. apply HW. lia.
Qed.

(** The rest of the output frame is writable after the writes so far. *)
Lemma finv_wframe m w outs :
  finv m w outs ->
  write_frame_at m bd dbase bw outedge (cursor - Z.of_nat (length outs)) (N - Z.of_nat (length outs)).
Proof.
  intros (HV & _ & HN & (O & P & F & L & Pm) & _).
  set (n := Z.of_nat (length outs)) in *. set (count := N - n).
  assert (HF : write_frame_at m0 bd dbase bw outedge cursor (n + count)) by (unfold count; replace (n + (N - n)) with N by lia; exact HF0).
  assert (Hcount : 0 <= count) by (unfold count; lia).
  pose proof HF as [HB [HFl [HE [HC [HM [HD [PD HW]]]]]]].
  assert (Hn : 0 <= n) by (unfold n; lia).
  assert (HVA : forall chunk b ofs p, fext b -> Mem.valid_access m0 chunk b ofs p ->
    Mem.valid_access m chunk b ofs p).
  { intros chunk b ofs p Hb [HR HA]. split; [|exact HA]. intros addr HA'. apply Pm; [exact Hb|]. apply HR; exact HA'. }
  split; [exact HB|]. split; [exact F|]. split; [exact HE|]. split; [lia|]. split; [lia|].
  split; [exact HD|]. split; [apply HVA; [exact fext_bd|exact PD]|].
  intros i Hi. cbn zeta.
  assert (Haddr : write_cell_address outedge (cursor - n) i = write_cell_address outedge cursor (i + n)).
  { unfold write_cell_address. replace (cursor - n - 1 - i) with (cursor - 1 - (i + n)) by lia. reflexivity. }
  rewrite Haddr. destruct (HW (i + n) ltac:(lia)) as [HA0 [HA [PW [old Hold]]]].
  assert (Hbw : fext bw) by (split; [right; left; reflexivity|exact (load_valid _ _ _ _ _ Hold)]).
  split; [exact HA0|]. split; [exact HA|]. split; [apply HVA; assumption|].
  set (addr := write_cell_address outedge cursor (i + n)) in *.
  assert (Haddr_def : addr = outedge + 8 * ((cursor - 1 - (i + n)) / 64)) by reflexivity.
  assert (Hmono : (cursor - 1 - (i + n)) / 64 <= (cursor - n) / 64)
    by (apply Z.div_le_mono; lia).
  destruct (Z_le_dec (addr + 8) (outedge + 8 * ((cursor - n) / 64))) as [Hlow|Hnl].
  - exists old. rewrite L; [exact Hold|exact Hbw|left; exact (not_eq_sym HD)|right; left; exact Hlow].
  - destruct (Z_le_dec (write_word_address outedge cursor + 8) addr) as [Hhigh|Hnh].
    + exists old. rewrite L; [exact Hold|exact Hbw|left; exact (not_eq_sym HD)|right; right; exact Hhigh].
    + unfold write_word_address in Hnh.
      assert (Hk : (cursor - 1 - (i + n)) / 64 = (cursor - n) / 64) by lia.
      destruct (Z.eq_dec n 0) as [Hn0|Hn1].
      * destruct (write_frame_at_head m0 bd dbase bw outedge cursor (n + count) ltac:(lia) HF)
          as [_ [_ [_ [w0 Hw0]]]].
        destruct (P w0 Hw0) as [w1 [Hw1 _]]. exists w1.
        replace addr with (write_word_address outedge cursor); [exact Hw1|].
        unfold write_word_address. rewrite Haddr_def.
        pose proof (Z.div_le_mono (cursor - 1) (cursor - n) 64 ltac:(lia) ltac:(lia)) as Hge.
        lia.
      * assert (HlenN : (Z.to_nat (n - 1) < length outs)%nat) by (unfold n in *; lia).
        destruct (nth_error outs (Z.to_nat (n - 1))) as [c|] eqn:Hc;
          [|apply nth_error_None in Hc; lia].
        specialize (O (Z.to_nat (n - 1)) c Hc).
        replace (cursor - 1 - Z.of_nat (Z.to_nat (n - 1))) with (cursor - n) in O by lia.
        assert (Hbit : exists bit, frame_output_bit_at m bw outedge (cursor - n) bit).
        { destruct c as [bit|]; cbn [cell_matches] in O; [exists bit; exact O|exact O]. }
        destruct Hbit as [bit [_ [w1 [Hw1 _]]]]. exists w1.
        replace addr with (outedge + 8 * ((cursor - n) / 64)); [exact Hw1|].
        rewrite Haddr_def, Hk. reflexivity.
Qed.

(** A write, given as its actual effect on the memory, extends the state. *)
Lemma finv_write m m' w outs n2 cells2 :
  finv m w outs -> Z.of_nat (length cells2) = n2 -> Z.of_nat (length outs) + n2 <= N ->
  write_effect m m' bd dbase bw outedge (cursor - Z.of_nat (length outs)) n2 cells2 ->
  finv m' true (outs ++ cells2).
Proof.
  intros (HV & _ & HN & (O1 & P1 & F1 & L1 & Pm1) & _) HL2 HN2 (O2 & P2 & F2 & L2 & Pm2 & V2).
  set (n1 := Z.of_nat (length outs)) in *.
  assert (Hn2 : 0 <= n2) by lia. assert (Hn1 : 0 <= n1) by (unfold n1; lia).
  assert (HFrame : write_frame_at m0 bd dbase bw outedge cursor (n1 + n2)) by (apply (write_frame_at_le m0 N); [lia|exact HF0]).
  pose proof HFrame as [HB [HF [HE [HC [HM [HD [PD HW]]]]]]].
  assert (Hdiv1 : (cursor - n1 - n2) / 64 <= (cursor - n1) / 64) by (apply Z.div_le_mono; lia).
  assert (Hdiv2 : write_word_address outedge (cursor - n1) <= write_word_address outedge cursor).
  { unfold write_word_address. pose proof (Z.div_le_mono (cursor - n1 - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia. }
  split; [intros b Hb; apply V2, HV; exact Hb|]. split; [exact HF0|].
  split; [rewrite app_length, Nat2Z.inj_add; fold n1; lia|].
  split; [|intros; discriminate].
  rewrite app_length, Nat2Z.inj_add. fold n1. rewrite HL2.
  split.
  - apply frame_output_cells_at_app. split.
    + eapply frame_output_cells_prefix_preserved with (m := m) (bf := bd) (base := dbase)
        (cursor := cursor - n1) (low := outedge + 8 * ((cursor - n1 - n2) / 64)).
      * exact HD.
      * fold n1. lia.
      * exact P2.
      * exact L2.
      * exact O1.
    + fold n1. exact O2.
  - split.
    + eapply write_prefix_at_chain with (mi := m) (next := cursor - n1)
        (low := outedge + 8 * ((cursor - n1 - n2) / 64)).
      * exact HD.
      * lia.
      * exact P1.
      * exact P2.
      * exact L2.
    + split.
      * replace (cursor - (n1 + n2)) with (cursor - n1 - n2) by lia. exact F2.
      * split.
        -- intros chunk b ofs Hb Hbf Hbw.
           replace (cursor - (n1 + n2)) with (cursor - n1 - n2) in Hbw by lia.
           assert (Hbw2 : b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - n1 - n2) / 64) \/
             write_word_address outedge (cursor - n1) + 8 <= ofs).
           { destruct Hbw as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; lia]. }
           assert (Hbw1 : b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - n1) / 64) \/
             write_word_address outedge cursor + 8 <= ofs).
           { destruct Hbw as [H|[H|H]]; [left; exact H|right; left; lia|right; right; exact H]. }
           rewrite (L2 chunk b ofs Hbf Hbw2). apply (L1 chunk b ofs Hb Hbf Hbw1).
        -- intros b ofs kind p Hb HP. apply Pm2, Pm1; assumption.
Qed.
End FINV.
