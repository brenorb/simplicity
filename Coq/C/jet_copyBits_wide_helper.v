(** copyBitsHelper and copyBits for copy counts between 65 and 128 bits, at
    every alignment of the two frames: partial-word prefix, then the
    destination-aligned tail.  Conditional on the explicit [memcpy_model]
    (used only on the source-aligned paths). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_frame_spec C.jet_word_bits C.jet_frame_constants C.jet_context_separated.
Require Import C.jet_copyBits_exec C.jet_copyBits_helper_exec C.jet_copyBits_helper_right.
Require Import C.jet_copyBits_partial_crossing C.jet_copyBits_right_advance.
Require Import C.jet_copyBits_two_words_right_exec C.jet_copyBits_two_words_left_exec.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing.
Require Import C.jet_copyBits_short_word C.jet_copyBits_partial_crossing_cells C.jet_copyBits_separation.
Require Import C.jet_memcpy_model.
Require Import C.jet_copyBits_wide_prefix C.jet_copyBits_wide_sem C.jet_copyBits_wide_tail_sem.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 120.

Lemma valid_access_perm_preserved m m' chunk b ofs p :
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm m' b ofs kind p) ->
  Mem.valid_access m chunk b ofs p -> Mem.valid_access m' chunk b ofs p.
Proof. intros HP [HR HA]. split; [intros o Ho; apply HP; apply HR; exact Ho|exact HA]. Qed.

Section WideHelper.
Variable Hmodel : memcpy_model.
Variables (m : mem) (bd : block) (base : Z) (bs : block) (sbase : Z) (bi : block) (edge rc : Z).
Variables (bw : block) (outedge cursor n : Z) (cells : list Cell).
Hypothesis HSb : frame_base_valid sbase.
Hypothesis HF : frame_fields_at m bs sbase bi edge rc.
Hypothesis Hwrite : write_frame_at m bd base bw outedge cursor n.
Hypothesis Hlen : n = Z.of_nat (length cells).
Hypothesis Hn : 64 < n <= 128.
Hypothesis Hsepb : jet_copy_buffers_separated bd bi bw edge outedge cursor rc n.
Hypothesis Hinput : frame_input_cells_at m bi edge rc cells.

Let ds := cursor mod 64.
Let ss0 := 64 - rc mod 64.
Let k0 := rc / 64.
Let cq := cursor / 64.
Let C := cursor - 1 + rc.
Let dA := cq - 1.
Let wwa := write_word_address outedge cursor.
Let le0 := copy_helper_env bd base bs sbase n bi edge rc bw outedge cursor.

Lemma wh_cursor : cursor = 64 * cq + ds /\ 0 <= ds < 64.
Proof. unfold cq, ds. split; [apply Z.div_mod; lia|apply Z.mod_pos_bound; lia]. Qed.

Lemma wh_rc : rc = 64 * k0 + (64 - ss0) /\ 1 <= ss0 <= 64 /\ 0 <= rc.
Proof.
  destruct (input_cells_word m bi edge rc cells 0 Hinput ltac:(lia)) as (HR & _).
  unfold k0, ss0. pose proof (Z.div_mod rc 64 ltac:(lia)). pose proof (Z.mod_pos_bound rc 64 ltac:(lia)). lia.
Qed.

Lemma wh_k0 : 0 <= k0.
Proof. destruct wh_rc as (_ & _ & HR). unfold k0. apply Z.div_pos; lia. Qed.

Lemma wh_bounds : 0 <= n <= cursor /\ cursor <= Int64.max_unsigned /\ 0 <= outedge /\ bd <> bw.
Proof. destruct Hwrite as (_ & _ & HO & HC & HM & HD & _). tauto. Qed.

Lemma wh_src q :
  rc <= q < rc + n ->
  8 * (1 + q / 64) <= edge <= Ptrofs.max_unsigned /\
  exists S, Mem.load Mint64 m bi (edge - 8 * (1 + q / 64)) = Some (Vlong S).
Proof.
  intros Hq. destruct (input_cells_word m bi edge rc cells (q - rc) Hinput ltac:(lia)) as (_ & HE & HS).
  replace (rc + (q - rc)) with q in * by lia. split; assumption.
Qed.

Lemma wh_dst p :
  cursor - n <= p < cursor ->
  0 <= outedge + 8 * (p / 64) /\ outedge + 8 * (p / 64) + 8 <= Ptrofs.max_unsigned /\
  Mem.valid_access m Mint64 bw (outedge + 8 * (p / 64)) Writable /\
  exists w, Mem.load Mint64 m bw (outedge + 8 * (p / 64)) = Some (Vlong w).
Proof.
  intros Hp. destruct Hwrite as (_ & _ & _ & _ & _ & _ & _ & HW).
  specialize (HW (cursor - 1 - p) ltac:(lia)). unfold write_cell_address in HW.
  replace (cursor - 1 - (cursor - 1 - p)) with p in HW by lia. exact HW.
Qed.

Lemma wh_sep q p :
  rc <= q < rc + n -> cursor - n <= p < cursor ->
  bi <> bw \/ edge - 8 * (1 + q / 64) + 8 <= outedge + 8 * (p / 64) \/
    outedge + 8 * (p / 64) + 8 <= edge - 8 * (1 + q / 64).
Proof.
  intros Hq Hp. destruct wh_rc as (_ & _ & HR). destruct wh_bounds as (HNC & _).
  pose proof (copy_buffers_separated_words bd bi bw edge outedge cursor rc n (q - rc) (cursor - 1 - p)
    Hsepb HR ltac:(lia) ltac:(lia)) as H.
  unfold write_word_address in H.
  replace (rc + (q - rc)) with q in H by lia.
  replace (cursor - (cursor - 1 - p) - 1) with p in H by lia. exact H.
Qed.

Lemma wh_keys :
  le0!_src_ptr = Some (Vptr bi (Ptrofs.repr (edge - 8 * (1 + rc / 64)))) /\
  le0!_dst_ptr = Some (Vptr bw (Ptrofs.repr (write_word_address outedge cursor))) /\
  le0!_src_shift = Some (Vlong (Int64.repr (64 - rc mod 64))) /\
  le0!_dst_shift = Some (Vlong (Int64.repr (cursor mod 64))) /\
  le0!_n = Some (Vlong (Int64.repr n)).
Proof.
  unfold le0. repeat split.
Qed.

Definition wide_prefix_post (le1 : temp_env) (m1 : mem) (so1 do1 : ptrofs) (k1 ss1 : Z) : Prop :=
  le1!_src_ptr = Some (Vptr bi so1) /\ le1!_dst_ptr = Some (Vptr bw do1) /\
  le1!_src_shift = Some (Vlong (Int64.repr ss1)) /\ le1!_n = Some (Vlong (Int64.repr (n - ds))) /\
  Ptrofs.unsigned so1 = edge - 8 * (1 + k1) /\ Ptrofs.unsigned do1 = outedge + 8 * dA /\
  0 <= ss1 <= 64 /\ k0 <= k1 /\ rc + ds = 64 * k1 + 64 - ss1 /\
  copied m m1 bi edge bw outedge C (cursor - ds) cursor /\
  (forall old, Mem.load Mint64 m bw wwa = Some (Vlong old) ->
    exists W, Mem.load Mint64 m1 bw wwa = Some (Vlong W) /\
      forall i, write_word_shift cursor <= i < 64 -> Int64.testbit W i = Int64.testbit old i) /\
  (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * (dA + 1) \/ wwa + 8 <= ofs ->
    Mem.load chunk m1 b ofs = Mem.load chunk m b ofs) /\
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm m1 b ofs kind p) /\
  (forall b, Mem.valid_block m b -> Mem.valid_block m1 b).

Lemma wide_prefix :
  exists le1 m1 so1 do1 k1 ss1,
    Clight2.exec_stmt ge0 empty_env le0 m
      (Sifthenelse (Etempvar _dst_shift tulong) copy_partial Sskip) E0 le1 m1 Out_normal /\
    wide_prefix_post le1 m1 so1 do1 k1 ss1.
Proof.
  destruct wh_cursor as (Hcur & Hds). destruct wh_rc as (Hrc & Hss0 & HR0).
  destruct wh_bounds as (HNC & HCM & HO & Hbd). pose proof wh_k0 as Hk0.
  destruct wh_keys as (KP & KD & KS & KDS & KN).
  fold ss0 in KS. fold ds in KDS. fold k0 in KP. fold wwa in KD.
  assert (Hcq : 1 <= cq) by lia.
  destruct (wh_src rc ltac:(lia)) as (HE0 & S0 & HS0). fold k0 in HE0, HS0.
  destruct (Z.eq_dec ds 0) as [Hz|Hnz].
  - (* destination aligned: no prefix *)
    assert (Hwd : (cursor - 1) / 64 = dA).
    { unfold dA. symmetry. apply (Z.div_unique (cursor - 1) 64 (cq - 1) 63); lia. }
    assert (Hwwa : wwa = outedge + 8 * dA) by (unfold wwa, write_word_address; rewrite Hwd; reflexivity).
    destruct (wh_dst (cursor - 1) ltac:(lia)) as (HA0 & HAM & _ & _). rewrite Hwd in HA0, HAM.
    exists le0, m, (Ptrofs.repr (edge - 8 * (1 + k0))), (Ptrofs.repr wwa), k0, ss0. split.
    + eapply exec_Sifthenelse with (v1 := Vlong Int64.zero) (b := Datatypes.false).
      * apply eval_Etempvar. rewrite KDS, Hz. reflexivity.
      * reflexivity.
      * apply exec_Sskip.
    + unfold wide_prefix_post. rewrite Hz, Z.sub_0_r.
      split; [exact KP|]. split; [exact KD|]. split; [exact KS|]. split; [exact KN|].
      split; [apply Ptrofs.unsigned_repr; lia|]. split; [rewrite Hwwa; apply Ptrofs.unsigned_repr; lia|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros p b Hp; lia|].
      split; [intros old Hold; exists old; split; [exact Hold|reflexivity]|].
      split; [reflexivity|]. split; intros; assumption.
  - (* partial destination word *)
    assert (Hds1 : 1 <= ds <= 63) by lia.
    assert (Hwd : (cursor - 1) / 64 = cq).
    { symmetry. apply (Z.div_unique (cursor - 1) 64 cq (ds - 1)); lia. }
    assert (Hwwa : wwa = outedge + 8 * cq) by (unfold wwa, write_word_address; rewrite Hwd; reflexivity).
    assert (Hshift : write_word_shift cursor = ds).
    { unfold write_word_shift. replace ((cursor - 1) mod 64) with (ds - 1); [lia|].
      apply (Z.mod_unique (cursor - 1) 64 cq (ds - 1)); lia. }
    destruct (wh_dst (cursor - 1) ltac:(lia)) as (HA0 & HAM & PW & old & Hold).
    rewrite Hwd in HA0, HAM, PW, Hold. rewrite <- Hwwa in HA0, HAM, PW, Hold.
    assert (Hsep0 : bi <> bw \/ edge - 8 * (1 + k0) + 8 <= wwa \/ wwa + 8 <= edge - 8 * (1 + k0)).
    { pose proof (wh_sep rc (cursor - 1) ltac:(lia) ltac:(lia)) as H.
      rewrite Hwd in H. fold k0 in H. rewrite Hwwa. exact H. }
    assert (Hdo_u : Ptrofs.unsigned (Ptrofs.repr wwa) = wwa) by (apply Ptrofs.unsigned_repr; lia).
    assert (Hso_u : Ptrofs.unsigned (Ptrofs.repr (edge - 8 * (1 + k0))) = edge - 8 * (1 + k0))
      by (apply Ptrofs.unsigned_repr; lia).
    assert (Hdo1_u : Ptrofs.unsigned (Ptrofs.sub (Ptrofs.repr wwa) (Ptrofs.repr 8)) = outedge + 8 * dA).
    { destruct (wh_dst (cursor - ds - 1) ltac:(lia)) as (HB0 & _).
      assert (Hbd' : (cursor - ds - 1) / 64 = cq - 1).
      { symmetry. apply (Z.div_unique (cursor - ds - 1) 64 (cq - 1) 63); lia. }
      rewrite Hbd' in HB0.
      rewrite ptrofs_sub_unsigned by (rewrite Hdo_u; lia). rewrite Hdo_u. unfold dA. lia. }
    destruct (Mem.valid_access_store m Mint64 bw wwa (Vlong (clear_low ds old)) PW) as [mc SC].
    assert (HS0c : Mem.load Mint64 mc bi (edge - 8 * (1 + k0)) = Some (Vlong S0)).
    { erewrite Mem.load_store_other; [exact HS0|exact SC|]. change (size_chunk Mint64) with 8. exact Hsep0. }
    assert (PWc : Mem.valid_access mc Mint64 bw wwa Writable) by (eapply Mem.store_valid_access_1; eauto).
    assert (Hcond : forall le, le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
      forall le' m' , Clight2.exec_stmt ge0 empty_env le m copy_partial E0 le' m' Out_normal ->
      Clight2.exec_stmt ge0 empty_env le m
        (Sifthenelse (Etempvar _dst_shift tulong) copy_partial Sskip) E0 le' m' Out_normal).
    { intros le Hle le' m' Hex.
      eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr ds)) (b := Datatypes.true).
      - apply eval_Etempvar. exact Hle.
      - cbn. rewrite Int64.eq_false; [reflexivity|].
        intro HEq. apply (f_equal Int64.unsigned) in HEq.
        rewrite Int64.unsigned_repr in HEq by (change Int64.max_unsigned with 18446744073709551615; lia).
        change (Int64.unsigned Int64.zero) with 0 in HEq. lia.
      - exact Hex. }
    destruct (Z_le_gt_dec ds ss0) as [Hright|Hleft].
    + (* enough source bits in the current source word *)
      destruct (Mem.valid_access_store mc Mint64 bw wwa (Vlong (copy_right_value ss0 ds old S0)) PWc)
        as [mp SP].
      assert (HloadT : Mem.load Mint64 mp bw wwa = Some (Vlong (copy_right_value ss0 ds old S0)))
        by exact (Mem.load_store_same _ _ _ _ _ _ SP).
      eexists _, mp, (Ptrofs.repr (edge - 8 * (1 + k0))), (Ptrofs.sub (Ptrofs.repr wwa) (Ptrofs.repr 8)),
        k0, (ss0 - ds). split.
      * apply Hcond; [exact KDS|].
        eapply exec_copy_partial_continue_right_w with (src_ofs := Ptrofs.repr (edge - 8 * (1 + k0)))
          (dst_ofs := Ptrofs.repr wwa) (mc := mc) (old := old) (source := S0);
          try eassumption; try lia.
        -- rewrite Hdo_u. exact Hold.
        -- rewrite Hdo_u. exact SC.
        -- rewrite Hso_u. exact HS0c.
        -- rewrite Hdo_u. exact SP.
      * unfold wide_prefix_post, copy_two_right_env, copy_right_advance_env, copy_right_env, copy_clear_env.
        split; [rewrite !PTree.gso by discriminate; exact KP|].
        split; [apply PTree.gss|].
        split; [rewrite PTree.gso by discriminate; apply PTree.gss|].
        split; [rewrite !PTree.gso by discriminate; apply PTree.gss|].
        split; [exact Hso_u|]. split; [exact Hdo1_u|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split.
        { rewrite Hwwa in HloadT.
          apply (copied_sub m mp bi edge bw outedge C (64 * cq + 0) (64 * cq + ds)); [|lia|lia].
          apply (copied_word m mp bi edge bw outedge C cq k0 (ss0 - ds) 0 ds _ S0 HloadT HS0
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold C; lia)).
          intros i Hi. split; [lia|]. rewrite copy_right_value_bits by lia.
          rewrite zlt_true by lia. reflexivity. }
        split.
        { intros old' Hold'. rewrite Hold in Hold'. injection Hold' as <-.
          eexists. split; [exact HloadT|]. intros i Hi. rewrite Hshift in Hi.
          rewrite copy_right_value_bits by lia. rewrite zlt_false by lia. reflexivity. }
        split.
        { intros chunk b ofs Hout.
          assert (Hout' : b <> bw \/ ofs + size_chunk chunk <= wwa \/ wwa + size_chunk Mint64 <= ofs).
          { change (size_chunk Mint64) with 8. rewrite Hwwa. unfold dA in Hout. rewrite Hwwa in Hout.
            destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
          erewrite Mem.load_store_other; [|exact SP|exact Hout'].
          eapply Mem.load_store_other; [exact SC|exact Hout']. }
        split.
        { intros b ofs kind p Hp. eapply Mem.perm_store_1; [exact SP|]. eapply Mem.perm_store_1; eauto. }
        { intros b Hv. eapply Mem.store_valid_block_1; [exact SP|]. eapply Mem.store_valid_block_1; eauto. }
    + (* the source word runs out first: continue from the next source word *)
      destruct (wh_src (rc + ss0) ltac:(lia)) as (HE1 & S1 & HS1).
      assert (Hq1 : (rc + ss0) / 64 = k0 + 1).
      { symmetry. apply (Z.div_unique (rc + ss0) 64 (k0 + 1) 0); lia. }
      rewrite Hq1 in HE1, HS1.
      assert (Hsep1 : bi <> bw \/ edge - 8 * (1 + (k0 + 1)) + 8 <= wwa \/ wwa + 8 <= edge - 8 * (1 + (k0 + 1))).
      { pose proof (wh_sep (rc + ss0) (cursor - 1) ltac:(lia) ltac:(lia)) as H.
        rewrite Hwd, Hq1 in H. rewrite Hwwa. exact H. }
      assert (Hso1_u : Ptrofs.unsigned (Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + k0))) (Ptrofs.repr 8)) =
        edge - 8 * (1 + (k0 + 1))).
      { rewrite ptrofs_sub_unsigned by (rewrite Hso_u; lia). rewrite Hso_u. lia. }
      destruct (Mem.valid_access_store mc Mint64 bw wwa (Vlong (copy_left_value ss0 ds old S0)) PWc)
        as [ml SL].
      assert (PWl : Mem.valid_access ml Mint64 bw wwa Writable) by (eapply Mem.store_valid_access_1; eauto).
      assert (HS1l : Mem.load Mint64 ml bi (edge - 8 * (1 + (k0 + 1))) = Some (Vlong S1)).
      { erewrite Mem.load_store_other; [|exact SL|change (size_chunk Mint64) with 8; exact Hsep1].
        erewrite Mem.load_store_other; [exact HS1|exact SC|]. change (size_chunk Mint64) with 8. exact Hsep1. }
      destruct (Mem.valid_access_store ml Mint64 bw wwa
        (Vlong (copy_partial_cross_value ss0 ds old S0 S1)) PWl) as [mp SP].
      assert (HloadT : Mem.load Mint64 mp bw wwa = Some (Vlong (copy_partial_cross_value ss0 ds old S0 S1)))
        by exact (Mem.load_store_same _ _ _ _ _ _ SP).
      eexists _, mp, (Ptrofs.sub (Ptrofs.repr (edge - 8 * (1 + k0))) (Ptrofs.repr 8)),
        (Ptrofs.sub (Ptrofs.repr wwa) (Ptrofs.repr 8)), (k0 + 1), (64 - (ds - ss0)). split.
      * apply Hcond; [exact KDS|].
        eapply exec_copy_partial_continue_left_w with (src_ofs := Ptrofs.repr (edge - 8 * (1 + k0)))
          (dst_ofs := Ptrofs.repr wwa) (mc := mc) (ml := ml) (old := old) (source := S0) (next := S1);
          try eassumption; try lia.
        -- rewrite Hdo_u. exact Hold.
        -- rewrite Hdo_u. exact SC.
        -- rewrite Hso_u. exact HS0c.
        -- rewrite Hdo_u. exact SL.
        -- rewrite Hso1_u. exact HS1l.
        -- rewrite Hdo_u. exact SP.
      * unfold wide_prefix_post, copy_two_left_env, copy_right_advance_env, copy_partial_cross_env,
          copy_right_env, copy_cross_env, copy_left_env, copy_clear_env.
        split; [rewrite !PTree.gso by discriminate; apply PTree.gss|].
        split; [apply PTree.gss|].
        split; [rewrite PTree.gso by discriminate; apply PTree.gss|].
        split.
        { rewrite !PTree.gso by discriminate. rewrite PTree.gss. do 3 f_equal. lia. }
        split; [exact Hso1_u|]. split; [exact Hdo1_u|].
        split; [lia|]. split; [lia|]. split; [lia|].
        split.
        { rewrite Hwwa in HloadT.
          apply (copied_sub m mp bi edge bw outedge C (64 * cq + 0) (64 * cq + ds)); [|lia|lia].
          eapply copied_app with (mid := 64 * cq + (ds - ss0)).
          - apply (copied_word m mp bi edge bw outedge C cq (k0 + 1) (64 - (ds - ss0)) 0 (ds - ss0) _ S1
              HloadT HS1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold C; lia)).
            intros i Hi. split; [lia|]. rewrite copy_partial_cross_value_bits by lia.
            rewrite zlt_true by lia. reflexivity.
          - apply (copied_word m mp bi edge bw outedge C cq k0 (- (ds - ss0)) (ds - ss0) ds _ S0
              HloadT HS0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold C; lia)).
            intros i Hi. split; [lia|]. rewrite copy_partial_cross_value_bits by lia.
            rewrite zlt_false by lia. rewrite zlt_true by lia. f_equal; lia. }
        split.
        { intros old' Hold'. rewrite Hold in Hold'. injection Hold' as <-.
          eexists. split; [exact HloadT|]. intros i Hi. rewrite Hshift in Hi.
          rewrite copy_partial_cross_value_bits by lia.
          rewrite zlt_false by lia. rewrite zlt_false by lia. reflexivity. }
        split.
        { intros chunk b ofs Hout.
          assert (Hout' : b <> bw \/ ofs + size_chunk chunk <= wwa \/ wwa + size_chunk Mint64 <= ofs).
          { change (size_chunk Mint64) with 8. rewrite Hwwa. unfold dA in Hout. rewrite Hwwa in Hout.
            destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
          erewrite Mem.load_store_other; [|exact SP|exact Hout'].
          erewrite Mem.load_store_other; [|exact SL|exact Hout'].
          eapply Mem.load_store_other; [exact SC|exact Hout']. }
        split.
        { intros b ofs kind p Hp. eapply Mem.perm_store_1; [exact SP|].
          eapply Mem.perm_store_1; [exact SL|]. eapply Mem.perm_store_1; eauto. }
        { intros b Hv. eapply Mem.store_valid_block_1; [exact SP|].
          eapply Mem.store_valid_block_1; [exact SL|]. eapply Mem.store_valid_block_1; eauto. }
Qed.
Theorem eval_copy_helper_wide :
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_output_cells_at mf bw outedge cursor cells /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - n) / 64) \/
      wwa + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  destruct wh_cursor as (Hcur & Hds). destruct wh_rc as (Hrc & Hss0 & HR0).
  destruct wh_bounds as (HNC & HCM & HO & Hbd). pose proof wh_k0 as Hk0.
  assert (Hcq : 1 <= cq) by lia.
  destruct wide_prefix as (le1 & m1 & so1 & do1 & k1 & ss1 & Hex1 &
    KP & KD & KS & KN & Hso & Hdo & Hss1 & Hk1 & Hal & Hcop1 & Htop & Heff1 & Hperm1 & Hvalid1).
  assert (Hwd : (cursor - 1) / 64 = if Z.eq_dec ds 0 then cq - 1 else cq).
  { destruct (Z.eq_dec ds 0); symmetry;
      [apply (Z.div_unique (cursor - 1) 64 (cq - 1) 63)|apply (Z.div_unique (cursor - 1) 64 cq (ds - 1))]; lia. }
  assert (Hwwa : wwa = outedge + 8 * (if Z.eq_dec ds 0 then cq - 1 else cq)).
  { unfold wwa, write_word_address. rewrite Hwd. reflexivity. }
  assert (Hlow : 64 * (dA + 1) - (n - ds) = cursor - n) by (unfold dA; lia).
  assert (Ha1 : 1 <= n - ds <= 128) by lia.
  assert (Ha2 : 0 <= dA) by (unfold dA; lia).
  assert (Ha3 : 0 <= k1) by lia.
  assert (Ha4 : n - ds <= 64 * (dA + 1)) by (unfold dA; lia).
  assert (Ha5 : C - 64 * dA - 63 = 64 * k1 + 64 - ss1) by (unfold C, dA; lia).
  destruct (wide_tail Hmodel le1 m m1 bi edge bw outedge C so1 do1 k1 dA ss1 (n - ds)
    KP KD KS KN Hso Hdo Ha1 Ha2 Ha3 Ha4 Ha5) as (le' & mf & out & Hex2 & Hout & Hcop2 & Heff2 & Hperm2 & Hvalid2).
  - (* source words *)
    intros q Hq. destruct (wh_src q ltac:(lia)) as (HE & S & HS). split; [exact HE|].
    exists S. split; [exact HS|]. rewrite Heff1; [exact HS|].
    pose proof (wh_sep q (cursor - 1) ltac:(lia) ltac:(lia)) as Hsp. rewrite Hwd in Hsp.
    change (size_chunk Mint64) with 8. rewrite Hwwa. unfold dA.
    destruct (Z.eq_dec ds 0); destruct Hsp as [H|[H|H]]; first [left; exact H|right; lia].
  - (* destination words *)
    intros p Hp. destruct (wh_dst p ltac:(unfold dA in Hp; lia)) as (H0 & HM & PW & _).
    split; [exact H0|]. split; [exact HM|]. eapply valid_access_perm_preserved; [exact Hperm1|exact PW].
  - (* separation *)
    intros q p Hq Hp. apply wh_sep; [lia|unfold dA in Hp; lia].
  - (* tail range *)
    lia.
  - (* assemble *)
    rewrite Hlow in Hcop2, Heff2.
    replace (64 * (dA + 1)) with (cursor - ds) in Hcop2 by (unfold dA; lia).
    assert (HcopAll : copied m mf bi edge bw outedge C (cursor - n) cursor).
    { eapply copied_app with (mid := cursor - ds); [exact Hcop2|].
      eapply copied_preserved; [exact Hcop1|].
      intros p Hp. apply Heff2. right; right.
      assert (Hpd : p / 64 = cq) by (symmetry; apply (Z.div_unique p 64 cq (p - 64 * cq)); lia).
      rewrite Hpd. unfold dA. lia. }
    destruct Hwrite as (HB & HW & _ & _ & _ & _ & _ & _).
    destruct (wh_src rc ltac:(lia)) as (HE0 & _).
    assert (Hwm : write_word_address outedge cursor <= Ptrofs.max_unsigned).
    { destruct (wh_dst (cursor - 1) ltac:(lia)) as (_ & HM & _). unfold write_word_address. lia. }
    assert (Hrcr : 0 <= rc <= Int64.max_unsigned).
    { destruct (input_cells_word m bi edge rc cells 0 Hinput ltac:(lia)) as (HRr & _).
      replace (rc + 0) with rc in HRr by lia. exact HRr. }
    assert (Hcr : 1 <= cursor <= Int64.max_unsigned) by lia.
    exists mf. split.
    + eapply eval_copy_helper_prefix_composes with (bi := bi) (edge := edge) (rc := rc) (le' := le') (out := out);
        try eassumption.
      rewrite copy_helper_tail_shape.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le1); [exact Hex1|exact Hex2].
    + split.
      * eapply copied_output_cells; [exact Hinput|]. rewrite <- Hlen. exact HcopAll.
      * split.
        -- intros old Hold. fold wwa in Hold.
           destruct (Z.eq_dec ds 0) as [Hz|Hnz].
           ++ destruct (input_cells_word m bi edge rc cells 0 Hinput ltac:(lia)) as (HRr & HEe & S & HS).
              replace (rc + 0) with rc in * by lia.
              assert (Hin : frame_input_bit_at m bi edge (C - (cursor - 1))
                (Z.testbit (Int64.unsigned S) (63 - rc mod 64))).
              { replace (C - (cursor - 1)) with rc by (unfold C; lia).
                split; [exact HRr|]. split; [exact HEe|]. exists S. split; [exact HS|reflexivity]. }
              destruct (HcopAll (cursor - 1) _ ltac:(lia) Hin) as (_ & w & Hw & _).
              exists w. split; [exact Hw|].
              intros i Hi Hio. unfold write_word_shift in Hio.
              replace ((cursor - 1) mod 64) with 63 in Hio
                by (apply (Z.mod_unique (cursor - 1) 64 (cq - 1) 63); lia). lia.
           ++ destruct (Htop old Hold) as (W & HW1 & Hbits).
              exists W. split.
              ** fold wwa. rewrite Heff2; [exact HW1|]. right; right. rewrite Hwwa. unfold dA.
                 destruct (Z.eq_dec ds 0); lia.
              ** intros i Hi Hio. apply Hbits. lia.
        -- split.
           ++ destruct HW as [HWe HWc]. split.
              ** rewrite Heff2 by (left; exact Hbd). rewrite Heff1 by (left; exact Hbd). exact HWe.
              ** rewrite Heff2 by (left; exact Hbd). rewrite Heff1 by (left; exact Hbd). exact HWc.
           ++ split.
              ** intros chunk b ofs Hofs.
                 assert (Hdiv : (cursor - n) / 64 <= cq) by (apply Z.div_le_mono; lia).
                 rewrite Heff2.
                 --- apply Heff1. rewrite Hwwa in *. unfold dA.
                     destruct (Z.eq_dec ds 0); destruct Hofs as [H|[H|H]];
                       first [left; exact H|right; lia].
                 --- rewrite Hwwa in Hofs. unfold dA.
                     destruct (Z.eq_dec ds 0); destruct Hofs as [H|[H|H]];
                       first [left; exact H|right; left; exact H|right; right; lia].
              ** split.
                 --- intros b ofs kind p Hp. apply Hperm2. apply Hperm1. exact Hp.
                 --- intros b Hv. apply Hvalid2. apply Hvalid1. exact Hv.
Qed.

Theorem eval_copyBits_wide_layout :
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_copyBits)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_output_cells_at mf bw outedge cursor cells /\
    write_prefix_at m mf bw outedge cursor /\
    frame_fields_at mf bd base bw outedge (cursor - n) /\
    loads_outside_ranges m mf bd (base + 8) (base + 16)
      bw (outedge + 8 * ((cursor - n) / 64)) (write_word_address outedge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  destruct wh_bounds as (HNC & HCM & HO & Hbd).
  destruct eval_copy_helper_wide as (mi & Hcall & Hcells & Hprefix & Hfields & Houtside & Hperm & Hvalid).
  pose proof Hwrite as (HB & _ & _ & _ & _ & _ & PC & _).
  assert (PCi : Mem.valid_access mi Mint64 bd (base + 8) Writable)
    by (eapply valid_access_perm_preserved; [exact Hperm|exact PC]).
  destruct (eval_copyBits_nonzero_advances m mi bd base bs (Ptrofs.repr sbase)
    bw outedge cursor n HB ltac:(lia) HCM Hcall Hfields PCi)
    as [mf [Hwrapper [Hfieldsf [HcursorOutside [Hpermf Hvalidf]]]]].
  assert (Hbwload : forall ofs, Mem.load Mint64 mf bw ofs = Mem.load Mint64 mi bw ofs).
  { intros ofs. apply HcursorOutside. left. congruence. }
  exists mf. split; [exact Hwrapper|]. split.
  - intros i c Hi. specialize (Hcells i c Hi).
    assert (Hbit : forall q b, frame_output_bit_at mi bw outedge q b -> frame_output_bit_at mf bw outedge q b).
    { intros q b (H0 & w & Hw & Hb). split; [exact H0|]. exists w. split; [rewrite Hbwload; exact Hw|exact Hb]. }
    destruct c as [b|]; cbn [cell_matches] in *; [apply Hbit; exact Hcells|].
    destruct Hcells as [b Hb]. exists b. apply Hbit. exact Hb.
  - split.
    + intros old Hold. destruct (Hprefix old Hold) as (w & Hw & Heq).
      exists w. split; [rewrite Hbwload; exact Hw|exact Heq].
    + split; [exact Hfieldsf|]. split.
      * intros chunk b ofs Hcursor HwordOutside.
        rewrite HcursorOutside by exact Hcursor. apply Houtside. exact HwordOutside.
      * split.
        -- intros b ofs kind p HP. apply Hpermf. apply Hperm; exact HP.
        -- intros b HV. apply Hvalidf. apply Hvalid; exact HV.
Qed.
End WideHelper.
