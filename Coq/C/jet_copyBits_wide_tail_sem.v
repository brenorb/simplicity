(** The destination-aligned tail of copyBitsHelper for remaining counts up
    to two words: execution and position-level postcondition, for the loop
    branch (source not word-aligned) and the [memcpy] branch (source aligned).
    The [memcpy] branch is conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_encoding.
Require Import C.jet_word_bits C.jet_frame_constants.
Require Import C.jet_copyBits_exec C.jet_copyBits_helper_exec.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing.
Require Import C.jet_copyBits_aligned_short C.jet_copyBits_aligned_crossing.
Require Import C.jet_memcpy_model C.jet_copyBits_memcpy_exec C.jet_copyBits_memcpy_helper.
Require Import C.jet_copyBits_wide_tail C.jet_copyBits_wide_memcpy C.jet_copyBits_wide_sem.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 120.

Lemma ptrofs_sub_unsigned x c :
  0 <= c <= Ptrofs.unsigned x ->
  Ptrofs.unsigned (Ptrofs.sub x (Ptrofs.repr c)) = Ptrofs.unsigned x - c.
Proof.
  intros Hc. unfold Ptrofs.sub. pose proof (Ptrofs.unsigned_range_2 x) as Hx.
  rewrite (Ptrofs.unsigned_repr c) by lia. apply Ptrofs.unsigned_repr. lia.
Qed.

Lemma div64_unique a r : 0 <= r < 64 -> (64 * a + r) / 64 = a.
Proof. intros Hr. symmetry. apply (Z.div_unique (64 * a + r) 64 a r); lia. Qed.

Section WideTail.
Variable Hmodel : memcpy_model.
Variables (le : temp_env) (m0 m1 : mem) (bi : block) (edge : Z) (bw : block) (outedge C : Z).
Variables (so do : ptrofs) (k1 dA ss n1 : Z).
Hypothesis HP : le!_src_ptr = Some (Vptr bi so).
Hypothesis HD : le!_dst_ptr = Some (Vptr bw do).
Hypothesis HS : le!_src_shift = Some (Vlong (Int64.repr ss)).
Hypothesis HN : le!_n = Some (Vlong (Int64.repr n1)).
Hypothesis Hso : Ptrofs.unsigned so = edge - 8 * (1 + k1).
Hypothesis Hdo : Ptrofs.unsigned do = outedge + 8 * dA.
Hypothesis Hn : 1 <= n1 <= 128.
Hypothesis HdA : 0 <= dA.
Hypothesis Hpos : n1 <= 64 * (dA + 1).
Hypothesis Halign : C - 64 * dA - 63 = 64 * k1 + 64 - ss.
Hypothesis Hsrc : forall q, 64 * k1 + 64 - ss <= q < 64 * k1 + 64 - ss + n1 ->
  8 * (1 + q / 64) <= edge <= Ptrofs.max_unsigned /\
  exists S, Mem.load Mint64 m0 bi (edge - 8 * (1 + q / 64)) = Some (Vlong S) /\
    Mem.load Mint64 m1 bi (edge - 8 * (1 + q / 64)) = Some (Vlong S).
Hypothesis Hdst : forall p, 64 * (dA + 1) - n1 <= p < 64 * (dA + 1) ->
  0 <= outedge + 8 * (p / 64) /\ outedge + 8 * (p / 64) + 8 <= Ptrofs.max_unsigned /\
  Mem.valid_access m1 Mint64 bw (outedge + 8 * (p / 64)) Writable.
Hypothesis Hsep : forall q p,
  64 * k1 + 64 - ss <= q < 64 * k1 + 64 - ss + n1 -> 64 * (dA + 1) - n1 <= p < 64 * (dA + 1) ->
  bi <> bw \/ edge - 8 * (1 + q / 64) + 8 <= outedge + 8 * (p / 64) \/
    outedge + 8 * (p / 64) + 8 <= edge - 8 * (1 + q / 64).

Definition wide_tail_post (le' : temp_env) (mf : mem) (out : outcome) : Prop :=
  (out = Out_normal \/ out = Out_return None) /\
  copied m0 mf bi edge bw outedge C (64 * (dA + 1) - n1) (64 * (dA + 1)) /\
  (forall chunk b ofs,
    b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((64 * (dA + 1) - n1) / 64) \/
      outedge + 8 * (dA + 1) <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m1 b ofs) /\
  (forall b ofs kind p, Mem.perm m1 b ofs kind p -> Mem.perm mf b ofs kind p) /\
  (forall b, Mem.valid_block m1 b -> Mem.valid_block mf b).

(** Source word [k1 + j], available whenever some needed stream position lies in it. *)
Lemma tail_src_word j :
  0 <= j -> 64 * k1 + 64 - ss <= 64 * (k1 + j) + 63 -> 64 * (k1 + j) < 64 * k1 + 64 - ss + n1 ->
  8 * (1 + (k1 + j)) <= edge <= Ptrofs.max_unsigned /\
  exists S, Mem.load Mint64 m0 bi (edge - 8 * (1 + (k1 + j))) = Some (Vlong S) /\
    Mem.load Mint64 m1 bi (edge - 8 * (1 + (k1 + j))) = Some (Vlong S).
Proof.
  intros Hj Hlo Hhi.
  set (q := Z.max (64 * (k1 + j)) (64 * k1 + 64 - ss)).
  assert (Hq : 64 * k1 + 64 - ss <= q < 64 * k1 + 64 - ss + n1) by (unfold q; lia).
  assert (Hqd : q / 64 = k1 + j).
  { symmetry. apply (Z.div_unique q 64 (k1 + j) (q - 64 * (k1 + j))); unfold q; lia. }
  pose proof (Hsrc q Hq) as H. rewrite Hqd in H. exact H.
Qed.

(** Destination word [dA - j], writable whenever some needed position lies in it. *)
Lemma tail_dst_word j :
  0 <= j -> 64 * j < n1 ->
  0 <= outedge + 8 * (dA - j) /\ outedge + 8 * (dA - j) + 8 <= Ptrofs.max_unsigned /\
  Mem.valid_access m1 Mint64 bw (outedge + 8 * (dA - j)) Writable.
Proof.
  intros Hj Hn1.
  assert (Hp : 64 * (dA + 1) - n1 <= 64 * (dA - j) + 63 < 64 * (dA + 1)) by lia.
  pose proof (Hdst _ Hp) as H. rewrite div64_unique in H by lia. exact H.
Qed.

Lemma tail_sep_word j i :
  0 <= j -> 64 * k1 + 64 - ss <= 64 * (k1 + j) + 63 -> 64 * (k1 + j) < 64 * k1 + 64 - ss + n1 ->
  0 <= i -> 64 * i < n1 ->
  bi <> bw \/ edge - 8 * (1 + (k1 + j)) + 8 <= outedge + 8 * (dA - i) \/
    outedge + 8 * (dA - i) + 8 <= edge - 8 * (1 + (k1 + j)).
Proof.
  intros Hj Hlo Hhi Hi Hn1.
  set (q := Z.max (64 * (k1 + j)) (64 * k1 + 64 - ss)).
  assert (Hq : 64 * k1 + 64 - ss <= q < 64 * k1 + 64 - ss + n1) by (unfold q; lia).
  assert (Hqd : q / 64 = k1 + j).
  { symmetry. apply (Z.div_unique q 64 (k1 + j) (q - 64 * (k1 + j))); unfold q; lia. }
  assert (Hp : 64 * (dA + 1) - n1 <= 64 * (dA - i) + 63 < 64 * (dA + 1)) by lia.
  pose proof (Hsep q _ Hq Hp) as H. rewrite Hqd, div64_unique in H by lia. exact H.
Qed.

Lemma tail_low_word j :
  0 <= j -> 64 * j < n1 <= 64 * (j + 1) -> (64 * (dA + 1) - n1) / 64 = dA - j.
Proof.
  intros Hj Hn1. symmetry.
  apply (Z.div_unique (64 * (dA + 1) - n1) 64 (dA - j) (64 * (j + 1) - n1)); lia.
Qed.

(** * Loop branch *)
Lemma wide_tail_loop :
  1 <= ss <= 63 ->
  exists le' mf out,
    Clight2.exec_stmt ge0 empty_env le m1 copy_tail_after_partial E0 le' mf out /\
    wide_tail_post le' mf out.
Proof.
  intros Hss.
  destruct (tail_src_word 0 ltac:(lia) ltac:(lia) ltac:(lia)) as (HE0 & S0 & HS0 & HS0').
  replace (k1 + 0) with k1 in * by lia.
  destruct (tail_dst_word 0 ltac:(lia) ltac:(lia)) as (HA0 & HAM & PA).
  replace (dA - 0) with dA in * by lia.
  rewrite <- Hso in HS0'. rewrite <- Hdo in PA.
  destruct (Mem.valid_access_store m1 Mint64 bw (Ptrofs.unsigned do)
    (Vlong (copy_loop_value ss S0)) PA) as [mi SI].
  assert (HcopA_hi : forall mm W,
    Mem.load Mint64 mm bw (outedge + 8 * dA) = Some (Vlong W) ->
    (forall i, 64 - ss <= i < 64 -> Int64.testbit W i = Int64.testbit S0 (i - (64 - ss))) ->
    copied m0 mm bi edge bw outedge C (64 * dA + (64 - ss)) (64 * dA + 64)).
  { intros mm W HW Hbits.
    apply (copied_word m0 mm bi edge bw outedge C dA k1 (- (64 - ss)) (64 - ss) 64 W S0 HW HS0 HdA ltac:(lia) ltac:(lia) ltac:(lia)).
    intros i Hi. split; [lia|]. rewrite Hbits by exact Hi. f_equal; lia. }
  destruct (Z_le_gt_dec n1 ss) as [Hshort|Hlong].
  - (* single short iteration *)
    exists (copy_loop_env le ss S0), mi, (Out_return None). split.
    + eapply exec_copy_choice_from_loop; [exact Hss|exact HS|].
      eapply exec_copy_loop_short with (src_ofs := so) (dst_ofs := do); try eassumption; lia.
    + split; [right; reflexivity|]. split.
      * eapply copied_sub with (lo := 64 * dA + (64 - ss)) (hi := 64 * dA + 64); [|lia|lia].
        eapply HcopA_hi.
        -- rewrite <- Hdo. exact (Mem.load_store_same _ _ _ _ _ _ SI).
        -- intros i Hi. rewrite copy_loop_value_bits by lia. rewrite zlt_false by lia. reflexivity.
      * split.
        -- intros chunk b ofs Hout. eapply Mem.load_store_other; [exact SI|].
           rewrite Hdo. rewrite (tail_low_word 0) in Hout by lia.
           change (size_chunk Mint64) with 8. destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
        -- split; [intros b ofs kind p Hp; eapply Mem.perm_store_1; eauto|
             intros b Hv; eapply Mem.store_valid_block_1; eauto].
  - (* the first word is completed from the next source word *)
    destruct (tail_src_word 1 ltac:(lia) ltac:(lia) ltac:(lia)) as (HE1 & S1 & HS1 & HS1').
    assert (Hso1 : Ptrofs.unsigned (Ptrofs.sub so (Ptrofs.repr 8)) = edge - 8 * (1 + (k1 + 1))).
    { rewrite ptrofs_sub_unsigned by lia. lia. }
    pose proof (tail_sep_word 1 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsep10.
    replace (dA - 0) with dA in Hsep10 by lia.
    assert (HS1i : Mem.load Mint64 mi bi (Ptrofs.unsigned (Ptrofs.sub so (Ptrofs.repr 8))) = Some (Vlong S1)).
    { rewrite Hso1. erewrite Mem.load_store_other; [exact HS1'|exact SI|].
      rewrite Hdo. change (size_chunk Mint64) with 8. exact Hsep10. }
    assert (PAi : Mem.valid_access mi Mint64 bw (Ptrofs.unsigned do) Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mi Mint64 bw (Ptrofs.unsigned do)
      (Vlong (copy_loop_join_value ss S0 S1)) PAi) as [m2 S2].
    assert (HloadA : Mem.load Mint64 m2 bw (outedge + 8 * dA) = Some (Vlong (copy_loop_join_value ss S0 S1))).
    { rewrite <- Hdo. exact (Mem.load_store_same _ _ _ _ _ _ S2). }
    assert (HcopA : copied m0 m2 bi edge bw outedge C (64 * dA) (64 * dA + 64)).
    { replace (64 * dA) with (64 * dA + 0) at 1 by lia.
      eapply copied_app with (mid := 64 * dA + (64 - ss)).
      - apply (copied_word m0 m2 bi edge bw outedge C dA (k1 + 1) ss 0 (64 - ss) _ S1 HloadA HS1 HdA ltac:(lia) ltac:(lia) ltac:(lia)).
        intros i Hi. split; [lia|]. rewrite copy_loop_join_value_bits by lia.
        rewrite zlt_true by lia. reflexivity.
      - eapply HcopA_hi; [exact HloadA|].
        intros i Hi. rewrite copy_loop_join_value_bits by lia. rewrite zlt_false by lia. reflexivity. }
    assert (Heff2 : forall chunk b ofs,
      b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * dA \/ outedge + 8 * (dA + 1) <= ofs ->
      Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs).
    { intros chunk b ofs Hout.
      erewrite Mem.load_store_other; [|exact S2|rewrite Hdo; change (size_chunk Mint64) with 8;
        destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]].
      eapply Mem.load_store_other; [exact SI|]. rewrite Hdo. change (size_chunk Mint64) with 8.
      destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
    assert (Hperm2 : forall b ofs kind p, Mem.perm m1 b ofs kind p -> Mem.perm m2 b ofs kind p).
    { intros b ofs kind p Hp. eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; eauto. }
    assert (Hvalid2 : forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b).
    { intros b Hv. eapply Mem.store_valid_block_1; [exact S2|]. eapply Mem.store_valid_block_1; eauto. }
    destruct (Z_le_gt_dec n1 64) as [Hone|Htwo].
    + (* returns after the first full word *)
      eexists _, m2, (Out_return None). split.
      * eapply exec_copy_choice_from_loop; [exact Hss|exact HS|].
        eapply exec_copy_loop_full with (src_ofs := so) (dst_ofs := do) (mi := mi); try eassumption; lia.
      * split; [right; reflexivity|]. split.
        -- eapply copied_sub; [exact HcopA|lia|lia].
        -- split.
           ++ intros chunk b ofs Hout. apply Heff2. rewrite (tail_low_word 0) in Hout by lia.
              replace (dA - 0) with dA in Hout by lia. exact Hout.
           ++ split; [exact Hperm2|exact Hvalid2].
    + (* a second destination word *)
      set (le2 := copy_loop_next_env (copy_loop_join_env (copy_loop_env le ss S0) ss S0 S1) bi so bw do n1).
      assert (HIter : Clight2.exec_stmt ge0 empty_env le m1 copy_loop_body E0 le2 m2 Out_normal).
      { eapply exec_copy_loop_iter with (mi := mi); try eassumption; lia. }
      assert (HP2 : le2!_src_ptr = Some (Vptr bi (Ptrofs.sub so (Ptrofs.repr 8))))
        by (unfold le2, copy_loop_next_env; apply PTree.gss).
      assert (HD2 : le2!_dst_ptr = Some (Vptr bw (Ptrofs.sub do (Ptrofs.repr 8)))).
      { unfold le2, copy_loop_next_env. rewrite PTree.gso by discriminate. apply PTree.gss. }
      assert (HN2 : le2!_n = Some (Vlong (Int64.repr (n1 - 64)))).
      { unfold le2, copy_loop_next_env. rewrite !PTree.gso by discriminate. apply PTree.gss. }
      assert (HS2 : le2!_src_shift = Some (Vlong (Int64.repr ss))).
      { unfold le2, copy_loop_next_env, copy_loop_join_env, copy_loop_env.
        rewrite !PTree.gso by discriminate. exact HS. }
      destruct (tail_dst_word 1 ltac:(lia) ltac:(lia)) as (HB0 & HBM & PB).
      assert (Hdo1 : Ptrofs.unsigned (Ptrofs.sub do (Ptrofs.repr 8)) = outedge + 8 * (dA - 1)).
      { rewrite ptrofs_sub_unsigned by lia. lia. }
      pose proof (tail_sep_word 1 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsep11.
      assert (HS1_2 : Mem.load Mint64 m2 bi (Ptrofs.unsigned (Ptrofs.sub so (Ptrofs.repr 8))) = Some (Vlong S1)).
      { erewrite Mem.load_store_other; [exact HS1i|exact S2|].
        rewrite Hso1, Hdo. change (size_chunk Mint64) with 8. exact Hsep10. }
      assert (PB2 : Mem.valid_access m2 Mint64 bw (Ptrofs.unsigned (Ptrofs.sub do (Ptrofs.repr 8))) Writable).
      { rewrite Hdo1. eapply Mem.store_valid_access_1; [exact S2|]. eapply Mem.store_valid_access_1; eauto. }
      destruct (Mem.valid_access_store m2 Mint64 bw (Ptrofs.unsigned (Ptrofs.sub do (Ptrofs.repr 8)))
        (Vlong (copy_loop_value ss S1)) PB2) as [m3 S3].
      assert (HcopB_hi : forall mm W,
        Mem.load Mint64 mm bw (outedge + 8 * (dA - 1)) = Some (Vlong W) ->
        (forall i, 64 - ss <= i < 64 -> Int64.testbit W i = Int64.testbit S1 (i - (64 - ss))) ->
        copied m0 mm bi edge bw outedge C (64 * (dA - 1) + (64 - ss)) (64 * (dA - 1) + 64)).
      { intros mm W HW Hbits.
        apply (copied_word m0 mm bi edge bw outedge C (dA - 1) (k1 + 1) (- (64 - ss)) (64 - ss) 64 W S1 HW HS1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
        intros i Hi. split; [lia|]. rewrite Hbits by exact Hi. f_equal; lia. }
      assert (HkeepA : forall mm, (forall chunk ofs, ofs + size_chunk chunk <= outedge + 8 * dA \/
          outedge + 8 * dA + 8 <= ofs -> True) ->
        Mem.load Mint64 mm bw (outedge + 8 * dA) = Mem.load Mint64 m2 bw (outedge + 8 * dA) ->
        copied m0 mm bi edge bw outedge C (64 * dA) (64 * dA + 64)).
      { intros mm _ HL. eapply copied_preserved; [exact HcopA|].
        intros p Hp. replace (p / 64) with dA; [exact HL|].
        apply (Z.div_unique p 64 dA (p - 64 * dA)); lia. }
      destruct (Z_le_gt_dec (n1 - 64) ss) as [Hshort2|Hlong2].
      * (* short second word *)
        eexists _, m3, (Out_return None). split.
        -- eapply exec_copy_choice_from_loop; [exact Hss|exact HS|].
           eapply exec_copy_loop_step; [exact HIter|].
           eapply exec_copy_loop_short with (src_ofs := Ptrofs.sub so (Ptrofs.repr 8))
             (dst_ofs := Ptrofs.sub do (Ptrofs.repr 8)); try eassumption; lia.
        -- split; [right; reflexivity|]. split.
           ++ eapply copied_sub with (lo := 64 * (dA - 1) + (64 - ss)) (hi := 64 * dA + 64); [|lia|lia].
              eapply copied_app with (mid := 64 * dA).
              ** replace (64 * dA) with (64 * (dA - 1) + 64) by lia.
                 eapply HcopB_hi.
                 --- rewrite <- Hdo1. exact (Mem.load_store_same _ _ _ _ _ _ S3).
                 --- intros i Hi. rewrite copy_loop_value_bits by lia. rewrite zlt_false by lia. reflexivity.
              ** apply HkeepA; [intros; exact I|].
                 eapply Mem.load_store_other; [exact S3|]. rewrite Hdo1.
                 change (size_chunk Mint64) with 8. right; right; lia.
           ++ split.
              ** intros chunk b ofs Hout. rewrite (tail_low_word 1) in Hout by lia.
                 erewrite Mem.load_store_other; [|exact S3|rewrite Hdo1; change (size_chunk Mint64) with 8;
                   destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]].
                 apply Heff2. destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
              ** split.
                 --- intros b ofs kind p Hp. eapply Mem.perm_store_1; [exact S3|]. apply Hperm2. exact Hp.
                 --- intros b Hv. eapply Mem.store_valid_block_1; [exact S3|]. apply Hvalid2. exact Hv.
      * (* full second word *)
        destruct (tail_src_word 2 ltac:(lia) ltac:(lia) ltac:(lia)) as (HE2 & S2w & HS2w & HS2w').
        assert (Hso2 : Ptrofs.unsigned (Ptrofs.sub (Ptrofs.sub so (Ptrofs.repr 8)) (Ptrofs.repr 8)) =
          edge - 8 * (1 + (k1 + 2))).
        { rewrite ptrofs_sub_unsigned by lia. lia. }
        pose proof (tail_sep_word 2 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsep20.
        replace (dA - 0) with dA in Hsep20 by lia.
        pose proof (tail_sep_word 2 1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsep21.
        assert (HS2_3 : Mem.load Mint64 m3 bi
          (Ptrofs.unsigned (Ptrofs.sub (Ptrofs.sub so (Ptrofs.repr 8)) (Ptrofs.repr 8))) = Some (Vlong S2w)).
        { rewrite Hso2.
          erewrite Mem.load_store_other; [|exact S3|rewrite Hdo1; change (size_chunk Mint64) with 8; exact Hsep21].
          erewrite Mem.load_store_other; [|exact S2|rewrite Hdo; change (size_chunk Mint64) with 8; exact Hsep20].
          erewrite Mem.load_store_other; [exact HS2w'|exact SI|].
          rewrite Hdo; change (size_chunk Mint64) with 8; exact Hsep20. }
        assert (PB3 : Mem.valid_access m3 Mint64 bw (Ptrofs.unsigned (Ptrofs.sub do (Ptrofs.repr 8))) Writable)
          by (eapply Mem.store_valid_access_1; eauto).
        destruct (Mem.valid_access_store m3 Mint64 bw (Ptrofs.unsigned (Ptrofs.sub do (Ptrofs.repr 8)))
          (Vlong (copy_loop_join_value ss S1 S2w)) PB3) as [m4 S4].
        assert (HloadB : Mem.load Mint64 m4 bw (outedge + 8 * (dA - 1)) =
          Some (Vlong (copy_loop_join_value ss S1 S2w))).
        { rewrite <- Hdo1. exact (Mem.load_store_same _ _ _ _ _ _ S4). }
        eexists _, m4, (Out_return None). split.
        -- eapply exec_copy_choice_from_loop; [exact Hss|exact HS|].
           eapply exec_copy_loop_step; [exact HIter|].
           eapply exec_copy_loop_full with (src_ofs := Ptrofs.sub so (Ptrofs.repr 8))
             (dst_ofs := Ptrofs.sub do (Ptrofs.repr 8)) (mi := m3); try eassumption; lia.
        -- split; [right; reflexivity|]. split.
           ++ eapply copied_sub with (lo := 64 * (dA - 1) + 0) (hi := 64 * dA + 64); [|lia|lia].
              eapply copied_app with (mid := 64 * dA).
              ** replace (64 * dA) with (64 * (dA - 1) + 64) by lia.
                 eapply copied_app with (mid := 64 * (dA - 1) + (64 - ss)).
                 --- apply (copied_word m0 m4 bi edge bw outedge C (dA - 1) (k1 + 2) ss 0 (64 - ss) _ S2w HloadB HS2w ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
                     intros i Hi. split; [lia|]. rewrite copy_loop_join_value_bits by lia.
                     rewrite zlt_true by lia. reflexivity.
                 --- eapply HcopB_hi; [exact HloadB|].
                     intros i Hi. rewrite copy_loop_join_value_bits by lia. rewrite zlt_false by lia. reflexivity.
              ** apply HkeepA; [intros; exact I|].
                 erewrite Mem.load_store_other; [|exact S4|rewrite Hdo1; change (size_chunk Mint64) with 8;
                   right; right; lia].
                 eapply Mem.load_store_other; [exact S3|]. rewrite Hdo1.
                 change (size_chunk Mint64) with 8. right; right; lia.
           ++ split.
              ** intros chunk b ofs Hout. rewrite (tail_low_word 1) in Hout by lia.
                 erewrite Mem.load_store_other; [|exact S4|rewrite Hdo1; change (size_chunk Mint64) with 8;
                   destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]].
                 erewrite Mem.load_store_other; [|exact S3|rewrite Hdo1; change (size_chunk Mint64) with 8;
                   destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]].
                 apply Heff2. destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
              ** split.
                 --- intros b ofs kind p Hp. eapply Mem.perm_store_1; [exact S4|].
                     eapply Mem.perm_store_1; [exact S3|]. apply Hperm2. exact Hp.
                 --- intros b Hv. eapply Mem.store_valid_block_1; [exact S4|].
                     eapply Mem.store_valid_block_1; [exact S3|]. apply Hvalid2. exact Hv.
Qed.
End WideTail.
