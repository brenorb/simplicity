(** Every Bit Machine state has a memory representation.

    [bm_rep m L s] relates a C memory and layout to a Bit Machine state; it,
    [bm_separated] and [active_write_writable] are the premises of the local
    replacement theorem [jet_context].  This module shows the relation is
    total on states within the addressability bounds: for every [RunState],
    starting from any memory, one fresh block for cells and one for frame
    items (as in [C/eval.c]) can be filled so that all three premises hold
    and no load from a pre-existing block changes.  Frames are laid out
    consecutively: inactive read frames, the active read frame, the active
    write frame, inactive write frames.

    So the representation predicates exclude no Bit Machine state for a
    reason other than size, and [jet_context] is applicable to every
    context and input. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Zbits Integers AST Memory Values.
Require Import Simplicity.BitMachine.
Require Import C.jet_word_repr C.jet_frame_spec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_frame_constructible.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Lemma frame_words_mul64 k : frame_words (64 * k) = k.
Proof. unfold frame_words; symmetry; apply Z.div_unique with (r := 63); lia. Qed.

(** ** Contents of a write frame's words *)

(** Forward cell [i] lives at absolute offset [n - 1 - i]: bit [q mod 64] of
    word [q / 64]. *)
Definition write_word (cells : list Cell) (n j : Z) : val :=
  Vlong (packed_word (fun r => cell_bit cells (n - 1 - (64 * j + r)))).

Definition write_run (cells : list Cell) (n : Z) : list val :=
  map (fun j => write_word cells n (Z.of_nat j)) (List.seq 0 (Z.to_nat (frame_words n))).

Lemma write_run_length cells n : length (write_run cells n) = Z.to_nat (frame_words n).
Proof. unfold write_run. rewrite map_length, seq_length. reflexivity. Qed.

Lemma write_run_represents m bw base (cells : list Cell) n :
  Z.of_nat (length cells) <= n ->
  (forall i v, nth_error (write_run cells n) i = Some v ->
    Mem.load Mint64 m bw (base + 8 * Z.of_nat i) = Some (Val.load_result Mint64 v)) ->
  frame_output_cells_at m bw base n cells.
Proof.
  intros HLen HLoads i c Hc.
  assert (Hi : (i < length cells)%nat) by (apply nth_error_Some; congruence).
  set (q := n - 1 - Z.of_nat i).
  assert (Hq : 0 <= q < n) by (unfold q; lia).
  destruct (frame_words_bounds n ltac:(lia)) as [HW0 HW].
  assert (Hj : 0 <= q / 64 < frame_words n).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  pose proof (Z.mod_pos_bound q 64 ltac:(lia)) as Hmod.
  pose proof (Z.div_mod q 64 ltac:(lia)) as Hdm.
  assert (Hs : (Z.to_nat (q / 64) < Z.to_nat (frame_words n))%nat) by lia.
  assert (Hnth : nth_error (write_run cells n) (Z.to_nat (q / 64)) =
      Some (write_word cells n (q / 64))).
  { unfold write_run. rewrite nth_error_map.
    rewrite nth_error_seq_in by exact Hs. unfold Datatypes.option_map. cbv beta.
    apply (f_equal Some). apply (f_equal (write_word cells n)). lia. }
  pose proof (HLoads _ _ Hnth) as HL.
  assert (HP : frame_output_bit_at m bw base q (cell_bit cells (Z.of_nat i))).
  { unfold frame_output_bit_at. split; [lia|]. eexists. split.
    - replace (base + 8 * (q / 64)) with (base + 8 * Z.of_nat (Z.to_nat (q / 64))) by lia.
      exact HL.
    - unfold Int64.testbit. rewrite packed_word_testbit by lia. f_equal. unfold q in *. lia. }
  assert (Hbit : cell_bit cells (Z.of_nat i) = match c with Some b => b | None => false end).
  { unfold cell_bit. rewrite Nat2Z.id, Hc. reflexivity. }
  fold q. destruct c as [b|]; cbn [cell_matches].
  - rewrite <- Hbit. exact HP.
  - eexists. exact HP.
Qed.

Lemma write_run_longs cells n i v :
  nth_error (write_run cells n) i = Some v -> exists w, v = Vlong w.
Proof.
  unfold write_run. rewrite nth_error_map.
  destruct (nth_error _ i); [|discriminate]. intros H; injection H as <-.
  eexists; reflexivity.
Qed.

Lemma input_run_longs cells i v :
  nth_error (input_run cells) i = Some v -> exists w, v = Vlong w.
Proof.
  unfold input_run. rewrite nth_error_map.
  destruct (nth_error _ i); [|discriminate]. intros H; injection H as <-.
  eexists; reflexivity.
Qed.

(** ** One frame *)

Inductive frame := FRead (rf : ReadFrame) | FWrite (wf : WriteFrame).

(** The padded stream of a read frame: [read_padding] undefined cells, then
    the frame's cells in order. *)
Definition read_stream (rf : ReadFrame) : list Cell :=
  repeat None (Z.to_nat (read_padding (read_size rf))) ++ rev (prevData rf) ++ nextData rf.

Definition frame_nwords (x : frame) : Z :=
  match x with
  | FRead rf => frame_words (read_size rf)
  | FWrite wf => frame_words (write_size wf)
  end.

Definition frame_run (x : frame) : list val :=
  match x with
  | FRead rf => input_run (read_stream rf)
  | FWrite wf => write_run (rev (writeData wf)) (write_size wf)
  end.

(** Edge and C cursor of a frame whose words start at word index [start]. *)
Definition frame_edge (x : frame) (start : Z) : Z :=
  match x with
  | FRead rf => 8 * (start + frame_nwords x)
  | FWrite _ => 8 * start
  end.

Definition frame_cursor (x : frame) : Z :=
  match x with
  | FRead rf => read_padding (read_size rf) + Z.of_nat (length (prevData rf))
  | FWrite wf => Z.of_nat (writeEmpty wf)
  end.

Lemma read_size_nonneg rf : 0 <= read_size rf.
Proof. unfold read_size. lia. Qed.

Lemma read_stream_length rf :
  Z.of_nat (length (read_stream rf)) = 64 * frame_words (read_size rf).
Proof.
  unfold read_stream. rewrite !app_length, repeat_length, rev_length.
  pose proof (read_size_nonneg rf) as HN.
  destruct (frame_words_bounds (read_size rf) HN) as [_ HW].
  unfold read_padding. unfold read_size in *. lia.
Qed.

Lemma frame_run_length x : Z.of_nat (length (frame_run x)) = frame_nwords x.
Proof.
  destruct x as [rf|wf]; cbn [frame_run frame_nwords].
  - rewrite input_run_length, read_stream_length, frame_words_mul64.
    destruct (frame_words_bounds (read_size rf) (read_size_nonneg rf)). lia.
  - rewrite write_run_length.
    assert (0 <= write_size wf) by (unfold write_size; lia).
    destruct (frame_words_bounds (write_size wf) H). lia.
Qed.

Definition frame_rep (m : mem) (L : bm_layout) (l : frame_loc) (x : frame) : Prop :=
  match x with
  | FRead rf => read_frame_rep m L l rf
  | FWrite wf => write_frame_rep m L l wf
  end.

Section OneFrame.
Variables (m : mem) (L : bm_layout) (k start : Z) (x : frame).
Hypothesis Hk : 0 <= k.
Hypothesis Hstart : 0 <= start.
Hypothesis HItemEnd : 16 * k + 16 <= Ptrofs.max_unsigned.
Hypothesis HCellsEnd : 8 * (start + frame_nwords x) <= Ptrofs.max_unsigned.
Hypothesis HBits : 64 * frame_nwords x <= Int64.max_unsigned.
Hypothesis HRun : forall i v, nth_error (frame_run x) i = Some v ->
  Mem.load Mint64 m (cells_blk L) (8 * start + 8 * Z.of_nat i) =
    Some (Val.load_result Mint64 v).
Hypothesis HEdge : Mem.load Mptr m (frames_blk L) (16 * k) =
  Some (Vptr (cells_blk L) (Ptrofs.repr (frame_edge x start))).
Hypothesis HCursor : Mem.load Mint64 m (frames_blk L) (16 * k + 8) =
  Some (Vlong (Int64.repr (frame_cursor x))).

Lemma frame_rep_built :
  frame_rep m L {| item_ofs := 16 * k; edge_ofs := frame_edge x start |} x.
Proof.
  assert (HM : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  assert (HPM : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  destruct x as [rf|wf]; cbn [frame_rep frame_edge frame_nwords frame_run frame_cursor] in *.
  - pose proof (read_size_nonneg rf) as HN.
    destruct (frame_words_bounds (read_size rf) HN) as [HW0 HW].
    pose proof (read_stream_length rf) as HSL.
    unfold read_frame_rep. cbv zeta. cbn [item_ofs edge_ofs].
    split; [split; lia|]. split; [exists (2 * k); lia|].
    split; [split; [exact HEdge|exact HCursor]|].
    split; [lia|]. split; [unfold read_padding; lia|]. split.
    + intros i Hi.
      assert (Hs : (Z.to_nat (frame_words (read_size rf) - 1 - i) <
          length (input_run (read_stream rf)))%nat).
      { rewrite input_run_length, HSL, frame_words_mul64. lia. }
      destruct (nth_error (input_run (read_stream rf))
        (Z.to_nat (frame_words (read_size rf) - 1 - i))) as [v|] eqn:Hv;
        [|apply nth_error_None in Hv; lia].
      destruct (input_run_longs _ _ _ Hv) as [w ->].
      exists w. pose proof (HRun _ _ Hv) as HL.
      replace (8 * (start + frame_words (read_size rf)) - 8 * (1 + i))
        with (8 * start + 8 * Z.of_nat (Z.to_nat (frame_words (read_size rf) - 1 - i))) by lia.
      exact HL.
    + assert (HAll : frame_input_cells_at m (cells_blk L)
          (8 * start + 8 * frame_words (Z.of_nat (length (read_stream rf)))) 0 (read_stream rf)).
      { apply input_run_represents_at.
        - rewrite HSL. lia.
        - lia.
        - rewrite HSL, frame_words_mul64. lia.
        - exact HRun. }
      rewrite HSL, frame_words_mul64 in HAll.
      unfold read_stream in HAll. apply frame_input_cells_at_app in HAll.
      destruct HAll as [_ HAll]. rewrite repeat_length in HAll.
      replace (8 * (start + frame_words (read_size rf)))
        with (8 * start + 8 * frame_words (read_size rf)) by lia.
      replace (read_padding (read_size rf))
        with (0 + Z.of_nat (Z.to_nat (read_padding (read_size rf))))
        by (unfold read_padding; lia).
      exact HAll.
  - assert (HN : 0 <= write_size wf) by (unfold write_size; lia).
    destruct (frame_words_bounds (write_size wf) HN) as [HW0 HW].
    unfold write_frame_rep. cbv zeta. cbn [item_ofs edge_ofs].
    split; [split; lia|].
    split; [split; [exact HEdge|exact HCursor]|].
    split; [lia|]. split; [apply Z.divide_factor_l|]. split; [lia|]. split; [lia|]. split.
    + intros i Hi.
      assert (Hs : (Z.to_nat i < length (write_run (rev (writeData wf)) (write_size wf)))%nat).
      { rewrite write_run_length. lia. }
      destruct (nth_error (write_run (rev (writeData wf)) (write_size wf)) (Z.to_nat i))
        as [v|] eqn:Hv; [|apply nth_error_None in Hv; lia].
      destruct (write_run_longs _ _ _ _ Hv) as [w ->].
      exists w. pose proof (HRun _ _ Hv) as HL.
      replace (8 * start + 8 * i) with (8 * start + 8 * Z.of_nat (Z.to_nat i)) by lia.
      exact HL.
    + apply write_run_represents; [|exact HRun].
      rewrite rev_length. unfold write_size. lia.
Qed.
End OneFrame.

(** ** A sequence of frames laid out consecutively *)

Fixpoint total_words (xs : list frame) : Z :=
  match xs with
  | [] => 0
  | x :: rest => frame_nwords x + total_words rest
  end.

Fixpoint locs_from (k start : Z) (xs : list frame) : list frame_loc :=
  match xs with
  | [] => []
  | x :: rest =>
      {| item_ofs := 16 * k; edge_ofs := frame_edge x start |} ::
      locs_from (k + 1) (start + frame_nwords x) rest
  end.

Fixpoint items_from (cb : block) (start : Z) (xs : list frame) : list val :=
  match xs with
  | [] => []
  | x :: rest =>
      Vptr cb (Ptrofs.repr (frame_edge x start)) :: Vlong (Int64.repr (frame_cursor x)) ::
      items_from cb (start + frame_nwords x) rest
  end.

Definition cells_content (xs : list frame) : list val := concat (map frame_run xs).

Lemma frame_nwords_nonneg x : 0 <= frame_nwords x.
Proof. rewrite <- frame_run_length. lia. Qed.

Lemma total_words_nonneg xs : 0 <= total_words xs.
Proof.
  induction xs as [|x rest IH]; cbn [total_words]; [lia|].
  pose proof (frame_nwords_nonneg x). lia.
Qed.

Lemma total_words_app xs ys : total_words (xs ++ ys) = total_words xs + total_words ys.
Proof. induction xs as [|x rest IH]; cbn [total_words app]; lia. Qed.

Lemma cells_content_length xs : Z.of_nat (length (cells_content xs)) = total_words xs.
Proof.
  unfold cells_content. induction xs as [|x rest IH]; [reflexivity|].
  cbn [map concat total_words]. rewrite app_length, Nat2Z.inj_add, IH, frame_run_length.
  reflexivity.
Qed.

Lemma cells_content_app xs ys : cells_content (xs ++ ys) = cells_content xs ++ cells_content ys.
Proof. unfold cells_content. rewrite map_app, concat_app. reflexivity. Qed.

Lemma items_from_length cb xs : forall start,
  Z.of_nat (length (items_from cb start xs)) = 2 * Z.of_nat (length xs).
Proof.
  induction xs as [|x rest IH]; intros start; [reflexivity|].
  cbn [items_from length]. specialize (IH (start + frame_nwords x)). lia.
Qed.

Lemma items_from_app cb xs : forall start ys,
  items_from cb start (xs ++ ys) =
    items_from cb start xs ++ items_from cb (start + total_words xs) ys.
Proof.
  induction xs as [|x rest IH]; intros start ys; cbn [items_from app total_words].
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH.
    replace (start + frame_nwords x + total_words rest)
      with (start + (frame_nwords x + total_words rest)) by lia.
    reflexivity.
Qed.

Lemma nth_error_app_left {T} (xs ys : list T) i v :
  nth_error xs i = Some v -> nth_error (xs ++ ys) i = Some v.
Proof.
  intros H. rewrite nth_error_app1; [exact H|]. apply nth_error_Some. congruence.
Qed.

Lemma nth_error_app_right {T} (xs ys : list T) i v :
  nth_error ys i = Some v -> nth_error (xs ++ ys) (length xs + i) = Some v.
Proof.
  intros H. rewrite nth_error_app2 by lia.
  replace (length xs + i - length xs)%nat with i by lia. exact H.
Qed.

Section FrameList.
Variables (m : mem) (L : bm_layout).

Lemma frames_rep_built : forall xs k start,
  0 <= k -> 0 <= start ->
  16 * (k + Z.of_nat (length xs)) <= Ptrofs.max_unsigned ->
  64 * (start + total_words xs) <= Int64.max_unsigned ->
  (forall i v, nth_error (cells_content xs) i = Some v ->
    Mem.load Mint64 m (cells_blk L) (8 * start + 8 * Z.of_nat i) =
      Some (Val.load_result Mint64 v)) ->
  (forall i v, nth_error (items_from (cells_blk L) start xs) i = Some v ->
    Mem.load Mint64 m (frames_blk L) (16 * k + 8 * Z.of_nat i) =
      Some (Val.load_result Mint64 v)) ->
  Forall2 (frame_rep m L) (locs_from k start xs) xs.
Proof.
  assert (HM : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  assert (HPM : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  induction xs as [|x rest IH]; intros k start Hk Hstart HItems HBits HCells HRecs;
    cbn [locs_from]; [constructor|].
  pose proof (frame_nwords_nonneg x) as HW.
  pose proof (total_words_nonneg rest) as HT.
  cbn [total_words length] in *. rewrite Nat2Z.inj_succ in HItems.
  constructor.
  - apply frame_rep_built; try lia.
    + intros i v Hv. apply HCells. unfold cells_content. cbn [map concat].
      apply nth_error_app_left. exact Hv.
    + pose proof (HRecs 0%nat _ eq_refl) as H.
      rewrite Z.mul_0_r, Z.add_0_r in H. exact H.
    + exact (HRecs 1%nat _ eq_refl).
  - apply IH; try lia.
    + intros i v Hv.
      pose proof (HCells (length (frame_run x) + i)%nat v) as H.
      unfold cells_content in H. cbn [map concat] in H.
      specialize (H (nth_error_app_right _ _ _ _ Hv)).
      rewrite Nat2Z.inj_add, frame_run_length in H.
      replace (8 * (start + frame_nwords x) + 8 * Z.of_nat i)
        with (8 * start + 8 * (frame_nwords x + Z.of_nat i)) by lia.
      exact H.
    + intros i v Hv.
      pose proof (HRecs (S (S i)) v Hv) as H.
      replace (16 * (k + 1) + 8 * Z.of_nat i) with (16 * k + 8 * Z.of_nat (S (S i))) by lia.
      exact H.
Qed.
End FrameList.

(** Where the frames of a consecutive layout sit. *)
Lemma locs_from_extent : forall xs k start,
  Forall2 (fun l x => exists j s,
      k <= j < k + Z.of_nat (length xs) /\ item_ofs l = 16 * j /\
      start <= s /\ s + frame_nwords x <= start + total_words xs /\
      edge_ofs l = frame_edge x s)
    (locs_from k start xs) xs.
Proof.
  induction xs as [|x rest IH]; intros k start; cbn [locs_from]; [constructor|].
  pose proof (frame_nwords_nonneg x) as HW.
  pose proof (total_words_nonneg rest) as HT.
  constructor.
  - exists k, start. cbn [item_ofs edge_ofs total_words length].
    rewrite Nat2Z.inj_succ. repeat split; lia.
  - eapply Forall2_impl; [|exact (IH (k + 1) (start + frame_nwords x))].
    intros l y (j & s & Hj & Hitem & Hs & He & Hedge).
    exists j, s. cbn [total_words length]. rewrite Nat2Z.inj_succ.
    repeat split; try assumption; lia.
Qed.

Lemma Forall2_map_right {A B C} (R : A -> C -> Prop) (f : B -> C) :
  forall l (l' : list B), Forall2 R l (map f l') -> Forall2 (fun a b => R a (f b)) l l'.
Proof.
  intros l l'. revert l. induction l' as [|b rest IH]; intros l H; inversion H; subst.
  - constructor.
  - constructor; [assumption|apply IH; assumption].
Qed.

Lemma Forall2_In_left {A B} (R : A -> B -> Prop) l l' a :
  Forall2 R l l' -> In a l -> exists b, R a b.
Proof.
  induction 1 as [|x y l l' Hxy _ IH]; intros HIn; [contradiction|].
  destruct HIn as [<-|HIn]; [exists y; exact Hxy|exact (IH HIn)].
Qed.

(** ** A whole Bit Machine state *)

Definition state_frames (s : RunState) : list frame :=
  map FRead (inactiveReadFrames s) ++
  [FRead (activeReadFrame s); FWrite (activeWriteFrame s)] ++
  map FWrite (inactiveWriteFrames s).

(** Addressability: all cells fit a C bit offset and all frame items fit the
    address space.  These are size bounds only. *)
Definition bm_state_fits (s : RunState) : Prop :=
  64 * total_words (state_frames s) <= Int64.max_unsigned /\
  16 * Z.of_nat (length (state_frames s)) <= Ptrofs.max_unsigned.

Definition state_layout (cb fb : block) (s : RunState) : bm_layout :=
  let irs := map FRead (inactiveReadFrames s) in
  let n1 := Z.of_nat (length irs) in
  let t1 := total_words irs in
  let ar := FRead (activeReadFrame s) in
  let aw := FWrite (activeWriteFrame s) in
  {| cells_blk := cb; frames_blk := fb;
     inactive_read_locs := locs_from 0 0 irs;
     active_read_loc := {| item_ofs := 16 * n1; edge_ofs := frame_edge ar t1 |};
     active_write_loc :=
       {| item_ofs := 16 * (n1 + 1); edge_ofs := frame_edge aw (t1 + frame_nwords ar) |};
     inactive_write_locs :=
       locs_from (n1 + 1 + 1) (t1 + frame_nwords ar + frame_nwords aw)
         (map FWrite (inactiveWriteFrames s)) |}.

Theorem bm_rep_constructible (s : RunState) (m0 : mem) :
  bm_state_fits s ->
  exists m L,
    bm_rep m L s /\ bm_separated L s /\ active_write_writable m L s /\
    ~ Mem.valid_block m0 (cells_blk L) /\ ~ Mem.valid_block m0 (frames_blk L) /\
    (forall b, Mem.valid_block m0 b ->
      Mem.valid_block m b /\
      forall chunk ofs, Mem.load chunk m b ofs = Mem.load chunk m0 b ofs).
Proof.
  intros [HBits HItems].
  assert (HM : Int64.max_unsigned = 18446744073709551615) by reflexivity.
  assert (HPM : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  set (irs := map FRead (inactiveReadFrames s)).
  set (ar := FRead (activeReadFrame s)).
  set (aw := FWrite (activeWriteFrame s)).
  set (iws := map FWrite (inactiveWriteFrames s)).
  set (mid := [ar; aw]).
  assert (HFrames : state_frames s = irs ++ mid ++ iws) by reflexivity.
  set (n1 := Z.of_nat (length irs)).
  set (t1 := total_words irs).
  pose proof (total_words_nonneg irs) as Ht1. fold t1 in Ht1.
  pose proof (total_words_nonneg iws) as Ht3.
  pose proof (frame_nwords_nonneg ar) as HWar.
  pose proof (frame_nwords_nonneg aw) as HWaw.
  assert (HTmid : total_words mid = frame_nwords ar + frame_nwords aw).
  { unfold mid. cbn [total_words]. lia. }
  rewrite HFrames, !total_words_app, HTmid in HBits. fold t1 in HBits.
  rewrite HFrames, !app_length, !Nat2Z.inj_add in HItems.
  change (Z.of_nat (length mid)) with 2 in HItems. fold n1 in HItems.
  destruct (alloc_word_run m0 (cells_content (state_frames s)))
    as (m1 & cb & HF1 & HV1 & HL1 & _ & HR1 & HO1 & _ & _ & HVB1).
  destruct (alloc_word_run m1 (items_from cb 0 (state_frames s)))
    as (m2 & fb & HF2 & HV2 & HL2 & HA2 & _ & HO2 & HP2 & _ & HVB2).
  assert (Ncf : cb <> fb) by (intros ->; exact (HF2 HV1)).
  set (L := state_layout cb fb s).
  assert (HCells : forall i v, nth_error (cells_content (state_frames s)) i = Some v ->
      Mem.load Mint64 m2 cb (8 * Z.of_nat i) = Some (Val.load_result Mint64 v)).
  { intros i v Hv. rewrite HO2 by exact HV1. exact (HL1 i v Hv). }
  rewrite HFrames, !cells_content_app in HCells.
  rewrite HFrames, !items_from_app in HL2. rewrite Z.add_0_l, HTmid in HL2. fold t1 in HL2.
  (* the three segments *)
  assert (Hn1 : 0 <= n1) by (unfold n1; lia).
  assert (Hn3 : 0 <= Z.of_nat (length iws)) by lia.
  assert (HSeg1 : Forall2 (frame_rep m2 L) (locs_from 0 0 irs) irs).
  { apply frames_rep_built; [lia|lia|fold n1; lia|fold t1; lia| |].
    - intros i v Hv. apply HCells. apply nth_error_app_left. exact Hv.
    - intros i v Hv. apply HL2. apply nth_error_app_left. exact Hv. }
  assert (HSeg2 : Forall2 (frame_rep m2 L) (locs_from n1 t1 mid) mid).
  { apply frames_rep_built;
      [lia|lia|change (Z.of_nat (length mid)) with 2; lia|rewrite HTmid; lia| |].
    - intros i v Hv.
      pose proof (HCells _ v (nth_error_app_right _ _ _ _ (nth_error_app_left _ _ _ _ Hv))) as H.
      rewrite Nat2Z.inj_add, cells_content_length in H. fold t1 in H.
      replace (8 * t1 + 8 * Z.of_nat i) with (8 * (t1 + Z.of_nat i)) by lia. exact H.
    - intros i v Hv.
      pose proof (HL2 _ v (nth_error_app_right _ _ _ _ (nth_error_app_left _ _ _ _ Hv))) as H.
      rewrite Nat2Z.inj_add, items_from_length in H. fold n1 in H.
      replace (16 * n1 + 8 * Z.of_nat i) with (8 * (2 * n1 + Z.of_nat i)) by lia. exact H. }
  assert (HSeg3 : Forall2 (frame_rep m2 L)
      (locs_from (n1 + 1 + 1) (t1 + frame_nwords ar + frame_nwords aw) iws) iws).
  { apply frames_rep_built; [lia|lia|lia|lia| |].
    - intros i v Hv.
      pose proof (HCells _ v (nth_error_app_right _ _ _ _ (nth_error_app_right _ _ _ _ Hv))) as H.
      rewrite !Nat2Z.inj_add, !cells_content_length, HTmid in H. fold t1 in H.
      replace (8 * (t1 + frame_nwords ar + frame_nwords aw) + 8 * Z.of_nat i)
        with (8 * (t1 + (frame_nwords ar + frame_nwords aw + Z.of_nat i))) by lia. exact H.
    - intros i v Hv.
      replace (t1 + frame_nwords ar + frame_nwords aw)
        with (t1 + (frame_nwords ar + frame_nwords aw)) in Hv by lia.
      pose proof (HL2 _ v (nth_error_app_right _ _ _ _ (nth_error_app_right _ _ _ _ Hv))) as H.
      rewrite !Nat2Z.inj_add, !items_from_length in H. fold n1 in H.
      change (Z.of_nat (length mid)) with 2 in H.
      replace (16 * (n1 + 1 + 1) + 8 * Z.of_nat i)
        with (8 * (2 * n1 + (2 * 2 + Z.of_nat i))) by lia. exact H. }
  pose proof (locs_from_extent irs 0 0) as HExt1.
  pose proof (locs_from_extent iws (n1 + 1 + 1) (t1 + frame_nwords ar + frame_nwords aw)) as HExt3.
  unfold mid in HSeg2. cbn [locs_from] in HSeg2.
  inversion HSeg2 as [|la xa lrest xrest HRepA HSeg2']; subst.
  inversion HSeg2' as [|lw xw lrest' xrest' HRepW _]; subst.
  exists m2, L.
  split; [|split; [|split; [|split; [|split]]]].
  - (* bm_rep *)
    split; [exact Ncf|]. split; [exact (Forall2_map_right _ _ _ _ HSeg1)|].
    split; [exact HRepA|]. split; [exact HRepW|].
    exact (Forall2_map_right _ _ _ _ HSeg3).
  - (* bm_separated *)
    unfold bm_separated. cbv zeta.
    change (active_write_loc L) with
      {| item_ofs := 16 * (n1 + 1); edge_ofs := frame_edge aw (t1 + frame_nwords ar) |}.
    change (active_read_loc L) with {| item_ofs := 16 * n1; edge_ofs := frame_edge ar t1 |}.
    change (inactive_read_locs L) with (locs_from 0 0 irs).
    change (inactive_write_locs L) with
      (locs_from (n1 + 1 + 1) (t1 + frame_nwords ar + frame_nwords aw) iws).
    cbn [item_ofs edge_ofs].
    assert (HHi : write_region_hi
        {| item_ofs := 16 * (n1 + 1); edge_ofs := frame_edge aw (t1 + frame_nwords ar) |}
        (activeWriteFrame s) = 8 * (t1 + frame_nwords ar) + 8 * frame_nwords aw).
    { reflexivity. }
    rewrite HHi. change (frame_edge aw (t1 + frame_nwords ar)) with (8 * (t1 + frame_nwords ar)).
    split; [|split].
    + intros l [<-|HIn].
      * cbn [item_ofs]. left. lia.
      * apply in_app_or in HIn. destruct HIn as [HIn|HIn].
        -- destruct (Forall2_In_left _ _ _ _ HExt1 HIn) as (x & j & s' & Hj & Hitem & _).
           fold n1 in Hj. rewrite Hitem. left. lia.
        -- destruct (Forall2_In_left _ _ _ _ HExt3 HIn) as (x & j & s' & Hj & Hitem & _).
           rewrite Hitem. right. lia.
    + constructor.
      * right. cbn [edge_ofs]. change (frame_edge ar t1) with (8 * (t1 + frame_nwords ar)). lia.
      * apply Forall2_map_right in HExt1.
        eapply Forall2_impl; [|exact HExt1].
        intros l rf (j & s' & _ & _ & Hs & He & Hedge). right. rewrite Hedge.
        fold t1 in He. change (frame_edge (FRead rf) s') with (8 * (s' + frame_nwords (FRead rf))).
        lia.
    + apply Forall2_map_right in HExt3.
      eapply Forall2_impl; [|exact HExt3].
      intros l wf (j & s' & _ & _ & Hs & _ & Hedge). left. rewrite Hedge.
      change (frame_edge (FWrite wf) s') with (8 * s'). lia.
  - (* active_write_writable *)
    unfold active_write_writable. cbv zeta.
    change (active_write_loc L) with
      {| item_ofs := 16 * (n1 + 1); edge_ofs := frame_edge aw (t1 + frame_nwords ar) |}.
    change (write_region_hi _ (activeWriteFrame s))
      with (8 * (t1 + frame_nwords ar) + 8 * frame_nwords aw).
    cbn [item_ofs edge_ofs]. change (frame_edge aw (t1 + frame_nwords ar)) with (8 * (t1 + frame_nwords ar)).
    split.
    + pose proof (HA2 (Z.to_nat (2 * (n1 + 1) + 1))) as H.
      replace (8 * Z.of_nat (Z.to_nat (2 * (n1 + 1) + 1))) with (16 * (n1 + 1) + 8) in H
        by (unfold n1; lia).
      apply H.
      pose proof (items_from_length cb (state_frames s) 0) as HLen.
      rewrite HFrames, !app_length, !Nat2Z.inj_add in HLen.
      change (Z.of_nat (length mid)) with 2 in HLen. fold n1 in HLen.
      rewrite HFrames. unfold n1 in *. lia.
    + intros ofs Hofs.
      assert (HPerm1 : Mem.perm m1 cb ofs Cur Writable).
      { eapply Mem.perm_implies; [|apply perm_F_any]. apply HR1.
        pose proof (cells_content_length (state_frames s)) as HLen.
        rewrite HFrames, !total_words_app, HTmid in HLen. fold t1 in HLen.
        rewrite HFrames. lia. }
      assert (HVA : Mem.valid_access m1 Mint8unsigned cb ofs Writable).
      { split; [|apply Z.divide_1_l]. intros o Ho. change (size_chunk Mint8unsigned) with 1 in Ho.
        replace o with ofs by lia. exact HPerm1. }
      exact (Mem.valid_access_perm _ _ _ _ Cur _ (HP2 _ _ _ _ HV1 HVA)).
  - exact HF1.
  - intros HV. exact (HF2 (HVB1 _ HV)).
  - intros b Hb. split; [apply HVB2; apply HVB1; exact Hb|].
    intros chunk ofs. rewrite HO2 by (apply HVB1; exact Hb). apply HO1. exact Hb.
Qed.
