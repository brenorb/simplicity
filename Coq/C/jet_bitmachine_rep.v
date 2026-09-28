(** Memory representation of Bit Machine states and local jet replacement.

    The C evaluator ([C/eval.c]) keeps the cells of every frame in one
    allocation ([cells]) and every [frameItem] in another ([frames]); the
    frames of each stack occupy disjoint regions of those shared blocks.
    [bm_rep m L s] says that memory [m] represents the Bit Machine state [s]
    under the layout [L]: each frame item holds the edge pointer and the
    C cursor, and the frame's cells hold the corresponding Bit Machine cells.
    It constrains loads only; permissions are a separate premise of a call.

    - A read frame of [n] cells occupies [frame_words n] words ending at
      [edge]; its C offset is the padding plus the Bit Machine cursor, and its
      cells are observed most significant first after the padding
      ([frame_input_cells_at]).  [prevData] is reversed back into frame order.
    - A write frame of [n] cells occupies [frame_words n] words starting at
      [edge]; its C offset is [writeEmpty], and the forward list of written
      cells, [rev writeData], is observed from offset [n - 1] downwards
      ([frame_output_cells_at]).  Unwritten cells are unconstrained, so a C
      writer may change them.

    [jet_context] is the local replacement theorem: from a represented state
    whose active frames hold the jet input and an empty output frame, the
    generated C jet reaches a memory representing the same state as the
    Bit Machine translation of the jet's Simplicity expression.  Every
    inactive frame and the caller's read frame remain represented.  The
    theorem is local to one call; it does not claim that the evaluator
    maintains [bm_rep] between calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_output_slice C.jet_encoding.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

(** * Layouts *)

(** [ROUND_UWORD(n)] and the padding of a read frame ([initReadFrame]). *)
Definition frame_words (n : Z) : Z := (n + 63) / 64.
Definition read_padding (n : Z) : Z := 64 * frame_words n - n.

Lemma frame_words_bounds n : 0 <= n -> 0 <= frame_words n /\ n <= 64 * frame_words n < n + 64.
Proof.
  intros Hn. unfold frame_words.
  pose proof (Z.div_mod (n + 63) 64 ltac:(lia)).
  pose proof (Z.mod_pos_bound (n + 63) 64 ltac:(lia)).
  split; [apply Z.div_pos; lia|lia].
Qed.

(** Location of one frame: its [frameItem] offset in [frames] and the
    offset of its edge in [cells]. *)
Record frame_loc := { item_ofs : Z; edge_ofs : Z }.

Record bm_layout := {
  cells_blk : block;
  frames_blk : block;
  inactive_read_locs : list frame_loc;
  active_read_loc : frame_loc;
  active_write_loc : frame_loc;
  inactive_write_locs : list frame_loc
}.

Definition read_size (rf : ReadFrame) : Z :=
  Z.of_nat (length (prevData rf) + length (nextData rf)).
Definition write_size (wf : WriteFrame) : Z :=
  Z.of_nat (length (writeData wf) + writeEmpty wf).

Definition read_frame_rep (m : mem) (L : bm_layout) (l : frame_loc) (rf : ReadFrame) : Prop :=
  let n := read_size rf in
  frame_base_valid (item_ofs l) /\ (8 | item_ofs l) /\
  frame_fields_at m (frames_blk L) (item_ofs l) (cells_blk L) (edge_ofs l)
    (read_padding n + Z.of_nat (length (prevData rf))) /\
  8 * frame_words n <= edge_ofs l <= Ptrofs.max_unsigned /\
  read_padding n + n <= Int64.max_unsigned /\
  (forall i, 0 <= i < frame_words n ->
    exists w, Mem.load Mint64 m (cells_blk L) (edge_ofs l - 8 * (1 + i)) = Some (Vlong w)) /\
  frame_input_cells_at m (cells_blk L) (edge_ofs l) (read_padding n)
    (rev (prevData rf) ++ nextData rf).

Definition write_frame_rep (m : mem) (L : bm_layout) (l : frame_loc) (wf : WriteFrame) : Prop :=
  let n := write_size wf in
  frame_base_valid (item_ofs l) /\
  frame_fields_at m (frames_blk L) (item_ofs l) (cells_blk L) (edge_ofs l)
    (Z.of_nat (writeEmpty wf)) /\
  0 <= edge_ofs l /\ (8 | edge_ofs l) /\
  edge_ofs l + 8 * frame_words n <= Ptrofs.max_unsigned /\
  n <= Int64.max_unsigned /\
  (forall i, 0 <= i < frame_words n ->
    exists w, Mem.load Mint64 m (cells_blk L) (edge_ofs l + 8 * i) = Some (Vlong w)) /\
  frame_output_cells_at m (cells_blk L) (edge_ofs l) n (rev (writeData wf)).

Definition bm_rep (m : mem) (L : bm_layout) (s : RunState) : Prop :=
  cells_blk L <> frames_blk L /\
  Forall2 (read_frame_rep m L) (inactive_read_locs L) (inactiveReadFrames s) /\
  read_frame_rep m L (active_read_loc L) (activeReadFrame s) /\
  write_frame_rep m L (active_write_loc L) (activeWriteFrame s) /\
  Forall2 (write_frame_rep m L) (inactive_write_locs L) (inactiveWriteFrames s).

(** * Noninterference and call permissions *)

Definition disjoint_ranges (lo1 hi1 lo2 hi2 : Z) : Prop := hi1 <= lo2 \/ hi2 <= lo1.

Definition read_region_lo (l : frame_loc) (rf : ReadFrame) : Z :=
  edge_ofs l - 8 * frame_words (read_size rf).
Definition write_region_hi (l : frame_loc) (wf : WriteFrame) : Z :=
  edge_ofs l + 8 * frame_words (write_size wf).

(** The jet writes only the active write frame's cells and the cursor field
    of its frame item.  Stronger than the value theorems, which permit an
    output frame that overwrites its own input after reading it, this
    condition keeps every other represented frame intact: the caller's read
    frame is part of the final Bit Machine state. *)
Definition bm_separated (L : bm_layout) (s : RunState) : Prop :=
  let aw := active_write_loc L in
  let awf := activeWriteFrame s in
  (forall l, In l (active_read_loc L :: inactive_read_locs L ++ inactive_write_locs L) ->
    disjoint_ranges (item_ofs l) (item_ofs l + 16) (item_ofs aw + 8) (item_ofs aw + 16)) /\
  Forall2 (fun l rf => disjoint_ranges (edge_ofs aw) (write_region_hi aw awf)
                         (read_region_lo l rf) (edge_ofs l))
    (active_read_loc L :: inactive_read_locs L)
    (activeReadFrame s :: inactiveReadFrames s) /\
  Forall2 (fun l wf => disjoint_ranges (edge_ofs aw) (write_region_hi aw awf)
                         (edge_ofs l) (write_region_hi l wf))
    (inactive_write_locs L) (inactiveWriteFrames s).

(** Permissions needed by the call: the cursor field of the output frame item
    and the output frame's backing words are writable. *)
Definition active_write_writable (m : mem) (L : bm_layout) (s : RunState) : Prop :=
  let aw := active_write_loc L in
  Mem.valid_access m Mint64 (frames_blk L) (item_ofs aw + 8) Writable /\
  Mem.range_perm m (cells_blk L) (edge_ofs aw)
    (write_region_hi aw (activeWriteFrame s)) Cur Writable.

Definition jet_args (L : bm_layout) : list val :=
  [Vptr (frames_blk L) (Ptrofs.repr (item_ofs (active_write_loc L)));
   Vptr (frames_blk L) (Ptrofs.repr (item_ofs (active_read_loc L))); Vundef].

(** * Canonical-encoding form of a jet's value theorem *)

(** [jet_local_spec f A B spec] states the public contract of the generated
    jet [f] with input and output observed through [Translate.encode]:
    arbitrary non-wrapping frame items and edges, arbitrary blocks, and the
    exact memory framing of the value theorems. *)
Definition jet_local_spec (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall ge0 m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vundef]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode (spec a)) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs).

(** The value theorems exclude a range starting at [slice_write_low]; it
    begins at or above the word of the lowest output cell. *)
Lemma slice_write_low_bound n edge c :
  1 <= n <= 64 -> n <= c ->
  edge + 8 * ((c - n) / 64) <= slice_write_low n edge c.
Proof.
  intros HN HC. unfold slice_write_low, write_word_address, write_word_shift.
  assert (Hd := Z.div_mod (c - 1) 64 ltac:(lia)).
  assert (Hs := Z.mod_pos_bound (c - 1) 64 ltac:(lia)).
  destruct (Z_le_dec n (1 + (c - 1) mod 64)).
  - assert ((c - n) / 64 = (c - 1) / 64).
    { symmetry. apply Z.div_unique with ((c - 1) mod 64 + 1 - n); lia. }
    lia.
  - assert ((c - n) / 64 < (c - 1) / 64).
    { apply Z.div_lt_upper_bound; lia. }
    lia.
Qed.

Lemma byte_write_low_slice edge c : byte_write_low edge c = slice_write_low 8 edge c.
Proof. reflexivity. Qed.

(** * Preservation of represented frames *)

Lemma load_valid_block chunk m b ofs v :
  Mem.load chunk m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intros H. eapply Mem.valid_access_valid_block.
  eapply Mem.valid_access_implies; [eapply Mem.load_valid_access; eauto|constructor].
Qed.

Section PRESERVE.

Variables (m mf : mem) (cells frames : block) (fitem lo hi : Z).

(** Loads outside the output frame item's cursor field and outside the
    modified cell range [lo, hi) are unchanged. *)
Hypothesis Hpres : forall chunk b ofs, Mem.valid_block m b ->
  (b <> frames \/ ofs + size_chunk chunk <= fitem + 8 \/ fitem + 16 <= ofs) ->
  (b <> cells \/ ofs + size_chunk chunk <= lo \/ hi <= ofs) ->
  Mem.load chunk mf b ofs = Mem.load chunk m b ofs.

Hypothesis Hblocks : cells <> frames.

Lemma cell_load_preserved a v :
  Mem.load Mint64 m cells a = Some v -> a + 8 <= lo \/ hi <= a ->
  Mem.load Mint64 mf cells a = Some v.
Proof.
  intros HL HR. rewrite Hpres; [exact HL|eapply load_valid_block; eauto|left; auto|].
  right. exact HR.
Qed.

Lemma item_preserved base bw edge cursor :
  frame_fields_at m frames base bw edge cursor ->
  disjoint_ranges base (base + 16) (fitem + 8) (fitem + 16) ->
  frame_fields_at mf frames base bw edge cursor.
Proof.
  intros [HE HC] HD. split.
  - rewrite Hpres; [exact HE|eapply load_valid_block; eauto| |left; auto].
    right. unfold disjoint_ranges in HD. cbn. lia.
  - rewrite Hpres; [exact HC|eapply load_valid_block; eauto| |left; auto].
    right. unfold disjoint_ranges in HD. cbn. lia.
Qed.

Lemma cell_matches_impl (P Q : bool -> Prop) c :
  (forall b, P b -> Q b) -> cell_matches P c -> cell_matches Q c.
Proof. destruct c as [b|]; cbn; [auto|intros H [b Hb]; eauto]. Qed.

Lemma input_bit_preserved bw edge q b :
  (forall v, Mem.load Mint64 m bw (edge - 8 * (1 + q / 64)) = Some v ->
    Mem.load Mint64 mf bw (edge - 8 * (1 + q / 64)) = Some v) ->
  frame_input_bit_at m bw edge q b -> frame_input_bit_at mf bw edge q b.
Proof.
  intros HP [HQ [HE [w [HL Hb]]]]. split; [exact HQ|]. split; [exact HE|].
  exists w. auto.
Qed.

Lemma output_bit_preserved bw edge q b :
  (forall v, Mem.load Mint64 m bw (edge + 8 * (q / 64)) = Some v ->
    Mem.load Mint64 mf bw (edge + 8 * (q / 64)) = Some v) ->
  frame_output_bit_at m bw edge q b -> frame_output_bit_at mf bw edge q b.
Proof.
  intros HP [HQ [w [HL Hb]]]. split; [exact HQ|]. exists w. auto.
Qed.

(** A read frame whose items and cells avoid the modified ranges stays
    represented. *)
Lemma read_frame_preserved L l rf :
  cells_blk L = cells -> frames_blk L = frames ->
  read_frame_rep m L l rf ->
  disjoint_ranges (item_ofs l) (item_ofs l + 16) (fitem + 8) (fitem + 16) ->
  hi <= read_region_lo l rf \/ edge_ofs l <= lo ->
  read_frame_rep mf L l rf.
Proof.
  intros HC HF Hrep HD HR. unfold read_frame_rep in *.
  destruct Hrep as [HB [HA [HFd [HE [HM [HW Hcells]]]]]].
  unfold read_region_lo in HR. rewrite HC, HF in *.
  assert (Hn : 0 <= read_size rf) by (unfold read_size; lia).
  destruct (frame_words_bounds _ Hn) as [Hfw0 Hfw].
  split; [exact HB|]. split; [exact HA|]. split; [eapply item_preserved; eauto|].
  split; [exact HE|]. split; [exact HM|]. split.
  - intros i Hi. destruct (HW i Hi) as [w Hw]. exists w.
    eapply cell_load_preserved; [exact Hw|lia].
  - intros i c Hi. specialize (Hcells i c Hi).
    assert (Hlen : (i < length (rev (prevData rf) ++ nextData rf))%nat).
    { apply nth_error_Some. rewrite Hi. discriminate. }
    rewrite app_length, rev_length in Hlen.
    eapply cell_matches_impl; [|exact Hcells]. intros b Hb.
    apply input_bit_preserved; [|exact Hb]. intros v Hv.
    unfold read_padding in *.
    assert (Hq : 0 <= (64 * frame_words (read_size rf) - read_size rf + Z.of_nat i) / 64
                   < frame_words (read_size rf)).
    { split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|].
      unfold read_size in *. lia. }
    eapply cell_load_preserved; [exact Hv|lia].
Qed.

Lemma write_frame_preserved L l wf :
  cells_blk L = cells -> frames_blk L = frames ->
  write_frame_rep m L l wf ->
  disjoint_ranges (item_ofs l) (item_ofs l + 16) (fitem + 8) (fitem + 16) ->
  hi <= edge_ofs l \/ write_region_hi l wf <= lo ->
  write_frame_rep mf L l wf.
Proof.
  intros HC HF Hrep HD HR. unfold write_frame_rep in *.
  destruct Hrep as [HB [HFd [HE0 [HA [HE [HM [HW Hcells]]]]]]].
  unfold write_region_hi in HR. rewrite HC, HF in *.
  assert (Hn : 0 <= write_size wf) by (unfold write_size; lia).
  destruct (frame_words_bounds _ Hn) as [Hfw0 Hfw].
  split; [exact HB|]. split; [eapply item_preserved; eauto|].
  split; [exact HE0|]. split; [exact HA|]. split; [exact HE|]. split; [exact HM|]. split.
  - intros i Hi. destruct (HW i Hi) as [w Hw]. exists w.
    eapply cell_load_preserved; [exact Hw|lia].
  - intros i c Hi. specialize (Hcells i c Hi).
    assert (Hlen : (i < length (rev (writeData wf)))%nat).
    { apply nth_error_Some. rewrite Hi. discriminate. }
    rewrite rev_length in Hlen.
    eapply cell_matches_impl; [|exact Hcells]. intros b Hb.
    apply output_bit_preserved; [|exact Hb]. intros v Hv.
    assert (Hq : 0 <= (write_size wf - 1 - Z.of_nat i) / 64 < frame_words (write_size wf)).
    { unfold write_size in *. split; [apply Z.div_pos; lia|].
      apply Z.div_lt_upper_bound; lia. }
    eapply cell_load_preserved; [exact Hv|lia].
Qed.

End PRESERVE.

Lemma Forall2_zip_in {A B} (P Q R : A -> B -> Prop) xs ys :
  (forall x y, In x xs -> P x y -> Q x y -> R x y) ->
  Forall2 P xs ys -> Forall2 Q xs ys -> Forall2 R xs ys.
Proof.
  intros H HP. induction HP as [|x y xs' ys' Hxy HP' IH]; intros HQ;
    inversion HQ as [|x' y' xs'' ys'' HQxy HQ']; subst; constructor.
  - apply H; [left; reflexivity|assumption|assumption].
  - apply IH; [|exact HQ']. intros a b Ha. apply H. right. exact Ha.
Qed.

(** Cells at or above the initial write cursor survive the jet's writes:
    the top modified word keeps its written prefix, and higher words are
    untouched. *)
Lemma output_bit_after_prefix m mf bw edge cursor q b :
  1 <= cursor <= q ->
  (forall a v, Mem.load Mint64 m bw a = Some v ->
    edge + 8 * ((cursor - 1) / 64) + 8 <= a -> Mem.load Mint64 mf bw a = Some v) ->
  write_prefix_at m mf bw edge cursor ->
  frame_output_bit_at m bw edge q b -> frame_output_bit_at mf bw edge q b.
Proof.
  intros HQ HP Hprefix [H0 [w [HL Hb]]]. split; [exact H0|].
  assert (Hd1 := Z.div_mod (cursor - 1) 64 ltac:(lia)).
  assert (Hs1 := Z.mod_pos_bound (cursor - 1) 64 ltac:(lia)).
  assert (Hd2 := Z.div_mod q 64 ltac:(lia)).
  assert (Hs2 := Z.mod_pos_bound q 64 ltac:(lia)).
  assert (Hge : (cursor - 1) / 64 <= q / 64) by (apply Z.div_le_mono; lia).
  destruct (Z.eq_dec (q / 64) ((cursor - 1) / 64)) as [Heq|Hne].
  - unfold write_prefix_at, write_word_address in Hprefix.
    rewrite Heq in HL. destruct (Hprefix w HL) as [w' [HL' Hout]].
    exists w'. rewrite Heq. split; [exact HL'|]. rewrite Hb. symmetry.
    apply Hout; [lia|]. right. unfold write_word_shift. lia.
  - exists w. split; [|exact Hb]. apply HP; [exact HL|]. lia.
Qed.

(** Re-establish the representation after a jet's writes.  [out] are the
    cells written from the initial cursor [length out + e]; the new active
    write frame has [rev out] prepended to its written data. *)
Lemma bm_rep_after_write m mf L s wd e (out : list Cell) :
  activeWriteFrame s = {| writeData := wd; writeEmpty := length out + e |} ->
  (1 <= length out)%nat ->
  bm_rep m L s -> bm_separated L s ->
  frame_output_cells_at mf (cells_blk L) (edge_ofs (active_write_loc L))
    (Z.of_nat (length out + e)) out ->
  write_prefix_at m mf (cells_blk L) (edge_ofs (active_write_loc L))
    (Z.of_nat (length out + e)) ->
  frame_fields_at mf (frames_blk L) (item_ofs (active_write_loc L)) (cells_blk L)
    (edge_ofs (active_write_loc L)) (Z.of_nat e) ->
  (forall chunk b ofs, Mem.valid_block m b ->
    (b <> frames_blk L \/ ofs + size_chunk chunk <= item_ofs (active_write_loc L) + 8 \/
      item_ofs (active_write_loc L) + 16 <= ofs) ->
    (b <> cells_blk L \/
      ofs + size_chunk chunk <= edge_ofs (active_write_loc L) + 8 * (Z.of_nat e / 64) \/
      write_word_address (edge_ofs (active_write_loc L)) (Z.of_nat (length out + e)) + 8 <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs) ->
  bm_rep mf L
    {| inactiveReadFrames := inactiveReadFrames s;
       activeReadFrame := activeReadFrame s;
       activeWriteFrame := {| writeData := rev out ++ wd; writeEmpty := e |};
       inactiveWriteFrames := inactiveWriteFrames s |}.
Proof.
  intros Hawf HN [Hblk [HIR [HAR [HAW HIW]]]] [HSI [HSR HSW]] Hout Hprefix Hfields Hpres.
  set (aw := active_write_loc L) in *.
  set (cursor := Z.of_nat (length out + e)) in *.
  set (lo := edge_ofs aw + 8 * (Z.of_nat e / 64)) in *.
  set (hi := write_word_address (edge_ofs aw) cursor + 8) in *.
  assert (HSI' : forall l, In l (active_read_loc L :: inactive_read_locs L ++ inactive_write_locs L) ->
    disjoint_ranges (item_ofs l) (item_ofs l + 16) (item_ofs aw + 8) (item_ofs aw + 16))
    by exact HSI.
  clear HSI.
  unfold write_frame_rep in HAW. rewrite Hawf in HAW.
  destruct HAW as [HB [HFd [HE0 [HA [HE [HM [HW Hcells]]]]]]].
  cbn [writeData writeEmpty] in HB, HFd, HE0, HA, HE, HM, HW, Hcells.
  set (n := write_size {| writeData := wd; writeEmpty := length out + e |}) in *.
  assert (Hn : n = Z.of_nat (length wd) + cursor) by (unfold n, cursor, write_size; cbn; lia).
  assert (Hn0 : 0 <= n) by lia.
  destruct (frame_words_bounds _ Hn0) as [Hfw0 Hfw].
  assert (Hcur : 1 <= cursor) by (unfold cursor; lia).
  assert (He64 : 0 <= Z.of_nat e / 64) by (apply Z.div_pos; lia).
  assert (Hlo : edge_ofs aw <= lo) by (unfold lo; lia).
  assert (Htop : (cursor - 1) / 64 < frame_words n) by (apply Z.div_lt_upper_bound; lia).
  assert (Hhi : hi <= edge_ofs aw + 8 * frame_words n) by (unfold hi, write_word_address; lia).
  assert (Hwhi : write_region_hi aw (activeWriteFrame s) = edge_ofs aw + 8 * frame_words n).
  { unfold write_region_hi. rewrite Hawf. reflexivity. }
  inversion HSR as [|l0 rf0 ls rfs HSA HSR' Hl Hr]. clear HSR.
  split; [exact Hblk|]. split; [|split; [|split]].
  - (* inactive read frames *)
    eapply Forall2_zip_in; [|exact HIR|exact HSR'].
    intros l rf Hin Hrep Hdisj.
    eapply (read_frame_preserved m mf (cells_blk L) (frames_blk L) (item_ofs aw) lo hi);
      eauto.
    + apply HSI'. right. apply in_or_app. left. exact Hin.
    + rewrite Hwhi in Hdisj. unfold disjoint_ranges in Hdisj. lia.
  - (* active read frame *)
    cbn [activeReadFrame].
    eapply (read_frame_preserved m mf (cells_blk L) (frames_blk L) (item_ofs aw) lo hi);
      eauto.
    + apply HSI'. left. reflexivity.
    + rewrite Hwhi in HSA. unfold disjoint_ranges in HSA. lia.
  - (* active write frame *)
    cbn [activeWriteFrame]. unfold write_frame_rep. cbn [writeData writeEmpty].
    assert (Hsize : write_size {| writeData := rev out ++ wd; writeEmpty := e |} = n).
    { unfold n, write_size. cbn. rewrite app_length, rev_length. lia. }
    rewrite Hsize.
    split; [exact HB|]. split; [exact Hfields|].
    split; [exact HE0|]. split; [exact HA|]. split; [exact HE|]. split; [exact HM|]. split.
    + intros i Hi.
      destruct (Z_lt_ge_dec (edge_ofs aw + 8 * i) lo) as [Hbelow|Habove1];
        [|destruct (Z_lt_ge_dec (edge_ofs aw + 8 * i) hi) as [Hin|Habove2]].
      * destruct (HW i Hi) as [w Hw]. exists w.
        eapply (cell_load_preserved m mf (cells_blk L) (frames_blk L) (item_ofs aw) lo hi);
          eauto.
        unfold lo in *. fold aw. left. lia.
      * set (q := Z.max (Z.of_nat e) (64 * i)).
        assert (Hdi := Z.div_mod (Z.of_nat e) 64 ltac:(lia)).
        assert (Hmi := Z.mod_pos_bound (Z.of_nat e) 64 ltac:(lia)).
        assert (Hdc := Z.div_mod (cursor - 1) 64 ltac:(lia)).
        assert (Hmc := Z.mod_pos_bound (cursor - 1) 64 ltac:(lia)).
        unfold lo, hi, write_word_address in *.
        assert (Hi1 : Z.of_nat e / 64 <= i) by lia.
        assert (Hi2 : i <= (cursor - 1) / 64) by lia.
        assert (Hq : Z.of_nat e <= q <= cursor - 1) by (unfold q; lia).
        assert (Hqi : q / 64 = i).
        { unfold q. destruct (Z.max_spec (Z.of_nat e) (64 * i)) as [[Hlt ->]|[Hge ->]].
          - rewrite Z.mul_comm, Z.div_mul by lia. reflexivity.
          - symmetry. apply Z.div_unique with (Z.of_nat e - 64 * i); lia. }
        set (j := Z.to_nat (cursor - 1 - q)).
        assert (Hj : (j < length out)%nat) by (unfold j, cursor in *; lia).
        destruct (nth_error out j) as [c|] eqn:Hc;
          [|apply nth_error_None in Hc; lia].
        specialize (Hout j c Hc).
        replace (cursor - 1 - Z.of_nat j) with q in Hout by (unfold j; lia).
        assert (Hex : exists b, frame_output_bit_at mf (cells_blk L) (edge_ofs aw) q b).
        { destruct c as [b|]; cbn in Hout; [exists b; exact Hout|exact Hout]. }
        destruct Hex as [b [_ [w [Hw _]]]]. exists w. rewrite Hqi in Hw. exact Hw.
      * destruct (HW i Hi) as [w Hw]. exists w.
        eapply (cell_load_preserved m mf (cells_blk L) (frames_blk L) (item_ofs aw) lo hi);
          eauto.
        fold aw. right. lia.
    + rewrite rev_app_distr, rev_involutive. apply frame_output_cells_at_app. split.
      * intros j c Hj. specialize (Hcells j c Hj).
        assert (Hlen : (j < length (rev wd))%nat).
        { apply nth_error_Some. rewrite Hj. discriminate. }
        rewrite rev_length in Hlen.
        eapply cell_matches_impl; [|exact Hcells]. intros b Hb.
        eapply output_bit_after_prefix; [| |exact Hprefix|exact Hb].
        -- lia.
        -- intros a v Hv Ha.
           eapply (cell_load_preserved m mf (cells_blk L) (frames_blk L) (item_ofs aw) lo hi);
             eauto.
      * rewrite rev_length. replace (n - Z.of_nat (length wd)) with cursor by lia.
        exact Hout.
  - (* inactive write frames *)
    cbn [inactiveWriteFrames].
    eapply Forall2_zip_in; [|exact HIW|exact HSW].
    intros l wf Hin Hrep Hdisj.
    eapply (write_frame_preserved m mf (cells_blk L) (frames_blk L) (item_ofs aw) lo hi);
      eauto.
    + apply HSI'. right. apply in_or_app. right. exact Hin.
    + rewrite Hwhi in Hdisj. unfold disjoint_ranges in Hdisj. lia.
Qed.
