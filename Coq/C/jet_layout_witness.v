(** Evaluator-shaped layouts satisfy the premises of [jet_context].

    [store_words] builds a memory from a list of aligned, pairwise separated
    64-bit stores.  [increment64_layout_witness] uses it to lay out, in two
    allocations as in [C/eval.c], a state with an inactive read frame holding a
    caller word [z], the [increment_64] input [a] in the active read frame, a
    65-cell output frame followed by an inactive write frame holding [w].  For
    every [a], [z] and [w] the resulting memory satisfies [bm_rep],
    [bm_separated] and the write permissions, so [increment64_context] applies
    and the caller frames [z] and [w] are still represented afterwards. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Import Simplicity.Ty Simplicity.Bit Simplicity.Word Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_increment64_wide_word.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_context C.jet_canonical.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.

Definition word_sep (x y : block * Z * val) : Prop :=
  match x, y with
  | (b1, o1, _), (b2, o2, _) => b1 <> b2 \/ o1 + 8 <= o2 \/ o2 + 8 <= o1
  end.

Lemma store_words m (ws : list (block * Z * val)) :
  ForallOrdPairs word_sep ws ->
  (forall b o v, In (b, o, v) ws -> Mem.valid_access m Mint64 b o Writable) ->
  exists m',
    (forall b o v, In (b, o, v) ws -> Mem.load Mint64 m' b o = Some (Val.load_result Mint64 v)) /\
    (forall b ofs k p, Mem.perm m' b ofs k p <-> Mem.perm m b ofs k p) /\
    Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction ws as [|[[b o] v] rest IH]; intros Hsep Hva.
  - exists m. repeat split; [intros b o v [] |tauto..].
  - inversion Hsep as [|x l Hsep_rest Hsep_tail]; subst.
    destruct (IH Hsep_tail (fun b' o' v' Hin => Hva b' o' v' (or_intror Hin)))
      as (m1 & Hl1 & Hp1 & Hn1).
    assert (Hva1 : Mem.valid_access m1 Mint64 b o Writable).
    { pose proof (Hva b o v (or_introl eq_refl)) as [Hr Ha]. split; [|exact Ha].
      intros ofs Hofs. apply Hp1. apply Hr. exact Hofs. }
    destruct (Mem.valid_access_store m1 Mint64 b o v Hva1) as [m2 Hst].
    exists m2. split; [|split].
    + intros b' o' v' [Heq|Hin].
      * inversion Heq; subst. eapply Mem.load_store_same in Hst. cbn in Hst. exact Hst.
      * rewrite (Mem.load_store_other _ _ _ _ _ _ Hst).
        -- apply Hl1. exact Hin.
        -- rewrite Forall_forall in Hsep_rest. specialize (Hsep_rest _ Hin).
           cbn in Hsep_rest. change (size_chunk Mint64) with 8.
           destruct Hsep_rest as [H|[H|H]]; [left; congruence|right; right; lia|right; left; lia].
    + intros b' ofs k p. split; intros H.
      * apply Hp1. eapply Mem.perm_store_2; eauto.
      * eapply Mem.perm_store_1; eauto. apply Hp1. exact H.
    + rewrite (Mem.nextblock_store _ _ _ _ _ _ Hst). exact Hn1.
Qed.

(** * Frames holding one 64-bit word *)

Definition wv (x : Ty.tySem (Word 6)) : val := Vlong (Int64.repr (@toZ (WordToZ 6) x)).

Lemma wv_testbit x j : 0 <= j < 64 ->
  Int64.testbit (Int64.repr (@toZ (WordToZ 6) x)) j = Z.testbit (@toZ (WordToZ 6) x) j.
Proof. intros Hj. apply Int64.testbit_repr. change Int64.zwordsize with 64. lia. Qed.

Lemma encode_len64 (x : Ty.tySem (Word 6)) : length (encode x) = 64%nat.
Proof. rewrite encode_word_length. reflexivity. Qed.

Lemma read_frame_rep_word m L l rf (x : Ty.tySem (Word 6)) :
  prevData rf = [] -> nextData rf = encode x ->
  frame_base_valid (item_ofs l) -> (8 | item_ofs l) ->
  8 <= edge_ofs l <= Ptrofs.max_unsigned ->
  frame_fields_at m (frames_blk L) (item_ofs l) (cells_blk L) (edge_ofs l) 0 ->
  Mem.load Mint64 m (cells_blk L) (edge_ofs l - 8) = Some (wv x) ->
  read_frame_rep m L l rf.
Proof.
  intros Hp Hn HB HA HE HF HL. unfold read_frame_rep.
  assert (Hsz : read_size rf = 64) by (unfold read_size; rewrite Hp, Hn, encode_len64; reflexivity).
  rewrite Hsz. rewrite Hp, Hn. cbn [rev app length].
  assert (Hw : frame_words 64 = 1) by reflexivity.
  assert (Hpd : read_padding 64 = 0) by reflexivity.
  rewrite Hw, Hpd. split; [exact HB|]. split; [exact HA|].
  split; [exact HF|]. split; [lia|]. split; [change (0 + 64 <= Int64.max_unsigned); vm_compute; discriminate|].
  split.
  - intros i Hi. exists (Int64.repr (@toZ (WordToZ 6) x)). replace i with 0 by lia.
    replace (edge_ofs l - 8 * (1 + 0)) with (edge_ofs l - 8) by lia. exact HL.
  - apply (frame_input_word_at_encode (n := 6%nat)).
    rewrite frame_input_word_at_iff. intros i Hi.
    change (Z.of_nat (Nat.pow 2 6)) with 64 in *.
    unfold frame_input_bit_at. rewrite Z.add_0_l.
    assert (Hq : i / 64 = 0 /\ i mod 64 = i) by (split; [apply Z.div_small|apply Z.mod_small]; lia).
    destruct Hq as [Hq1 Hq2]. rewrite Hq1, Hq2.
    split; [change Int64.max_unsigned with 18446744073709551615; lia|].
    split; [lia|]. exists (Int64.repr (@toZ (WordToZ 6) x)).
    replace (edge_ofs l - 8 * (1 + 0)) with (edge_ofs l - 8) by lia. split; [exact HL|].
    pose proof (wv_testbit x (63 - i) ltac:(lia)) as Hb. unfold Int64.testbit in Hb.
    rewrite Hb. f_equal.
Qed.

Lemma write_frame_rep_word m L l wf (x : Ty.tySem (Word 6)) :
  writeData wf = rev (encode x) -> writeEmpty wf = 0%nat ->
  frame_base_valid (item_ofs l) -> 0 <= edge_ofs l -> (8 | edge_ofs l) ->
  edge_ofs l + 8 <= Ptrofs.max_unsigned ->
  frame_fields_at m (frames_blk L) (item_ofs l) (cells_blk L) (edge_ofs l) 0 ->
  Mem.load Mint64 m (cells_blk L) (edge_ofs l) = Some (wv x) ->
  write_frame_rep m L l wf.
Proof.
  intros Hd He HB H0 HA HE HF HL. unfold write_frame_rep.
  assert (Hsz : write_size wf = 64) by (unfold write_size; rewrite Hd, He, rev_length, encode_len64; reflexivity).
  rewrite Hsz. rewrite He.
  assert (Hw : frame_words 64 = 1) by reflexivity. rewrite Hw.
  split; [exact HB|]. split; [exact HF|]. split; [exact H0|]. split; [exact HA|].
  split; [lia|]. split; [change (64 <= Int64.max_unsigned); vm_compute; discriminate|]. split.
  - intros i Hi. exists (Int64.repr (@toZ (WordToZ 6) x)). replace i with 0 by lia.
    replace (edge_ofs l + 8 * 0) with (edge_ofs l) by lia. exact HL.
  - rewrite Hd, rev_involutive.
    apply (frame_output_word_iff (n := 6%nat)). intros j Hj.
    change (Z.of_nat (Nat.pow 2 6)) with 64 in *.
    unfold frame_output_bit_at. replace (64 - 64 + j) with j by lia.
    assert (Hq : j / 64 = 0 /\ j mod 64 = j) by (split; [apply Z.div_small|apply Z.mod_small]; lia).
    destruct Hq as [Hq1 Hq2]. rewrite Hq1, Hq2.
    split; [lia|]. exists (Int64.repr (@toZ (WordToZ 6) x)).
    replace (edge_ofs l + 8 * 0) with (edge_ofs l) by lia. split; [exact HL|].
    pose proof (wv_testbit x j ltac:(lia)) as Hb. rewrite Hb. reflexivity.
Qed.

Lemma write_frame_rep_empty m L l wf :
  writeData wf = [] -> writeEmpty wf = 65%nat ->
  frame_base_valid (item_ofs l) -> 0 <= edge_ofs l -> (8 | edge_ofs l) ->
  edge_ofs l + 16 <= Ptrofs.max_unsigned ->
  frame_fields_at m (frames_blk L) (item_ofs l) (cells_blk L) (edge_ofs l) 65 ->
  (forall i, 0 <= i < 2 -> exists w, Mem.load Mint64 m (cells_blk L) (edge_ofs l + 8 * i) = Some (Vlong w)) ->
  write_frame_rep m L l wf.
Proof.
  intros Hd He HB H0 HA HE HF HW. unfold write_frame_rep.
  assert (Hsz : write_size wf = 65) by (unfold write_size; rewrite Hd, He; reflexivity).
  rewrite Hsz. rewrite He.
  assert (Hw : frame_words 65 = 2) by reflexivity. rewrite Hw.
  split; [exact HB|]. split; [exact HF|]. split; [exact H0|]. split; [exact HA|].
  split; [lia|]. split; [change (65 <= Int64.max_unsigned); vm_compute; discriminate|]. split.
  - exact HW.
  - rewrite Hd. intros i c Hi. destruct i; discriminate.
Qed.

(** * The witness layout *)

Definition witness_ctx (z w : Ty.tySem (Word 6)) : Context :=
  {| inactiveReadFrames := [{| prevData := []; nextData := encode z |}];
     activeReadFrame := {| prevData := []; nextData := [] |};
     activeWriteFrame := {| writeData := []; writeEmpty := 0 |};
     inactiveWriteFrames := [{| writeData := rev (encode w); writeEmpty := 0 |}] |}.

Definition witness_layout (c f : block) : bm_layout :=
  {| cells_blk := c; frames_blk := f;
     inactive_read_locs := [{| item_ofs := 0; edge_ofs := 8 |}];
     active_read_loc := {| item_ofs := 16; edge_ofs := 16 |};
     active_write_loc := {| item_ofs := 32; edge_ofs := 24 |};
     inactive_write_locs := [{| item_ofs := 48; edge_ofs := 40 |}] |}.

Definition witness_state (a z w : Ty.tySem (Word 6)) : RunState :=
  fillContext (witness_ctx z w)
    {| readLocalState := encode a;
       writeLocalState := newWriteFrame (bitSize (Ty.Prod Bit (Word 6))) |}.

Lemma witness_alloc c f m1 m2 :
  Mem.alloc Mem.empty 0 48 = (m1, c) -> Mem.alloc m1 0 64 = (m2, f) ->
  c <> f /\
  (forall o, 0 <= o -> o + 8 <= 48 -> (8 | o) -> Mem.valid_access m2 Mint64 c o Writable) /\
  (forall o, 0 <= o -> o + 8 <= 64 -> (8 | o) -> Mem.valid_access m2 Mint64 f o Writable) /\
  (forall o, 0 <= o < 48 -> Mem.perm m2 c o Cur Freeable).
Proof.
  intros Hc Hf.
  pose proof (Mem.alloc_result _ _ _ _ _ Hc) as Ec. pose proof (Mem.alloc_result _ _ _ _ _ Hf) as Ef.
  rewrite (Mem.nextblock_alloc _ _ _ _ _ Hc), Mem.nextblock_empty in Ef.
  rewrite Mem.nextblock_empty in Ec.
  split; [subst; discriminate|]. split; [|split].
  - intros o H0 H1 HA.
    eapply Mem.valid_access_implies; [|apply perm_F_any].
    eapply Mem.valid_access_alloc_other; [exact Hf|].
    eapply Mem.valid_access_alloc_same; [exact Hc|lia|exact H1|exact HA].
  - intros o H0 H1 HA.
    eapply Mem.valid_access_implies; [|apply perm_F_any].
    eapply Mem.valid_access_alloc_same; [exact Hf|lia|exact H1|exact HA].
  - intros o Ho. eapply Mem.perm_alloc_1; [exact Hf|].
    eapply Mem.perm_alloc_2; [exact Hc|lia].
Qed.

Lemma read_size_word rf (x : Ty.tySem (Word 6)) :
  prevData rf = [] -> nextData rf = encode x -> read_size rf = 64.
Proof. intros Hp Hn. unfold read_size. rewrite Hp, Hn, encode_len64. reflexivity. Qed.

Lemma write_size_word wf (x : Ty.tySem (Word 6)) :
  writeData wf = rev (encode x) -> writeEmpty wf = 0%nat -> write_size wf = 64.
Proof. intros Hd He. unfold write_size. rewrite Hd, He, rev_length, encode_len64. reflexivity. Qed.

Lemma write_size_empty wf :
  writeData wf = [] -> writeEmpty wf = 65%nat -> write_size wf = 65.
Proof. intros Hd He. unfold write_size. rewrite Hd, He. reflexivity. Qed.

Ltac lay := cbn [witness_layout active_read_loc active_write_loc inactive_read_locs
  inactive_write_locs cells_blk frames_blk item_ofs edge_ofs].

Ltac lay_in H := cbn [witness_layout active_read_loc active_write_loc inactive_read_locs
  inactive_write_locs cells_blk frames_blk item_ofs edge_ofs] in H.

Ltac va_side := first [lia | (apply Z.mod_divide; [lia|reflexivity])].

Lemma witness_separated c f a z w :
  bm_separated (witness_layout c f) (witness_state a z w).
Proof.
  set (s := witness_state a z w).
  assert (Ra : read_size (activeReadFrame s) = 64)
    by (apply read_size_word with (x := a); [reflexivity|apply app_nil_r]).
  assert (Rz : read_size {| prevData := []; nextData := encode z |} = 64)
    by (apply read_size_word with (x := z); reflexivity).
  assert (Wa : write_size (activeWriteFrame s) = 65)
    by (apply write_size_empty; reflexivity).
  assert (Ww : write_size {| writeData := rev (encode w); writeEmpty := 0 |} = 64)
    by (apply write_size_word with (x := w); reflexivity).
  assert (Ei : inactiveReadFrames s = [{| prevData := []; nextData := encode z |}]) by reflexivity.
  assert (Ew : inactiveWriteFrames s = [{| writeData := rev (encode w); writeEmpty := 0 |}])
    by reflexivity.
  assert (FW1 : frame_words 64 = 1) by reflexivity.
  assert (FW2 : frame_words 65 = 2) by reflexivity.
  unfold bm_separated. cbv zeta. split; [|split].
  - intros l Hl. cbn [witness_layout active_read_loc inactive_read_locs inactive_write_locs In app] in Hl.
    destruct Hl as [<-|[<-|[<-|[]]]]; unfold disjoint_ranges; lay; lia.
  - rewrite Ei. cbn [witness_layout active_read_loc inactive_read_locs].
    apply Forall2_cons; [|apply Forall2_cons; [|apply Forall2_nil]];
      unfold disjoint_ranges, read_region_lo, write_region_hi; rewrite ?Ra, ?Rz, ?Wa, ?FW1, ?FW2; lay; lia.
  - rewrite Ew. cbn [witness_layout inactive_write_locs].
    apply Forall2_cons; [|apply Forall2_nil];
      unfold disjoint_ranges, write_region_hi; rewrite ?Wa, ?Ww, ?FW1, ?FW2; lay; lia.
Qed.

(** The same concrete witness has ordered evaluator gap-buffer ranges. *)
Lemma witness_gap_buffer_layout c f (a z w : Ty.tySem (Word 6)) :
  gap_buffer_layout (witness_layout c f) (witness_state a z w).
Proof.
  unfold gap_buffer_layout, item_ranges, read_ranges, write_ranges,
    read_region_lo, write_region_hi, read_size, write_size,
    witness_state, witness_layout, witness_ctx, fillContext,
    newWriteFrame, read_padding, frame_words.
  cbn [map combine rev app activeReadFrame activeWriteFrame
    inactiveReadFrames inactiveWriteFrames active_read_loc active_write_loc
    inactive_read_locs inactive_write_locs item_ofs edge_ofs
    prevData nextData writeData writeEmpty readLocalState writeLocalState fst snd
    length bitSize].
  rewrite ?app_length, ?rev_length, !encode_len64.
  change (bitSize Word64) with 64%nat.
  cbn [increasing_ranges fst snd]. vm_compute. intuition discriminate.
Qed.

Theorem increment64_layout_witness (a z w : Ty.tySem (Word 6)) :
  exists m L,
    bm_rep m L (witness_state a z w) /\
    bm_separated L (witness_state a z w) /\
    active_write_writable m L (witness_state a z w) /\
    gap_buffer_layout L (witness_state a z w).
Proof.
  destruct (Mem.alloc Mem.empty 0 48) as [m1 c] eqn:Hc.
  destruct (Mem.alloc m1 0 64) as [m2 f] eqn:Hf.
  destruct (witness_alloc c f m1 m2 Hc Hf) as (Hcf & Hvc & Hvf & Hperm).
  set (ws := [(c, 0, wv z); (c, 8, wv a); (c, 24, Vlong (Int64.repr 0));
    (c, 32, Vlong (Int64.repr 0)); (c, 40, wv w);
    (f, 0, Vptr c (Ptrofs.repr 8)); (f, 8, Vlong (Int64.repr 0));
    (f, 16, Vptr c (Ptrofs.repr 16)); (f, 24, Vlong (Int64.repr 0));
    (f, 32, Vptr c (Ptrofs.repr 24)); (f, 40, Vlong (Int64.repr 65));
    (f, 48, Vptr c (Ptrofs.repr 40)); (f, 56, Vlong (Int64.repr 0))]).
  assert (Hsep : ForallOrdPairs word_sep ws).
  { unfold ws.
    repeat (apply FOP_cons;
      [apply Forall_forall; intros y Hy; simpl in Hy;
       repeat (destruct Hy as [<-|Hy]); try contradiction; unfold word_sep;
       first [(left; congruence) | (right; left; lia) | (right; right; lia)]|]);
    apply FOP_nil. }
  assert (Hva : forall b o v, In (b, o, v) ws -> Mem.valid_access m2 Mint64 b o Writable).
  { intros b o v Hin. unfold ws in Hin. simpl in Hin.
    repeat (destruct Hin as [E|Hin];
      [inversion E; subst; clear E; first [apply Hvc | apply Hvf]; va_side|]);
    try contradiction. }
  destruct (store_words m2 ws Hsep Hva) as (m & Hl & Hp & _).
  exists m, (witness_layout c f).
  assert (Hmax : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  assert (Hin' : forall b o v, In (b, o, v) ws -> Mem.load Mint64 m b o = Some (Val.load_result Mint64 v)) by exact Hl.
  (* loads of the stored words *)
  assert (Lz : Mem.load Mint64 m c 0 = Some (wv z)) by exact (Hin' c 0 (wv z) ltac:(unfold ws; simpl; tauto)).
  assert (La : Mem.load Mint64 m c 8 = Some (wv a)) by exact (Hin' c 8 (wv a) ltac:(unfold ws; simpl; tauto)).
  assert (Lw24 : Mem.load Mint64 m c 24 = Some (Vlong (Int64.repr 0))) by exact (Hin' c 24 _ ltac:(unfold ws; simpl; tauto)).
  assert (Lw32 : Mem.load Mint64 m c 32 = Some (Vlong (Int64.repr 0))) by exact (Hin' c 32 _ ltac:(unfold ws; simpl; tauto)).
  assert (Lw : Mem.load Mint64 m c 40 = Some (wv w)) by exact (Hin' c 40 (wv w) ltac:(unfold ws; simpl; tauto)).
  assert (F0 : frame_fields_at m f 0 c 8 0).
  { split; [change Mptr with Mint64; exact (Hin' f 0 _ ltac:(unfold ws; simpl; tauto))
           |exact (Hin' f 8 _ ltac:(unfold ws; simpl; tauto))]. }
  assert (F16 : frame_fields_at m f 16 c 16 0).
  { split; [change Mptr with Mint64; exact (Hin' f 16 _ ltac:(unfold ws; simpl; tauto))
           |exact (Hin' f 24 _ ltac:(unfold ws; simpl; tauto))]. }
  assert (F32 : frame_fields_at m f 32 c 24 65).
  { split; [change Mptr with Mint64; exact (Hin' f 32 _ ltac:(unfold ws; simpl; tauto))
           |exact (Hin' f 40 _ ltac:(unfold ws; simpl; tauto))]. }
  assert (F48 : frame_fields_at m f 48 c 40 0).
  { split; [change Mptr with Mint64; exact (Hin' f 48 _ ltac:(unfold ws; simpl; tauto))
           |exact (Hin' f 56 _ ltac:(unfold ws; simpl; tauto))]. }
  assert (Hbase : forall o, 0 <= o -> o + 16 <= 64 -> frame_base_valid o)
    by (intros o H0 H1; unfold frame_base_valid; split; lia).
  refine (conj (conj Hcf (conj _ (conj _ (conj _ _)))) (conj _ _)).
  - apply Forall2_cons; [|apply Forall2_nil].
    eapply (read_frame_rep_word m (witness_layout c f) _ _ z);
      [ reflexivity | reflexivity
      | apply Hbase; lay; lia
      | lay; exists 0; reflexivity
      | lay; rewrite Hmax; lia
      | exact F0 | exact Lz ].
  - eapply (read_frame_rep_word m (witness_layout c f) _ _ a);
      [ reflexivity | apply app_nil_r
      | apply Hbase; lay; lia
      | lay; exists 2; reflexivity
      | lay; rewrite Hmax; lia
      | exact F16 | exact La ].
  - eapply (write_frame_rep_empty m (witness_layout c f));
      [ reflexivity | reflexivity
      | apply Hbase; lay; lia
      | lay; lia
      | lay; exists 3; reflexivity
      | lay; rewrite Hmax; lia
      | exact F32
      | intros i Hi; lay; assert (i = 0 \/ i = 1) as [-> | ->] by lia;
        eexists; [exact Lw24|exact Lw32] ].
  - apply Forall2_cons; [|apply Forall2_nil].
    eapply (write_frame_rep_word m (witness_layout c f) _ _ w);
      [ reflexivity | reflexivity
      | apply Hbase; lay; lia
      | lay; lia
      | lay; exists 5; reflexivity
      | lay; rewrite Hmax; lia
      | exact F48 | exact Lw ].
  - exact (witness_separated c f a z w).
  - split; [|apply witness_gap_buffer_layout].
    assert (Wa : write_size (activeWriteFrame (witness_state a z w)) = 65)
      by (apply write_size_empty; reflexivity).
    assert (FW2 : frame_words 65 = 2) by reflexivity.
    assert (VA : forall b o, Mem.valid_access m2 Mint64 b o Writable ->
      Mem.valid_access m Mint64 b o Writable).
    { intros b o [Hr Ha]. split; [|exact Ha]. intros ofs Hofs. apply Hp. apply Hr. exact Hofs. }
    unfold active_write_writable. cbv zeta. split.
    + lay. apply VA. apply Hvf; [lia|lia|exists 5; reflexivity].
    + intros ofs Hofs. unfold write_region_hi in Hofs. rewrite Wa, FW2 in Hofs. lay_in Hofs.
      apply Hp. eapply Mem.perm_implies; [apply Hperm; lay; lia|apply perm_F_any].
Qed.

(** For every input [a] and every caller word [z] and saved output [w], the
    generated [increment_64] call in the witness layout terminates and leaves
    a memory representing the state reached by the Bit Machine translation.
    That state still contains the caller's read frame [encode z] and the
    inactive write frame [encode w]. *)
Corollary increment64_layout_witness_context (env : val) (a z w : Ty.tySem (Word 6)) :
  exists m L mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_increment_64) (jet_args env L)
      E0 mf (Vint Int.one) /\
    bm_rep mf L
      (fillContext (witness_ctx z w)
        {| readLocalState := encode a;
           writeLocalState :=
             fullWriteFrame (encode (@increment64_spec Alg.CoreFunSem a)) |}) /\
    witness_state a z w >>- @increment64_spec Naive.translate ->>
      fillContext (witness_ctx z w)
        {| readLocalState := encode a;
           writeLocalState :=
             fullWriteFrame (encode (@increment64_spec Alg.CoreFunSem a)) |} /\
    inactiveReadFrames (witness_ctx z w) =
      [{| prevData := []; nextData := encode z |}] /\
    inactiveWriteFrames (witness_ctx z w) =
      [{| writeData := rev (encode w); writeEmpty := 0 |}].
Proof.
  destruct (increment64_layout_witness a z w) as (m & L & Hrep & Hsep & Hwr & Hgap).
  destruct (increment64_context env m L (witness_ctx z w) a Hrep Hsep Hwr)
    as (mf & Hcall & Hrep' & Htr).
  exists m, L, mf.
  exact (conj Hcall (conj Hrep' (conj Htr (conj eq_refl eq_refl)))).
Qed.
