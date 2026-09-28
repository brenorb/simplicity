(** Local jet replacement in a represented Bit Machine context.

    [jet_context] combines a jet's canonical-encoding contract
    ([jet_local_spec]) with [Translate.Naive.translate_correct].  From a
    memory representing [fillContext ctx {encode a; newWriteFrame |B|}], the
    generated C jet terminates in a memory representing
    [fillContext ctx {encode a; fullWriteFrame (encode (t a))}], which is also
    the state reached by the Bit Machine translation of [t].

    [gap_buffer_separated] shows that the noninterference premise holds for
    the evaluator's gap-buffer layouts: frame items in increasing slots of the
    [frames] block and cell regions in increasing address order of the
    [cells] block, read frames first and write frames after the gap. *)
From Coq Require Import ZArith List Lia Sorting.Sorted.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep.
Import ListNotations.
Local Open Scope Z_scope.

Lemma write_frame_at_of_rep m L l wf N :
  (N <= writeEmpty wf)%nat ->
  cells_blk L <> frames_blk L ->
  write_frame_rep m L l wf ->
  Mem.valid_access m Mint64 (frames_blk L) (item_ofs l + 8) Writable ->
  Mem.range_perm m (cells_blk L) (edge_ofs l) (write_region_hi l wf) Cur Writable ->
  write_frame_at m (frames_blk L) (item_ofs l) (cells_blk L) (edge_ofs l)
    (Z.of_nat (writeEmpty wf)) (Z.of_nat N).
Proof.
  intros HN Hblk Hrep HV HR. unfold write_frame_rep in Hrep.
  destruct Hrep as [HB [HF [HE0 [HA [HE [HM [HW _]]]]]]].
  unfold write_region_hi in HR.
  assert (Hn0 : 0 <= write_size wf) by (unfold write_size; lia).
  destruct (frame_words_bounds _ Hn0) as [Hfw0 Hfw].
  unfold write_frame_at. split; [exact HB|]. split; [exact HF|]. split; [exact HE0|].
  split; [lia|]. split; [unfold write_size in HM; lia|]. split; [auto|]. split; [exact HV|].
  intros i Hi. cbv zeta. unfold write_cell_address.
  set (k := (Z.of_nat (writeEmpty wf) - 1 - i) / 64).
  assert (Hk : 0 <= k < frame_words (write_size wf)).
  { unfold k, write_size in *. split; [apply Z.div_pos; lia|].
    apply Z.div_lt_upper_bound; lia. }
  split; [lia|]. split; [lia|]. split.
  - split.
    + intros ofs Hofs. apply HR. change (size_chunk Mint64) with 8 in Hofs. lia.
    + change (align_chunk Mint64) with 8. apply Z.divide_add_r; [exact HA|].
      exists k. lia.
  - apply HW. exact Hk.
Qed.

(** * Local replacement *)

Theorem jet_context {A B : Ty} (f : function)
    (t : forall {alg : Alg.Core.Algebra}, Alg.Core.domain alg A B) :
  Alg.Core.Parametric (@t) ->
  jet_local_spec f A B (fun a => @t Alg.CoreFunSem a) ->
  (1 <= bitSize B)%nat ->
  forall m L (ctx : Context) (a : A),
  let s0 := fillContext ctx
    {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |} in
  let s1 := fillContext ctx
    {| readLocalState := encode a;
       writeLocalState := fullWriteFrame (encode (@t Alg.CoreFunSem a)) |} in
  bm_rep m L s0 -> bm_separated L s0 -> active_write_writable m L s0 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f) (jet_args L) E0 mf (Vint Int.one) /\
    bm_rep mf L s1 /\
    (s0 >>- @t Naive.translate ->> s1).
Proof.
  intros Ht Hspec HB m L ctx a s0 s1 Hrep Hsep [HV HR].
  pose proof Hrep as Hrep0.
  destruct Hrep as [Hblk [HIR [HAR [HAW HIW]]]].
  set (ar := active_read_loc L) in *. set (aw := active_write_loc L) in *.
  set (prev := prevData (activeReadFrame ctx)).
  set (next := nextData (activeReadFrame ctx)).
  set (wd := writeData (activeWriteFrame ctx)).
  set (e := writeEmpty (activeWriteFrame ctx)).
  set (out := encode (@t Alg.CoreFunSem a)).
  assert (Hlen : length out = bitSize B) by apply encode_length.
  assert (Harf : activeReadFrame s0 = {| prevData := prev; nextData := encode a ++ next |})
    by reflexivity.
  assert (Hawf : activeWriteFrame s0 = {| writeData := wd; writeEmpty := length out + e |}).
  { rewrite Hlen. reflexivity. }
  (* Input frame *)
  unfold read_frame_rep in HAR. rewrite Harf in HAR.
  destruct HAR as [HsB [HsA [HsF [HsE [HsM [_ HsC]]]]]].
  cbn [prevData nextData] in HsB, HsA, HsF, HsE, HsM, HsC.
  set (pad := read_padding (read_size {| prevData := prev; nextData := encode a ++ next |})) in *.
  assert (Hsize : read_size {| prevData := prev; nextData := encode a ++ next |} =
    Z.of_nat (length prev) + Z.of_nat (bitSize A) + Z.of_nat (length next)).
  { unfold read_size. cbn. rewrite app_length, encode_length. lia. }
  assert (Hpad : 0 <= pad).
  { unfold pad, read_padding. rewrite Hsize.
    pose proof (frame_words_bounds (Z.of_nat (length prev) + Z.of_nat (bitSize A) +
      Z.of_nat (length next)) ltac:(lia)). lia. }
  rewrite frame_input_cells_at_app in HsC. destruct HsC as [_ HsC].
  rewrite frame_input_cells_at_app in HsC. destruct HsC as [HsC _].
  rewrite rev_length in HsC.
  (* Output frame *)
  assert (HWF := write_frame_at_of_rep m L aw (activeWriteFrame s0) (bitSize B)).
  rewrite Hawf in HWF. cbn [writeEmpty] in HWF.
  destruct (Hspec m (frames_blk L) (item_ofs aw) (frames_blk L) (item_ofs ar)
    (cells_blk L) (cells_blk L) (edge_ofs ar) (edge_ofs aw)
    (Z.of_nat (length out + e)) (pad + Z.of_nat (length prev)) a HsB HsA HsF)
    as (mf & Hcall & Hout & Hprefix & Hfields & Hpres).
  - lia.
  - rewrite Hsize in HsM. lia.
  - exact HsC.
  - apply HWF; [lia|exact Hblk| |exact HV|].
    + rewrite <- Hawf. exact HAW.
    + rewrite <- Hawf. exact HR.
  - exists mf. split; [exact Hcall|]. split.
    + assert (Hcur : Z.of_nat (length out + e) - Z.of_nat (bitSize B) = Z.of_nat e) by lia.
      rewrite Hcur in Hfields, Hpres.
      change s1 with
        {| inactiveReadFrames := inactiveReadFrames s0;
           activeReadFrame := activeReadFrame s0;
           activeWriteFrame := {| writeData := rev out ++ wd; writeEmpty := e |};
           inactiveWriteFrames := inactiveWriteFrames s0 |}.
      eapply bm_rep_after_write; eauto; lia.
    + exact (Naive.translate_correct Ht a ctx).
Qed.

(** * Evaluator-shaped layouts *)

(** Ranges listed in increasing address order, each non-empty-or-empty and
    ending at or before the next one begins. *)
Fixpoint increasing_ranges (l : list (Z * Z)) : Prop :=
  match l with
  | [] => True
  | x :: l' =>
      fst x <= snd x /\
      match l' with [] => True | y :: _ => snd x <= fst y end /\
      increasing_ranges l'
  end.

Lemma increasing_ranges_head_bound bnd l :
  increasing_ranges l ->
  match l with [] => True | y :: _ => bnd <= fst y end ->
  Forall (fun z => bnd <= fst z) l.
Proof.
  induction l as [|y l IH]; intros H Hb; [constructor|].
  destruct H as [Hy [Hn Hl]]. constructor; [exact Hb|].
  apply IH; [exact Hl|]. destruct l as [|z l]; [exact I|]. lia.
Qed.

Lemma increasing_ranges_strong l :
  increasing_ranges l ->
  StronglySorted (fun x y => snd x <= fst y) l.
Proof.
  induction l as [|x l IH]; intros H; [constructor|].
  destruct H as [Hx [Hnext Hl]]. constructor; [apply IH; exact Hl|].
  apply increasing_ranges_head_bound; assumption.
Qed.

Lemma StronglySorted_app_rel {T} (R : T -> T -> Prop) xs ys x y :
  StronglySorted R (xs ++ ys) -> In x xs -> In y ys -> R x y.
Proof.
  induction xs as [|z xs IH]; intros H Hx Hy; [destruct Hx|].
  inversion H as [|z' l Hs Hall]; subst.
  destruct Hx as [<-|Hx].
  - rewrite Forall_forall in Hall. apply Hall. apply in_or_app. right. exact Hy.
  - apply IH; assumption.
Qed.

Lemma StronglySorted_app_r {T} (R : T -> T -> Prop) xs ys :
  StronglySorted R (xs ++ ys) -> StronglySorted R ys.
Proof.
  induction xs as [|x xs IH]; intros H; [exact H|].
  inversion H; subst. apply IH. assumption.
Qed.

Lemma StronglySorted_cons_rel {T} (R : T -> T -> Prop) x ys y :
  StronglySorted R (x :: ys) -> In y ys -> R x y.
Proof.
  intros H Hy. inversion H as [|z l Hs Hall]; subst.
  rewrite Forall_forall in Hall. auto.
Qed.

Definition read_ranges (ls : list frame_loc) (rfs : list ReadFrame) : list (Z * Z) :=
  map (fun p => (read_region_lo (fst p) (snd p), edge_ofs (fst p))) (combine ls rfs).
Definition write_ranges (ls : list frame_loc) (wfs : list WriteFrame) : list (Z * Z) :=
  map (fun p => (edge_ofs (fst p), write_region_hi (fst p) (snd p))) (combine ls wfs).
Definition item_ranges (ls : list frame_loc) : list (Z * Z) :=
  map (fun l => (item_ofs l, item_ofs l + 16)) ls.

(** The evaluator's gap buffers: read frames bottom to top, then the gap,
    then the active write frame and the inactive write frames.  Adjacent
    frames may touch; [initReadFrame] and [initWriteFrame] place each new
    frame at the previous frame's edge.  The lists of frames are the Bit
    Machine stacks, whose heads are the frames nearest the active ones. *)
Definition gap_buffer_layout (L : bm_layout) (s : RunState) : Prop :=
  increasing_ranges
    (rev (item_ranges (active_read_loc L :: inactive_read_locs L)) ++
     item_ranges (active_write_loc L :: inactive_write_locs L)) /\
  increasing_ranges
    (rev (read_ranges (active_read_loc L :: inactive_read_locs L)
                      (activeReadFrame s :: inactiveReadFrames s)) ++
     write_ranges (active_write_loc L :: inactive_write_locs L)
                  (activeWriteFrame s :: inactiveWriteFrames s)).

Lemma in_combine_Forall2 {A B} (P : A -> B -> Prop) xs ys :
  length xs = length ys ->
  (forall x y, In (x, y) (combine xs ys) -> P x y) -> Forall2 P xs ys.
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen H; try discriminate; constructor.
  - apply H. left. reflexivity.
  - apply IH; [cbn in Hlen; lia|]. intros a b Hab. apply H. right. exact Hab.
Qed.

Theorem gap_buffer_separated L s :
  length (inactive_read_locs L) = length (inactiveReadFrames s) ->
  length (inactive_write_locs L) = length (inactiveWriteFrames s) ->
  gap_buffer_layout L s -> bm_separated L s.
Proof.
  intros HlenR HlenW [Hitems Hcells].
  apply increasing_ranges_strong in Hitems. apply increasing_ranges_strong in Hcells.
  split; [|split].
  - intros l Hl.
    destruct Hl as [<-|Hl]; [|apply in_app_or in Hl; destruct Hl as [Hl|Hl]].
    + pose proof (StronglySorted_app_rel _ _ _ (item_ofs (active_read_loc L), item_ofs (active_read_loc L) + 16)
        (item_ofs (active_write_loc L), item_ofs (active_write_loc L) + 16) Hitems) as H.
      unfold disjoint_ranges. left.
      enough (item_ofs (active_read_loc L) + 16 <= item_ofs (active_write_loc L)) by lia.
      apply H; [rewrite <- in_rev|]; unfold item_ranges; simpl; auto.
    + pose proof (StronglySorted_app_rel _ _ _ (item_ofs l, item_ofs l + 16)
        (item_ofs (active_write_loc L), item_ofs (active_write_loc L) + 16) Hitems) as H.
      unfold disjoint_ranges. left.
      enough (item_ofs l + 16 <= item_ofs (active_write_loc L)) by lia.
      apply H; [|unfold item_ranges; simpl; auto].
      rewrite <- in_rev. unfold item_ranges. simpl. right. apply in_map_iff. exists l. auto.
    + apply StronglySorted_app_r in Hitems. rename Hitems into Hw.
      pose proof (StronglySorted_cons_rel _ (item_ofs (active_write_loc L), item_ofs (active_write_loc L) + 16) _
        (item_ofs l, item_ofs l + 16) Hw) as H.
      unfold disjoint_ranges. right.
      enough (item_ofs (active_write_loc L) + 16 <= item_ofs l) by lia. apply H.
      unfold item_ranges. apply in_map_iff. exists l. auto.
  - apply in_combine_Forall2; [cbn; lia|]. intros l rf Hin.
    pose proof (StronglySorted_app_rel _ _ _ (read_region_lo l rf, edge_ofs l)
      (edge_ofs (active_write_loc L), write_region_hi (active_write_loc L) (activeWriteFrame s)) Hcells) as H.
    unfold disjoint_ranges. right. apply H.
    + rewrite <- in_rev. unfold read_ranges. apply in_map_iff. exists (l, rf). auto.
    + unfold write_ranges; simpl; auto.
  - apply in_combine_Forall2; [exact HlenW|]. intros l wf Hin.
    apply StronglySorted_app_r in Hcells. rename Hcells into Hw.
    pose proof (StronglySorted_cons_rel _ (edge_ofs (active_write_loc L), write_region_hi (active_write_loc L) (activeWriteFrame s)) _
      (edge_ofs l, write_region_hi l wf) Hw) as H.
    unfold disjoint_ranges. left. apply H.
    unfold write_ranges. apply in_map_iff. exists (l, wf). auto.
Qed.
