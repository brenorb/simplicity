(** Initial-only contract for streaming/copy jets.
    The existing arithmetic contract deliberately permits input/output overlap;
    copyBits cannot generally do so. This alternative derives its separation
    premise from the SAME represented-caller invariants as jet_context, without
    restricting caller cursors or requiring distinct input/output cell blocks.
    This module is infrastructure, not additional public jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.BitMachine Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding C.jet_bitmachine_rep C.jet_context.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition jet_copy_buffers_separated (bd bi bw : block)
    (edge outedge cursor read_cursor input_count : Z) : Prop :=
  bd <> bi /\
  (bi <> bw \/ disjoint_ranges outedge (outedge + 8 * frame_words cursor)
    (edge - 8 * frame_words (read_cursor + input_count)) edge).

Definition jet_separated_local_spec (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    jet_copy_buffers_separated bd bi bw edge outedge cursor read_cursor (Z.of_nat (bitSize A)) ->
    exists mf,
      Clight2.eval_funcall ge0 m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
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

Lemma jet_local_spec_to_separated f A B spec :
  jet_local_spec f A B spec -> jet_separated_local_spec f A B spec.
Proof.
  intros Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HB HA HF H0 HM HI HW Hsep.
  exact (Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a HB HA HF H0 HM HI HW).
Qed.

Lemma copy_frame_words_mono n k : n <= k -> frame_words n <= frame_words k.
Proof. intros H; unfold frame_words; apply Z.div_le_mono; lia. Qed.
Lemma copy_frame_words_mul k : frame_words (64 * k) = k.
Proof. unfold frame_words; symmetry; apply Z.div_unique with (r := 63); lia. Qed.
Lemma copy_read_prefix_words n q :
  0 <= n -> 0 <= q <= n -> frame_words (read_padding n + q) <= frame_words n.
Proof.
  intros Hn Hq. rewrite <- (copy_frame_words_mul (frame_words n)) at 1.
  apply copy_frame_words_mono. unfold read_padding. lia.
Qed.

Lemma copy_buffers_separated_of_rep m L s count :
  bm_rep m L s -> bm_separated L s ->
  0 <= count <= Z.of_nat (length (nextData (activeReadFrame s))) ->
  jet_copy_buffers_separated (frames_blk L) (cells_blk L) (cells_blk L)
    (edge_ofs (active_read_loc L)) (edge_ofs (active_write_loc L))
    (Z.of_nat (writeEmpty (activeWriteFrame s)))
    (read_padding (read_size (activeReadFrame s)) +
      Z.of_nat (length (prevData (activeReadFrame s)))) count.
Proof.
  intros [Hblk [HIR [HAR [HAW HIW]]]] [Hitems [Hsep Hwrites]] Hcount.
  unfold jet_copy_buffers_separated. split; [congruence|]. right.
  inversion Hsep as [|l rf ls rfs Hhead Htail]; subst.
  pose proof (copy_read_prefix_words (read_size (activeReadFrame s))
    (Z.of_nat (length (prevData (activeReadFrame s))) + count)) as Hread.
  assert (Hread0 : 0 <= read_size (activeReadFrame s)).
  { unfold read_size. lia. }
  assert (Hreadq : 0 <= Z.of_nat (length (prevData (activeReadFrame s))) + count <=
    read_size (activeReadFrame s)).
  { unfold read_size. rewrite Nat2Z.inj_add. lia. }
  specialize (Hread Hread0 Hreadq).
  assert (Hwrite : frame_words (Z.of_nat (writeEmpty (activeWriteFrame s))) <=
    frame_words (write_size (activeWriteFrame s))).
  { apply copy_frame_words_mono. unfold write_size. rewrite Nat2Z.inj_add. lia. }
  unfold disjoint_ranges, read_region_lo, write_region_hi in *.
  replace (read_padding (read_size (activeReadFrame s)) +
    Z.of_nat (length (prevData (activeReadFrame s))) + count) with
    (read_padding (read_size (activeReadFrame s)) +
    (Z.of_nat (length (prevData (activeReadFrame s))) + count)) by lia.
  lia.
Qed.

Theorem jet_context_separated {A B : Ty} (f : function)
    (t : forall {alg : Alg.Core.Algebra}, Alg.Core.domain alg A B) :
  Alg.Core.Parametric (@t) ->
  jet_separated_local_spec f A B (fun a => @t Alg.CoreFunSem a) ->
  (1 <= bitSize B)%nat ->
  forall env m L (ctx : Context) (a : A),
  let s0 := fillContext ctx
    {| readLocalState := encode a; writeLocalState := newWriteFrame (bitSize B) |} in
  let s1 := fillContext ctx
    {| readLocalState := encode a;
       writeLocalState := fullWriteFrame (encode (@t Alg.CoreFunSem a)) |} in
  bm_rep m L s0 -> bm_separated L s0 -> active_write_writable m L s0 ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f) (jet_args env L) E0 mf (Vint Int.one) /\
    bm_rep mf L s1 /\
    (s0 >>- @t Naive.translate ->> s1).
Proof.
  intros Ht Hspec HB env m L ctx a s0 s1 Hrep Hsep [HV HR].
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
  assert (Hcopysep : jet_copy_buffers_separated (frames_blk L) (cells_blk L) (cells_blk L)
    (edge_ofs ar) (edge_ofs aw) (Z.of_nat (length out + e))
    (pad + Z.of_nat (length prev)) (Z.of_nat (bitSize A))).
  { pose proof (copy_buffers_separated_of_rep m L s0 (Z.of_nat (bitSize A)) Hrep0 Hsep) as HC.
    rewrite Harf, Hawf in HC. cbn [prevData nextData writeEmpty] in HC.
    apply HC. rewrite app_length, encode_length. lia. }
  destruct (Hspec env m (frames_blk L) (item_ofs aw) (frames_blk L) (item_ofs ar)
    (cells_blk L) (cells_blk L) (edge_ofs ar) (edge_ofs aw)
    (Z.of_nat (length out + e)) (pad + Z.of_nat (length prev)) a HsB HsA HsF)
    as (mf & Hcall & Hout & Hprefix & Hfields & Hpres).
  - lia.
  - rewrite Hsize in HsM. lia.
  - exact HsC.
  - apply HWF; [lia|exact Hblk| |exact HV|].
    + rewrite <- Hawf. exact HAW.
    + rewrite <- Hawf. exact HR.
  - exact Hcopysep.
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

