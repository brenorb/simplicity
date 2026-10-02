(** Derive the actual write32s loop from an initial uint32 array and writable
    output frame.  Earlier words and unrelated output contents are preserved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_uint32_array_init C.jet_write32s_exec.
Require Import C.jet_frame_spec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_output_layout_step C.jet_output_sequence_step C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_write_wide_layout_total C.jet_encoding C.jet_bitmachine_rep.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition uint32_word_cells (xs : list int) :=
  concat (map (fun x => @encode (Word 5) (@fromZ (WordToZ 5) (Int.unsigned x))) xs).
Lemma uint32_word_cells_length xs : length (uint32_word_cells xs) = (32 * length xs)%nat.
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  change (length (@encode (Word 5) (@fromZ (WordToZ 5) (Int.unsigned x)) ++ uint32_word_cells xs) =
    (32 * length (x :: xs))%nat).
  rewrite app_length, (encode_word_length 5 (@fromZ (WordToZ 5) (Int.unsigned x))), IH.
  cbn [Nat.pow length]; lia.
Qed.
Lemma decode_uint32_as_long x :
  decode_wide W32 (Int64.zero_ext 32 (Int64.repr (Int.unsigned x))) =
    @fromZ (WordToZ 5) (Int.unsigned x).
Proof.
  pose proof (Int.unsigned_range x) as HX.
  assert (HR : 0 <= Int.unsigned x <= Int64.max_unsigned).
  { change (0 <= Int.unsigned x <= 18446744073709551615).
    change (0 <= Int.unsigned x < 4294967296) in HX. lia. }
  unfold decode_wide. rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  rewrite (Int64.unsigned_repr (Int.unsigned x)) by exact HR.
  change (@fromZ (WordToZ 5) (Int.unsigned x mod 4294967296) =
    @fromZ (WordToZ 5) (Int.unsigned x)).
  rewrite Z.mod_small by exact HX. reflexivity.
Qed.

Theorem write32s_run_layout m bi input bf base bw edge cursor xs :
  0 <= input -> input + 4 * Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  bi <> bf -> bi <> bw -> uint32_array_at m bi input xs ->
  write_frame_at m bf base bw edge cursor (32 * Z.of_nat (length xs)) ->
  exists mf,
    write32s_run bi input bf base xs m mf /\
    frame_output_cells_at mf bw edge cursor (uint32_word_cells xs) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 32 * Z.of_nat (length xs)) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 32 * Z.of_nat (length xs)) / 64))
        (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  revert m input cursor. induction xs as [|x xs IH]; intros m input cursor HB HM Hif Hiw HA HW.
  - exists m. split; [reflexivity|]. split.
    + intros i c Hi. destruct i; discriminate.
    + split.
      * intros old HL. exists old. split; [exact HL|].
        unfold word_outside_eq; intros; reflexivity.
      * split.
        -- change (frame_fields_at m bf base bw edge (cursor - 0)).
           rewrite Z.sub_0_r. exact (proj1 (proj2 HW)).
        -- split; [unfold loads_outside_ranges; intros; reflexivity|]. split; auto.
  - pose proof HW as [HFBase [HFields [HE [HC [HMax [Hfw [PW HWords]]]]]]].
    assert (HW32 : write_frame_at m bf base bw edge cursor 32).
    { eapply write_frame_at_shorter with (count := 32 * Z.of_nat (length (x :: xs)));
        [cbn [length]; lia|exact HW]. }
    destruct (eval_write_wide_layout W32 m bf base bw edge cursor (Int64.repr (Int.unsigned x)) HW32)
      as [mi [Hwrite [Hslice [Hprefix [Hfields [Hmem [Hperm Hvalid]]]]]]].
    assert (HFirst : frame_output_cells_at mi bw edge cursor
      (@encode (Word 5) (@fromZ (WordToZ 5) (Int.unsigned x)))).
    { apply (wide_output_at_encode W32); [change (32 <= cursor); cbn [length] in HC; lia|].
      exists (Int64.zero_ext 32 (Int64.repr (Int.unsigned x))). split;
        [exact Hslice|apply decode_uint32_as_long]. }
    assert (HWNext : write_frame_at mi bf base bw edge (cursor - 32) (32 * Z.of_nat (length xs))).
    { eapply write_frame_at_after_slice with (n := 32) (x := Int64.zero_ext 32 (Int64.repr (Int.unsigned x)));
        [lia|lia| |exact Hfields|exact Hslice|exact Hmem|exact Hperm].
      replace (32 + 32 * Z.of_nat (length xs)) with (32 * Z.of_nat (length (x :: xs)))
        by (cbn [length]; lia). exact HW. }
    assert (HAHead : Mem.load Mint32 m bi input = Some (Vint x)).
    { pose proof (HA 0%nat x eq_refl) as HH.
      replace (input + 4 * Z.of_nat 0) with input in HH by lia. exact HH. }
    assert (HANext : uint32_array_at mi bi (input + 4) xs).
    { intros j v Hj. rewrite Hmem by (left; assumption).
      pose proof (HA (S j) v Hj) as HH.
      replace (input + 4 + 4 * Z.of_nat j) with (input + 4 * Z.of_nat (S j)) by lia. exact HH. }
    destruct (IH mi (input + 4) (cursor - 32) ltac:(lia) ltac:(cbn [length] in HM; lia)
      Hif Hiw HANext HWNext)
      as [mf [Hrun [Htail [HPrefixTail [HFieldsTail [HMemTail [HPermTail HValidTail]]]]]]].
    assert (HfirstFinal : frame_output_cells_at mf bw edge cursor
      (@encode (Word 5) (@fromZ (WordToZ 5) (Int.unsigned x)))).
    { eapply frame_output_cells_prefix_preserved with (bf := bf) (base := base)
        (cursor := cursor - 32); [exact Hfw| |exact HPrefixTail|exact HMemTail|exact HFirst].
      rewrite (encode_word_length 5 (@fromZ (WordToZ 5) (Int.unsigned x))).
      change (0 <= cursor - 32 <= cursor - 32).
      cbn [length] in HC; lia. }
    assert (HLo : edge + 8 * ((cursor - 32 * Z.of_nat (length (x :: xs))) / 64) <=
      slice_write_low 32 edge cursor).
    { pose proof (slice_write_low_bound 32 edge cursor ltac:(lia) ltac:(cbn [length] in HC; lia)) as HL.
      pose proof (Z.div_le_mono (cursor - 32 * Z.of_nat (length (x :: xs))) (cursor - 32) 64
        ltac:(lia) ltac:(cbn [length]; lia)). lia. }
    assert (HPrev : write_word_address edge (cursor - 32) <= write_word_address edge cursor).
    { unfold write_word_address. pose proof (Z.div_le_mono (cursor - 32 - 1) (cursor - 1) 64
        ltac:(lia) ltac:(lia)); lia. }
    exists mf. split; [exists mi; auto|]. split.
    + change (frame_output_cells_at mf bw edge cursor
        (@encode (Word 5) (@fromZ (WordToZ 5) (Int.unsigned x)) ++ uint32_word_cells xs)).
      apply frame_output_cells_at_app. split; [exact HfirstFinal|].
      rewrite (encode_word_length 5 (@fromZ (WordToZ 5) (Int.unsigned x))).
      exact Htail.
    + split.
      * eapply write_prefix_at_chain; [exact Hfw| |exact Hprefix|exact HPrefixTail|exact HMemTail].
        cbn [length] in HC; lia.
      * split.
        -- replace (cursor - 32 * Z.of_nat (length (x :: xs))) with
             (cursor - 32 - 32 * Z.of_nat (length xs)) by (cbn [length]; lia). exact HFieldsTail.
        -- split.
           ++ intros chunk b ofs Hbf Hbw. rewrite HMemTail.
              ** apply Hmem; [exact Hbf|]. destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto.
                 change (ofs + size_chunk chunk <= slice_write_low 32 edge cursor). lia.
              ** exact Hbf.
              ** replace (cursor - 32 - 32 * Z.of_nat (length xs)) with
                   (cursor - 32 * Z.of_nat (length (x :: xs))) by (cbn [length]; lia).
                 destruct Hbw as [Hneq|[Hbefore|Hafter]];
                   [left|right; left|right; right]; auto; lia.
           ++ split.
              ** intros b ofs kind p HP. apply HPermTail, Hperm; exact HP.
              ** intros b HV. apply HValidTail, Hvalid; exact HV.
Qed.

Theorem eval_write32s_layout m bi input bf base bw edge cursor xs :
  0 <= input -> input + 4 * Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  bi <> bf -> bi <> bw -> uint32_array_at m bi input xs ->
  write_frame_at m bf base bw edge cursor (32 * Z.of_nat (length xs)) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_write32s)
      [Vptr bf (Ptrofs.repr base); Vptr bi (Ptrofs.repr input);
        Vlong (Int64.repr (Z.of_nat (length xs)))] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor (uint32_word_cells xs) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - 32 * Z.of_nat (length xs)) /\
    loads_outside_ranges m mf bf (base + 8) (base + 16)
      bw (edge + 8 * ((cursor - 32 * Z.of_nat (length xs)) / 64))
        (write_word_address edge cursor + 8) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HM Hif Hiw HA HW.
  destruct (write32s_run_layout m bi input bf base bw edge cursor xs HB HM Hif Hiw HA HW)
    as [mf [HR HO]]. exists mf. split; [|exact HO].
  eapply eval_write32s_from_run; [exact HB|exact HM| |exact HR].
  pose proof HW as [_ [_ [_ [HC [Hmax _]]]]]. lia.
Qed.
