(** Derive read8s reader calls and stores from initial frame and writable-array
    contracts. This helper is not itself an individual jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_read8s_exec.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_read8_input_word_total.
Require Import C.jet_word_repr.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition word8_array_value (x : Ty.tySem (Word 3)) := Int.repr (@toZ (WordToZ 3) x).
Definition uint8_array_at m b base (xs : list int) :=
  forall i x, nth_error xs i = Some x ->
    Mem.load Mint8unsigned m b (base + Z.of_nat i) = Some (Vint x).
Lemma word8_array_value_zero_ext x : Int.zero_ext 8 (word8_array_value x) = word8_array_value x.
Proof.
  pose proof (word_toZ_range 3 x) as HR.
  change (0 <= @toZ (WordToZ 3) x < 256) in HR.
  apply Int.same_bits_eq. intros i HI.
  rewrite Int.bits_zero_ext by lia. destruct (zlt i 8); [reflexivity|].
  unfold word8_array_value. rewrite Int.testbit_repr by exact HI.
  symmetry. apply word_toZ_high_bits. change (Z.of_nat (Nat.pow 2 3)) with 8; lia.
Qed.

Theorem read8s_run_layout m bo output bf base bi edge cursor (xs : list (Ty.tySem (Word 3))) :
  0 <= output -> output + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Mem.range_perm m bo output (output + Z.of_nat (length xs)) Cur Writable ->
  bf <> bo -> bf <> bi -> bo <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 8 * Z.of_nat (length xs) <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  (forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bi edge (cursor + 8 * Z.of_nat i) x) ->
  exists mf,
    read8s_run bo output bf base (map word8_array_value xs) m mf /\
    uint8_array_at mf bo output (map word8_array_value xs) /\
    frame_fields_at mf bf base bi edge (cursor + 8 * Z.of_nat (length xs)) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/
        output + Z.of_nat (length xs) <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  revert m output cursor. induction xs as [|x xs IH]; intros m output cursor
    HB HM HP Hfo Hfi Hoi Hbase HC Hmax HF HW HI.
  - exists m. split; [reflexivity|]. split.
    + intros i v Hv. destruct i; discriminate.
    + split; [rewrite Z.add_0_r; exact HF|]. split; [intros; reflexivity|]. split; auto.
  - assert (Hfirst : frame_input_word_at m bi edge cursor x).
    { pose proof (HI O x eq_refl) as H. replace (cursor + 8 * Z.of_nat O) with cursor in H by lia. exact H. }
    destruct (eval_read8_word_at m bf base bi edge cursor x Hbase
      ltac:(cbn [length] in Hmax; lia) HF Hfirst HW Hfi)
      as (mr & HR & HFr & HMemr & HPermr & HValidr).
    assert (HStoreAccess : Mem.valid_access mr Mint8unsigned bo output Writable).
    { split; [|change (1 | output); exists output; lia]. intros ofs Hrange. apply HPermr, HP.
      cbn [length]. change (size_chunk Mint8unsigned) with 1 in Hrange. lia. }
    destruct (Mem.valid_access_store mr Mint8unsigned bo output
      (Vint (Int.zero_ext 8 (word8_array_value x))) HStoreAccess) as [ms HS].
    assert (HFNext : frame_fields_at ms bf base bi edge (cursor + 8)).
    { destruct HFr as [Hedge Hcursor]. split;
        erewrite Mem.load_store_other; [exact Hedge|exact HS|left; congruence|
          exact Hcursor|exact HS|left; congruence]. }
    assert (HWNext : Mem.valid_access ms Mint64 bf (base + 8) Writable).
    { destruct HW as [Hperm Halign]. split; [|exact Halign].
      intros ofs Hrange. eapply Mem.perm_store_1; [exact HS|]. apply HPermr, Hperm; exact Hrange. }
    assert (HPNext : Mem.range_perm ms bo (output + 1)
      (output + 1 + Z.of_nat (length xs)) Cur Writable).
    { intros ofs Hrange. eapply Mem.perm_store_1; [exact HS|]. apply HPermr, HP.
      cbn [length]. lia. }
    assert (HINext : forall i y, nth_error xs i = Some y ->
      frame_input_word_at ms bi edge (cursor + 8 + 8 * Z.of_nat i) y).
    { intros i y Hy. eapply frame_input_bits_at_preserved.
      - intros ofs w HL. erewrite Mem.load_store_other; [|exact HS|left; congruence].
        rewrite HMemr by (left; congruence). exact HL.
      - pose proof (HI (S i) y Hy) as H.
        replace (cursor + 8 * Z.of_nat (S i)) with (cursor + 8 + 8 * Z.of_nat i) in H by lia.
        exact H. }
    destruct (IH ms (output + 1) (cursor + 8) ltac:(lia)
      ltac:(cbn [length] in HM; lia)
      HPNext Hfo Hfi Hoi Hbase ltac:(lia) ltac:(cbn [length] in Hmax; lia)
      HFNext HWNext HINext)
      as (mf & HRun & HArray & HFields & HMemory & HPerm & HValid).
    assert (HFirstFinal : Mem.load Mint8unsigned mf bo output = Some (Vint (word8_array_value x))).
    { rewrite HMemory; [|left; congruence|right; left; cbn; lia].
      pose proof (Mem.load_store_same _ _ _ _ _ _ HS) as H.
      change (Mem.load Mint8unsigned ms bo output =
        Some (Vint (Int.zero_ext 8 (Int.zero_ext 8 (word8_array_value x))))) in H.
      rewrite !word8_array_value_zero_ext in H. exact H. }
    exists mf. split.
    + cbn [map read8s_run]. exists mr, ms. auto.
    + split.
      * intros [|i] y Hy.
        -- cbn in Hy. injection Hy as <-. replace (output + Z.of_nat O) with output by lia.
           exact HFirstFinal.
        -- cbn [map nth_error] in Hy.
           replace (output + Z.of_nat (S i)) with (output + 1 + Z.of_nat i) by lia.
           exact (HArray i y Hy).
      * split.
        -- replace (cursor + 8 * Z.of_nat (length (x :: xs))) with
             (cursor + 8 + 8 * Z.of_nat (length xs)) by (cbn [length]; lia). exact HFields.
        -- split.
           ++ intros chunk b ofs Hbf Hbo. rewrite HMemory.
              ** erewrite Mem.load_store_other; [apply HMemr; exact Hbf|exact HS|].
                 cbn [length] in Hbo. change (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 1 <= ofs).
                 destruct Hbo as [HN|[HL|HH]]; auto; lia.
              ** exact Hbf.
              ** cbn [length] in Hbo. destruct Hbo as [HN|[HL|HH]]; auto; right; lia.
           ++ split.
              ** intros b ofs kind p H. apply HPerm. eapply Mem.perm_store_1; [exact HS|].
                 apply HPermr; exact H.
              ** intros b H. apply HValid. eapply Mem.store_valid_block_1; [exact HS|].
                 apply HValidr; exact H.
Qed.

Theorem eval_read8s_layout m bo output bf base bi edge cursor (xs : list (Ty.tySem (Word 3))) :
  0 <= output -> output + Z.of_nat (length xs) <= Ptrofs.max_unsigned ->
  Mem.range_perm m bo output (output + Z.of_nat (length xs)) Cur Writable ->
  bf <> bo -> bf <> bi -> bo <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 8 * Z.of_nat (length xs) <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  (forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bi edge (cursor + 8 * Z.of_nat i) x) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_read8s)
      [Vptr bo (Ptrofs.repr output); Vlong (Int64.repr (Z.of_nat (length xs)));
        Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint8_array_at mf bo output (map word8_array_value xs) /\
    frame_fields_at mf bf base bi edge (cursor + 8 * Z.of_nat (length xs)) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/
        output + Z.of_nat (length xs) <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HM HP Hfo Hfi Hoi Hbase HC Hmax HF HW HI.
  destruct (read8s_run_layout m bo output bf base bi edge cursor xs
    HB HM HP Hfo Hfi Hoi Hbase HC Hmax HF HW HI) as [mf [HR HO]].
  exists mf. split; [|exact HO].
  rewrite <- (map_length word8_array_value xs) at 1.
  eapply eval_read8s_from_run; [exact HB|rewrite map_length; exact HM|
    rewrite map_length; lia|exact HR].
Qed.
