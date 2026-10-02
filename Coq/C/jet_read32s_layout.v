(** Derive read32s reader calls and stores from initial frame and writable-array
    contracts. This helper is not itself an individual jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word.
Require Import C.jets C.jet_exec C.jet_read32s_exec C.jet_uint32_array_init.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_read32_input_word_total.
Require Import C.jet_read32_input_word C.jet_word_repr.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition word32_carrier (x : Ty.tySem (Word 5)) := Int64.repr (@toZ (WordToZ 5) x).
Definition word32_array_value (x : Ty.tySem (Word 5)) := Int.repr (@toZ (WordToZ 5) x).
Lemma word32_carrier_loword x : Int64.loword (word32_carrier x) = word32_array_value x.
Proof.
  unfold word32_carrier, word32_array_value, Int64.loword.
  rewrite Int64.unsigned_repr; [reflexivity|].
  pose proof (word32_toZ_range x). change (0 <= @toZ (WordToZ 5) x <= 18446744073709551615). lia.
Qed.


Theorem read32s_run_layout m bo output bf base bi edge cursor (xs : list (Ty.tySem (Word 5))) :
  0 <= output -> output + 4 * Z.of_nat (length xs) <= Ptrofs.max_unsigned -> (4 | output) ->
  Mem.range_perm m bo output (output + 4 * Z.of_nat (length xs)) Cur Writable ->
  bf <> bo -> bf <> bi -> bo <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 32 * Z.of_nat (length xs) <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  (forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bi edge (cursor + 32 * Z.of_nat i) x) ->
  exists mf,
    read32s_run bo output bf base (map word32_carrier xs) m mf /\
    uint32_array_at mf bo output (map word32_array_value xs) /\
    frame_fields_at mf bf base bi edge (cursor + 32 * Z.of_nat (length xs)) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/
        output + 4 * Z.of_nat (length xs) <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  revert m output cursor. induction xs as [|x xs IH]; intros m output cursor
    HB HM HA HP Hfo Hfi Hoi Hbase HC Hmax HF HW HI.
  - exists m. split; [reflexivity|]. split.
    + intros i v Hv. destruct i; discriminate.
    + split; [rewrite Z.add_0_r; exact HF|]. split; [intros; reflexivity|]. split; auto.
  - assert (Hfirst : frame_input_word_at m bi edge cursor x).
    { pose proof (HI O x eq_refl) as H. replace (cursor + 32 * Z.of_nat O) with cursor in H by lia. exact H. }
    destruct (eval_read32_word_at m bf base bi edge cursor x Hbase
      ltac:(cbn [length] in Hmax; lia) HF Hfirst HW Hfi)
      as (mr & r & HR & Hr & HFr & HMemr & HPermr & HValidr).
    assert (Hrepr : r = word32_carrier x).
    { unfold word32_carrier. rewrite <- Hr. symmetry. apply Int64.repr_unsigned. }
    subst r.
    assert (HStoreAccess : Mem.valid_access mr Mint32 bo output Writable).
    { split; [|exact HA]. intros ofs Hrange. apply HPermr, HP.
      cbn [length]. change (size_chunk Mint32) with 4 in Hrange. lia. }
    destruct (Mem.valid_access_store mr Mint32 bo output
      (Vint (Int64.loword (word32_carrier x))) HStoreAccess) as [ms HS].
    assert (HFNext : frame_fields_at ms bf base bi edge (cursor + 32)).
    { destruct HFr as [Hedge Hcursor]. split;
        erewrite Mem.load_store_other; [exact Hedge|exact HS|left; congruence|
          exact Hcursor|exact HS|left; congruence]. }
    assert (HWNext : Mem.valid_access ms Mint64 bf (base + 8) Writable).
    { destruct HW as [Hperm Halign]. split; [|exact Halign].
      intros ofs Hrange. eapply Mem.perm_store_1; [exact HS|]. apply HPermr, Hperm; exact Hrange. }
    assert (HPNext : Mem.range_perm ms bo (output + 4)
      (output + 4 + 4 * Z.of_nat (length xs)) Cur Writable).
    { intros ofs Hrange. eapply Mem.perm_store_1; [exact HS|]. apply HPermr, HP.
      cbn [length]. lia. }
    assert (HINext : forall i y, nth_error xs i = Some y ->
      frame_input_word_at ms bi edge (cursor + 32 + 32 * Z.of_nat i) y).
    { intros i y Hy. eapply frame_input_bits_at_preserved.
      - intros ofs w HL. erewrite Mem.load_store_other; [|exact HS|left; congruence].
        rewrite HMemr by (left; congruence). exact HL.
      - pose proof (HI (S i) y Hy) as H.
        replace (cursor + 32 * Z.of_nat (S i)) with (cursor + 32 + 32 * Z.of_nat i) in H by lia.
        exact H. }
    destruct (IH ms (output + 4) (cursor + 32) ltac:(lia)
      ltac:(cbn [length] in HM; lia)
      ltac:(destruct HA as [k Hk]; exists (k + 1); lia)
      HPNext Hfo Hfi Hoi Hbase ltac:(lia) ltac:(cbn [length] in Hmax; lia)
      HFNext HWNext HINext)
      as (mf & HRun & HArray & HFields & HMemory & HPerm & HValid).
    assert (HFirstFinal : Mem.load Mint32 mf bo output = Some (Vint (word32_array_value x))).
    { rewrite HMemory; [|left; congruence|right; left; cbn; lia].
      rewrite <- word32_carrier_loword. exact (Mem.load_store_same _ _ _ _ _ _ HS). }
    exists mf. split.
    + cbn [map read32s_run]. exists mr, ms. auto.
    + split.
      * intros [|i] y Hy.
        -- cbn in Hy. injection Hy as <-. replace (output + 4 * Z.of_nat O) with output by lia.
           exact HFirstFinal.
        -- cbn [map nth_error] in Hy.
           replace (output + 4 * Z.of_nat (S i)) with (output + 4 + 4 * Z.of_nat i) by lia.
           exact (HArray i y Hy).
      * split.
        -- replace (cursor + 32 * Z.of_nat (length (x :: xs))) with
             (cursor + 32 + 32 * Z.of_nat (length xs)) by (cbn [length]; lia). exact HFields.
        -- split.
           ++ intros chunk b ofs Hbf Hbo. rewrite HMemory.
              ** erewrite Mem.load_store_other; [apply HMemr; exact Hbf|exact HS|].
                 cbn [length] in Hbo. change (b <> bo \/ ofs + size_chunk chunk <= output \/ output + 4 <= ofs).
                 destruct Hbo as [HN|[HL|HH]]; auto; lia.
              ** exact Hbf.
              ** cbn [length] in Hbo. destruct Hbo as [HN|[HL|HH]]; auto; right; lia.
           ++ split.
              ** intros b ofs kind p H. apply HPerm. eapply Mem.perm_store_1; [exact HS|].
                 apply HPermr; exact H.
              ** intros b H. apply HValid. eapply Mem.store_valid_block_1; [exact HS|].
                 apply HValidr; exact H.
Qed.

Theorem eval_read32s_layout m bo output bf base bi edge cursor (xs : list (Ty.tySem (Word 5))) :
  0 <= output -> output + 4 * Z.of_nat (length xs) <= Ptrofs.max_unsigned -> (4 | output) ->
  Mem.range_perm m bo output (output + 4 * Z.of_nat (length xs)) Cur Writable ->
  bf <> bo -> bf <> bi -> bo <> bi ->
  frame_base_valid base -> 0 <= cursor -> cursor + 32 * Z.of_nat (length xs) <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor -> Mem.valid_access m Mint64 bf (base + 8) Writable ->
  (forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bi edge (cursor + 32 * Z.of_nat i) x) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_read32s)
      [Vptr bo (Ptrofs.repr output); Vlong (Int64.repr (Z.of_nat (length xs)));
        Vptr bf (Ptrofs.repr base)] E0 mf Vundef /\
    uint32_array_at mf bo output (map word32_array_value xs) /\
    frame_fields_at mf bf base bi edge (cursor + 32 * Z.of_nat (length xs)) /\
    (forall chunk b ofs,
      (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
      (b <> bo \/ ofs + size_chunk chunk <= output \/
        output + 4 * Z.of_nat (length xs) <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HM HA HP Hfo Hfi Hoi Hbase HC Hmax HF HW HI.
  destruct (read32s_run_layout m bo output bf base bi edge cursor xs
    HB HM HA HP Hfo Hfi Hoi Hbase HC Hmax HF HW HI) as [mf [HR HO]].
  exists mf. split; [|exact HO].
  rewrite <- (map_length word32_carrier xs) at 1.
  eapply eval_read32s_from_run; [exact HB|rewrite map_length; exact HM|
    rewrite map_length; lia|exact HR].
Qed.
