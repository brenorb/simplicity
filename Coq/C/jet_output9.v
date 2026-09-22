(** Uniform nine-bit output representation across the first word boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Bit.
Require Import C.jets C.jet_exec C.jet_spec C.jet_frame_spec C.jet_frame_arith.
Require Import C.jet_add8_word C.jet_increment8_crossing_word C.jet_crossing_frame.
Require Import C.jet_carry_byte_position C.jet_carry_byte_crossing C.jet_two_word_input.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition output9 (m : mem) (bw : block) cursor (value : Ty.tySem (Ty.Prod Bit Word8)) : Prop :=
  if Z_le_dec cursor 64 then
    exists w, Mem.load Mint64 m bw 0 = Some (Vlong w) /\
      decode_carry_word8 (Int64.shru w (Int64.repr (cursor - 9))) = value
  else exists high low,
    Mem.load Mint64 m bw 8 = Some (Vlong high) /\
    Mem.load Mint64 m bw 0 = Some (Vlong low) /\
    decode_carry_crossing (cursor - 65) high low = value.

Definition output9_prefix (m mf : mem) (bw : block) cursor : Prop :=
  let addr := if Z_le_dec cursor 64 then 0 else 8 in
  let count := if Z_le_dec cursor 64 then cursor else cursor - 64 in
  forall old, Mem.load Mint64 m bw addr = Some (Vlong old) ->
    exists w, Mem.load Mint64 mf bw addr = Some (Vlong w) /\
      word_outside_eq 0 count w old.

Lemma write_frame_single_word9 m bd bw cursor :
  9 <= cursor <= 64 -> write_frame m bd bw 0 cursor 9 ->
  single_word_output m bd bw cursor.
Proof.
  intros HC [HF [HN [HM [HD [PD HW]]]]].
  pose proof (HW 0 ltac:(lia)) as H.
  cbn zeta in H. unfold write_cell_address in H.
  replace (cursor - 1 - 0) with (cursor - 1) in H by lia.
  rewrite Z.div_small in H by lia.
  change (0 <= 0 /\ 0 + 8 <= Ptrofs.max_unsigned /\
    Mem.valid_access m Mint64 bw 0 Writable /\
    exists w, Mem.load Mint64 m bw 0 = Some (Vlong w)) in H.
  destruct H as [_ [_ [PW HX]]].
  split; [exact HF |]. split; [lia |]. split; [exact HD |].
  split; [exact PD |]. split; assumption.
Qed.

Lemma write_frame_preserved m mf bd bw edge cursor count :
  (forall chunk b ofs v, b = bd \/ b = bw ->
    Mem.load chunk m b ofs = Some v -> Mem.load chunk mf b ofs = Some v) ->
  (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) ->
  write_frame m bd bw edge cursor count ->
  write_frame mf bd bw edge cursor count.
Proof.
  intros HL HP [[HE HO] [HN [HM [HD [PD HW]]]]].
  split; [split; eapply HL; eauto |].
  split; [exact HN |]. split; [exact HM |]. split; [exact HD |].
  split; [eapply permissions_preserve_access; eauto |].
  intros i HI. specialize (HW i HI). cbn zeta in *.
  destruct HW as [HA [HB [PW [w HW]]]].
  split; [exact HA |]. split; [exact HB |].
  split; [eapply permissions_preserve_access; eauto |].
  exists w. eapply HL; eauto.
Qed.

Lemma output9_preserved m mf bw cursor value :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  output9 m bw cursor value -> output9 mf bw cursor value.
Proof.
  intros HL. unfold output9. destruct (Z_le_dec cursor 64).
  - intros [w [HW HV]]. exists w; split; eauto.
  - intros [high [low [HH [HW HV]]]]. exists high, low; split; [eauto |]; split; eauto.
Qed.

Lemma output9_prefix_preserved m mr me mf bw cursor :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mr bw ofs = Some (Vlong w)) ->
  (forall ofs w, Mem.load Mint64 me bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  output9_prefix mr me bw cursor -> output9_prefix m mf bw cursor.
Proof.
  intros HR HF HP. unfold output9_prefix in *.
  intros old HO. destruct (HP old (HR _ _ HO)) as [w [HW HV]].
  exists w; split; eauto.
Qed.

Theorem eval_carry_byte_output9 m bd bw cursor (carry : bool) x :
  9 <= cursor <= 72 ->
  write_frame m bd bw 0 cursor 9 ->
  exists mb mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bd Ptrofs.zero; Vint (if carry then Int.one else Int.zero)]
      E0 mb (Vint (if carry then Int.one else Int.zero)) /\
    ClightBigstep.Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
      [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef /\
    output9 mf bw cursor
      ((if carry then inr tt else inl tt), decode_word8 (Int64.repr (Int.unsigned x))) /\
    output9_prefix m mf bw cursor /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (cursor - 9))) /\
    loads_outside_blocks m mf bd bw /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p).
Proof.
  intros HC HF. destruct (Z_le_dec cursor 64) as [HOne | HTwo].
  - destruct (write_frame_single_word9 m bd bw cursor ltac:(lia) HF)
      as [HF0 [HN [HD [PD [PW [old HW]]]]]].
    destruct (eval_carry_byte_position m bd bw cursor carry x old ltac:(lia) HF0 HD PD PW HW)
      as [mb [mf [output [HB [HByte [HOut [HBit [HValue [HPrefix [HOff [HMem HPerm]]]]]]]]]]].
    exists mb, mf. split; [exact HB |]. split; [exact HByte |]. split.
    + unfold output9. destruct (Z_le_dec cursor 64); [|lia].
      exists output. split; [exact HOut |].
      unfold decode_carry_word8.
      rewrite Int64.bits_shru by (change (0 <= 8 < 64); lia).
      rewrite cursor_unsigned by lia.
      rewrite Coqlib.zlt_true by (change (8 + (cursor - 9) < 64); lia).
      replace (8 + (cursor - 9)) with (cursor - 1) by lia.
      rewrite HBit, HValue. reflexivity.
    + split.
      * unfold output9_prefix. destruct (Z_le_dec cursor 64); [|lia].
        intros old' HOld. assert (old' = old) by congruence. subst old'.
        exists output; auto.
      * split; [exact HOff |]. split; assumption.
  - set (k := cursor - 65).
    assert (HK : 0 <= k <= 7) by (unfold k; lia).
    replace cursor with (65 + k) in HF by (unfold k; lia).
    destruct (crossing_carry_frame_words m bd bw k HK HF)
      as [HF0 [HD [PD [PH [PW [oldhigh [oldlow [HH HW]]]]]]]].
    destruct (eval_carry_byte_crossing m bd bw k carry x oldhigh oldlow HK HF0 HD PD PH PW HH HW)
      as [mb [mf [high [low [HB [HByte [HHout [HLout [HBit [HValue [HPrefix [HOff [HMem HPerm]]]]]]]]]]]]].
    exists mb, mf. split; [exact HB |]. split; [exact HByte |]. split.
    + unfold output9. destruct (Z_le_dec cursor 64); [lia|].
      exists high, low. split; [exact HHout |]. split; [exact HLout |].
      fold k.
      unfold decode_carry_crossing. rewrite HBit, HValue. reflexivity.
    + split.
      * unfold output9_prefix. destruct (Z_le_dec cursor 64); [lia|].
        intros old HOld. assert (old = oldhigh) by congruence. subst old.
        exists high; split; [exact HHout |].
        replace (cursor - 64) with (k + 1) by (unfold k; lia). exact HPrefix.
      * split.
        -- replace (cursor - 9) with (56 + k) by (unfold k; lia). exact HOff.
        -- split; assumption.
Qed.
