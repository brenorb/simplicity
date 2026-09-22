(** Complete carry/byte helper composition at any non-crossing output cursor. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_spec C.jet_frame_arith.
Require Import C.jet_word_bits C.jet_word_decode C.jet_word_position.
Require Import C.jet_writeBit_position C.jet_write8_position.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition carry_at cursor old (carry : bool) :=
  if carry then Int64.or old (Int64.shl Int64.one (Int64.repr (cursor - 1)))
  else clear_low cursor old.
Definition carry_byte_at cursor old carry x :=
  put_byte (cursor - 1) (carry_at cursor old carry) (Int64.repr (Int.unsigned x)).

Lemma carry_at_bit cursor old carry : 1 <= cursor <= 64 ->
  Int64.testbit (carry_at cursor old carry) (cursor - 1) = carry.
Proof.
  intros HC. unfold carry_at. destruct carry.
  - rewrite Int64.bits_or, Int64.bits_shl by (change (0 <= cursor - 1 < 64); lia).
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    replace (cursor - 1 - (cursor - 1)) with 0 by lia.
    change (orb (Int64.testbit old (cursor - 1)) true = true). apply orb_true_r.
  - rewrite clear_low_bits by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Lemma carry_byte_at_bit cursor old carry x : 9 <= cursor <= 64 ->
  Int64.testbit (carry_byte_at cursor old carry x) (cursor - 1) = carry.
Proof.
  intros HC. unfold carry_byte_at. rewrite put_byte_bits by lia.
  rewrite zlt_false by lia. apply carry_at_bit; lia.
Qed.

Lemma carry_byte_at_decode cursor old carry x : 9 <= cursor <= 64 ->
  decode_word8 (Int64.shru (carry_byte_at cursor old carry x) (Int64.repr (cursor - 9))) =
    decode_word8 (Int64.repr (Int.unsigned x)).
Proof.
  intros HC. unfold carry_byte_at.
  replace (cursor - 9) with (cursor - 1 - 8) by lia.
  rewrite <- decode_word8_projection, put_byte_projection by lia.
  apply decode_word8_projection.
Qed.

Lemma carry_byte_at_prefix cursor old carry x : 9 <= cursor <= 64 ->
  word_outside_eq 0 cursor (carry_byte_at cursor old carry x) old.
Proof.
  intros HC i HI Hout. unfold carry_byte_at. rewrite put_byte_bits by lia.
  rewrite zlt_false by lia. unfold carry_at. destruct carry.
  - rewrite Int64.bits_or, Int64.bits_shl by exact HI.
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    rewrite Int64.bits_one. destruct (zeq (i - (cursor - 1)) 0); [lia|apply orb_false_r].
  - rewrite clear_low_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

Theorem eval_carry_byte_position m bd bw cursor (carry : bool) x old :
  9 <= cursor <= 64 ->
  frame_fields m bd bw 0 cursor ->
  bd <> bw ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  Mem.load Mint64 m bw 0 = Some (Vlong old) ->
  exists mb mf output,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bd Ptrofs.zero; Vint (if carry then Int.one else Int.zero)]
      E0 mb (Vint (if carry then Int.one else Int.zero)) /\
    ClightBigstep.Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
      [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef /\
    Mem.load Mint64 mf bw 0 = Some (Vlong output) /\
    Int64.testbit output (cursor - 1) = carry /\
    decode_word8 (Int64.shru output (Int64.repr (cursor - 9))) =
      decode_word8 (Int64.repr (Int.unsigned x)) /\
    word_outside_eq 0 cursor output old /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (cursor - 9))) /\
    loads_outside_blocks m mf bd bw /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p).
Proof.
  intros HC [HE HO] HD PD PW HW.
  destruct (Mem.valid_access_store m Mint64 bd 8 (Vlong (Int64.repr (cursor - 1))) PD)
    as [mo SO].
  assert (PWo : Mem.valid_access mo Mint64 bw 0 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mo Mint64 bw 0 (Vlong (carry_at cursor old carry)) PWo)
    as [mb SB].
  assert (HB : ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd Ptrofs.zero; Vint (if carry then Int.one else Int.zero)]
    E0 mb (Vint (if carry then Int.one else Int.zero))).
  { unfold carry_at in SB. destruct carry.
    - eapply eval_writeBit_true_position; eauto; lia.
    - eapply eval_writeBit_false_position; eauto; lia. }
  assert (HEb : Mem.load Mptr mb bd 0 = Some (Vptr bw Ptrofs.zero)).
  { erewrite Mem.load_store_other; [|exact SB|auto].
    erewrite Mem.load_store_other; [exact HE|exact SO|right; left; change (0 + 8 <= 8); lia]. }
  assert (HOb : Mem.load Mint64 mb bd 8 = Some (Vlong (Int64.repr (cursor - 1)))).
  { erewrite Mem.load_store_other; [|exact SB|auto].
    exact (Mem.load_store_same _ _ _ _ _ _ SO). }
  assert (HWb : Mem.load Mint64 mb bw 0 = Some (Vlong (carry_at cursor old carry)))
    by exact (Mem.load_store_same _ _ _ _ _ _ SB).
  assert (PWb : Mem.valid_access mb Mint64 bw 0 Writable)
    by (eauto using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mb Mint64 bw 0
    (Vlong (carry_byte_at cursor old carry x)) PWb) as [mw SW].
  assert (PDw : Mem.valid_access mw Mint64 bd 8 Writable)
    by (eauto 8 using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mw Mint64 bd 8 (Vlong (Int64.repr (cursor - 9))) PDw)
    as [mf SF].
  exists mb, mf, (carry_byte_at cursor old carry x).
  split; [exact HB |]. split.
  - replace (cursor - 9) with (cursor - 1 - 8) in SF by lia.
    eapply eval_write8_position; eauto; lia.
  - split.
    + erewrite Mem.load_store_other; [|exact SF|auto].
      exact (Mem.load_store_same _ _ _ _ _ _ SW).
    + split; [apply carry_byte_at_bit; exact HC |].
      split; [apply carry_byte_at_decode; exact HC |].
      split; [apply carry_byte_at_prefix; exact HC |].
      split; [exact (Mem.load_store_same _ _ _ _ _ _ SF) |].
      split.
      * intros chunk b ofs HV Hbd Hbw.
        erewrite Mem.load_store_other; [|exact SF|auto].
        erewrite Mem.load_store_other; [|exact SW|auto].
        erewrite Mem.load_store_other; [|exact SB|auto].
        eapply Mem.load_store_other; [exact SO|auto].
      * intros b ofs kind p HP. eauto 8 using Mem.perm_store_1.
Qed.
