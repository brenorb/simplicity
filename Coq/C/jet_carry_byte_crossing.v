(** Compose actual carry and byte calls across all eight nine-bit splits. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_spec C.jet_word_bits C.jet_frame_arith.
Require Import C.jet_crossing_word C.jet_writeBit_high C.jet_write8_split.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Definition crossing_carry_high k old (carry : bool) :=
  if carry then Int64.or old (Int64.shl Int64.one (Int64.repr k))
  else clear_low (k + 1) old.

Lemma crossing_carry_bit k old carry : 0 <= k <= 7 ->
  Int64.testbit (crossing_carry_high k old carry) k = carry.
Proof.
  intros HK. unfold crossing_carry_high. destruct carry.
  - rewrite Int64.bits_or, Int64.bits_shl by (change (0 <= k < 64); lia).
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    replace (k - k) with 0 by lia.
    change (orb (Int64.testbit old k) true = true). apply orb_true_r.
  - rewrite clear_low_bits by lia. rewrite zlt_true by lia. reflexivity.
Qed.

Lemma crossing_carry_prefix k old carry : 0 <= k <= 7 ->
  word_outside_eq 0 (k + 1) (crossing_carry_high k old carry) old.
Proof.
  intros HK i HI Hout. unfold crossing_carry_high. destruct carry.
  - rewrite Int64.bits_or, Int64.bits_shl by exact HI.
    rewrite cursor_unsigned by lia. rewrite zlt_false by lia.
    rewrite Int64.bits_one. destruct (zeq (i - k) 0); [lia|apply orb_false_r].
  - rewrite clear_low_bits by lia. rewrite zlt_false by lia. reflexivity.
Qed.

Theorem eval_carry_byte_crossing m bd bw k (carry : bool) x oldhigh oldlow :
  0 <= k <= 7 ->
  frame_fields m bd bw 0 (65 + k) ->
  bd <> bw ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  Mem.load Mint64 m bw 8 = Some (Vlong oldhigh) ->
  Mem.load Mint64 m bw 0 = Some (Vlong oldlow) ->
  exists mb mf high low,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
      [Vptr bd Ptrofs.zero; Vint (if carry then Int.one else Int.zero)]
      E0 mb (Vint (if carry then Int.one else Int.zero)) /\
    ClightBigstep.Clight2.eval_funcall ge0 mb (Internal f_simplicity_write8)
      [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef /\
    Mem.load Mint64 mf bw 8 = Some (Vlong high) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong low) /\
    Int64.testbit high k = carry /\
    decode_word8 (crossing_byte k high low) =
      decode_word8 (Int64.repr (Int.unsigned x)) /\
    word_outside_eq 0 (k + 1) high oldhigh /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (56 + k))) /\
    loads_outside_blocks m mf bd bw /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p).
Proof.
  intros HK [HE HO] HD PD PH PL HH HL.
  destruct (Mem.valid_access_store m Mint64 bd 8 (Vlong (Int64.repr (64 + k))) PD)
    as [mo SO].
  assert (PHo : Mem.valid_access mo Mint64 bw 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mo Mint64 bw 8
    (Vlong (crossing_carry_high k oldhigh carry)) PHo) as [mb SB].
  assert (HC : ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_writeBit)
    [Vptr bd Ptrofs.zero; Vint (if carry then Int.one else Int.zero)]
    E0 mb (Vint (if carry then Int.one else Int.zero))).
  { replace (65 + k) with (64 + (k + 1)) in HO by lia.
    replace (64 + k) with (64 + (k + 1) - 1) in SO by lia.
    replace k with (k + 1 - 1) in SB at 1 by lia.
    unfold crossing_carry_high in SB.
    destruct carry.
    - eapply eval_writeBit_true_high with (k := k + 1); eauto; lia.
    - replace (k + 1 - 1 + 1) with (k + 1) in SB by lia.
      eapply eval_writeBit_false_high; eauto; lia. }
  assert (HEb : Mem.load Mptr mb bd 0 = Some (Vptr bw Ptrofs.zero)).
  { erewrite Mem.load_store_other; [|exact SB|auto].
    erewrite Mem.load_store_other; [exact HE|exact SO|right; left; change (0 + 8 <= 8); lia]. }
  assert (HOb : Mem.load Mint64 mb bd 8 = Some (Vlong (Int64.repr (64 + k)))).
  { erewrite Mem.load_store_other; [|exact SB|auto].
    exact (Mem.load_store_same _ _ _ _ _ _ SO). }
  assert (HHb : Mem.load Mint64 mb bw 8 = Some (Vlong (crossing_carry_high k oldhigh carry)))
    by exact (Mem.load_store_same _ _ _ _ _ _ SB).
  assert (HLb : Mem.load Mint64 mb bw 0 = Some (Vlong oldlow)).
  { erewrite Mem.load_store_other; [|exact SB|right; left; cbn; lia].
    erewrite Mem.load_store_other; [exact HL|exact SO|auto]. }
  assert (PDb : Mem.valid_access mb Mint64 bd 8 Writable) by (eauto using Mem.store_valid_access_1).
  assert (PHb : Mem.valid_access mb Mint64 bw 8 Writable) by (eauto using Mem.store_valid_access_1).
  assert (PLb : Mem.valid_access mb Mint64 bw 0 Writable) by (eauto using Mem.store_valid_access_1).
  destruct (eval_write8_split mb bd bw k x (crossing_carry_high k oldhigh carry) oldlow HK
    (conj HEb HOb) HD PDb PHb PLb HHb HLb)
    as [mf [high [low [HW [HHf [HLf [HV [HP [HOf [HM Hperm]]]]]]]]]].
  exists mb, mf, high, low.
  split; [exact HC |]. split; [exact HW |]. split; [exact HHf |]. split; [exact HLf |].
  split.
  - rewrite (HP k ltac:(lia) ltac:(lia)). apply crossing_carry_bit; exact HK.
  - split; [exact HV |]. split.
    + intros i HI Hout. rewrite HP by (try exact HI; lia).
      apply crossing_carry_prefix; assumption.
    + split; [exact HOf |]. split.
      * intros chunk b ofs HVb Hbd Hbw.
        rewrite HM; [|eauto using Mem.store_valid_block_1|exact Hbd|exact Hbw].
        erewrite Mem.load_store_other; [|exact SB|auto].
        eapply Mem.load_store_other; [exact SO|auto].
      * intros b ofs kind p HPm. apply Hperm. eauto using Mem.perm_store_1.
Qed.
