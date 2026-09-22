(** A byte following a crossing carry: includes the exact-boundary k=0 case. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_spec.
Require Import C.jet_crossing_word C.jet_crossing_frame C.jet_write8_crossing_frame.
Require Import C.jet_write8_position C.jet_word_position C.jet_word_decode.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Lemma crossing_byte_zero high low :
  crossing_byte 0 high low = Int64.shru low (Int64.repr 56).
Proof.
  unfold crossing_byte. rewrite Int64.zero_ext_below by lia.
  change (Int64.or Int64.zero (Int64.shru low (Int64.repr 56)) =
    Int64.shru low (Int64.repr 56)).
  apply Int64.or_zero_l.
Qed.

Theorem eval_write8_split m bd bw k x oldhigh oldlow :
  0 <= k <= 7 ->
  frame_fields m bd bw 0 (64 + k) ->
  bd <> bw ->
  Mem.valid_access m Mint64 bd 8 Writable ->
  Mem.valid_access m Mint64 bw 8 Writable ->
  Mem.valid_access m Mint64 bw 0 Writable ->
  Mem.load Mint64 m bw 8 = Some (Vlong oldhigh) ->
  Mem.load Mint64 m bw 0 = Some (Vlong oldlow) ->
  exists mf high low,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
      [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef /\
    Mem.load Mint64 mf bw 8 = Some (Vlong high) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong low) /\
    decode_word8 (crossing_byte k high low) =
      decode_word8 (Int64.repr (Int.unsigned x)) /\
    word_outside_eq 0 k high oldhigh /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (56 + k))) /\
    loads_outside_blocks m mf bd bw /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p).
Proof.
  intros HK HF HD PD PH PL HH HL.
  destruct (Z.eq_dec k 0) as [-> | HNZ].
  - destruct HF as [HE HO].
    destruct (Mem.valid_access_store m Mint64 bw 0
      (Vlong (put_byte 64 oldlow (Int64.repr (Int.unsigned x)))) PL) as [mw SW].
    assert (PDw : Mem.valid_access mw Mint64 bd 8 Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mw Mint64 bd 8 (Vlong (Int64.repr 56)) PDw)
      as [mf SF].
    exists mf, oldhigh, (put_byte 64 oldlow (Int64.repr (Int.unsigned x))).
    split.
    + eapply eval_write8_position; eauto; lia.
    + split.
      * erewrite Mem.load_store_other; [|exact SF|auto].
        erewrite Mem.load_store_other; [exact HH|exact SW|right; right; cbn; lia].
      * split.
        -- erewrite Mem.load_store_other; [|exact SF|auto].
           exact (Mem.load_store_same _ _ _ _ _ _ SW).
        -- split.
           ++ rewrite crossing_byte_zero.
              change (decode_word8 (Int64.shru
                (put_byte 64 oldlow (Int64.repr (Int.unsigned x))) (Int64.repr (64 - 8))) =
                decode_word8 (Int64.repr (Int.unsigned x))).
              rewrite <- decode_word8_projection, put_byte_projection by lia.
              apply decode_word8_projection.
           ++ split; [intros i HI Hout; reflexivity |].
              split; [exact (Mem.load_store_same _ _ _ _ _ _ SF) |].
              split.
              ** intros chunk b ofs HV Hbd Hbw.
                 erewrite Mem.load_store_other; [|exact SF|auto].
                 eapply Mem.load_store_other; [exact SW|auto].
              ** intros b ofs kind p HP. eauto using Mem.perm_store_1.
  - assert (HP : write_frame m bd bw 0 (64 + k) 8).
    { eapply crossing_frame_from_words; eauto; lia. }
    destruct (eval_write8_crossing_frame m bd bw k x ltac:(lia) HP)
      as [mf [high [low [HC [HH' [HL' [HV [Hprefix [HO [HM Hperm]]]]]]]]]].
    exists mf, high, low.
    split; [exact HC |]. split; [exact HH' |]. split; [exact HL' |].
    split; [exact HV |]. split; [apply Hprefix; exact HH |].
    split; [exact HO |]. split; assumption.
Qed.
