(** The arbitrary-byte crossing helper from an initial writable frame.
    All four stores are constructed; no successful helper execution is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_frame_spec C.jet_spec.
Require Import C.jet_crossing_word C.jet_crossing_byte C.jet_write8_crossing_general.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Theorem eval_write8_crossing_frame m bd bw k x :
  1 <= k <= 7 ->
  write_frame m bd bw 0 (64 + k) 8 ->
  exists mf high low,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f_simplicity_write8)
      [Vptr bd Ptrofs.zero; Vint x] E0 mf Vundef /\
    Mem.load Mint64 mf bw 8 = Some (Vlong high) /\
    Mem.load Mint64 mf bw 0 = Some (Vlong low) /\
    decode_word8 (crossing_byte k high low) =
      decode_word8 (Int64.repr (Int.unsigned x)) /\
    (forall old, Mem.load Mint64 m bw 8 = Some (Vlong old) ->
      word_outside_eq 0 k high old) /\
    Mem.load Mint64 mf bd 8 = Some (Vlong (Int64.repr (56 + k))) /\
    loads_outside_blocks m mf bd bw.
Proof.
  intros HK HFrame.
  destruct (crossing_frame_words m bd bw k HK HFrame)
    as [[HE HO] [HDw [PD [PH [PW [oldhigh [oldlow [HH HW]]]]]]]].
  destruct (Mem.valid_access_store m Mint64 bw 8 (Vlong (crossing_high k oldhigh x)) PH)
    as [mh SH].
  assert (PDh : Mem.valid_access mh Mint64 bd 8 Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mh Mint64 bd 8 (Vlong (Int64.repr 64)) PDh)
    as [mo SO].
  assert (PWo : Mem.valid_access mo Mint64 bw 0 Writable)
    by (eauto using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mo Mint64 bw 0 (Vlong (crossing_low k x)) PWo)
    as [mw SW].
  assert (PDw : Mem.valid_access mw Mint64 bd 8 Writable)
    by (eauto using Mem.store_valid_access_1).
  destruct (Mem.valid_access_store mw Mint64 bd 8 (Vlong (Int64.repr (56 + k))) PDw)
    as [mf SF].
  exists mf, (crossing_high k oldhigh x), (crossing_low k x).
  split.
  - eapply eval_write8_crossing; eauto.
  - split.
    + erewrite Mem.load_store_other; [|exact SF|auto].
      erewrite Mem.load_store_other; [|exact SW|right; right; cbn; lia].
      erewrite Mem.load_store_other; [|exact SO|auto].
      exact (Mem.load_store_same _ _ _ _ _ _ SH).
    + split.
      * erewrite Mem.load_store_other; [|exact SF|auto].
        exact (Mem.load_store_same _ _ _ _ _ _ SW).
      * split; [apply crossing_byte_decode; exact HK |].
        split.
        -- intros old HH'. assert (old = oldhigh) by congruence. subst old.
           apply crossing_high_prefix; exact HK.
        -- split.
           ++ exact (Mem.load_store_same _ _ _ _ _ _ SF).
           ++ intros chunk b ofs HV Hbd Hbw.
              erewrite Mem.load_store_other; [|exact SF|auto].
              erewrite Mem.load_store_other; [|exact SW|auto].
              erewrite Mem.load_store_other; [|exact SO|auto].
              eapply Mem.load_store_other; [exact SH|auto].
Qed.
