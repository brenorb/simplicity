(** Width-generic reader memory proof. The execution kernels below are
    parameters discharged by each concrete generated reader, not axioms. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Events Memory.
Require Import C.jets C.jet_exec C.jet_frame_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.

Section READER.
Variables (n : Z) (f : function).
Variables (non_crossing : Z -> int64 -> int64) (crossing : Z -> int64 -> int64 -> int64).

Definition reader_layout_value (cursor : Z) (high low : int64) : int64 :=
  if Z_le_dec (cursor mod 64) (64 - n)
  then non_crossing cursor high else crossing cursor high low.

Hypothesis kernel_non_crossing : forall m mf bf base bw edge cursor high ,
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - n ->
  cursor mod 64 <= 64 - n ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + n))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f)
    [Vptr bf (Ptrofs.repr base)] E0 mf
    (Vlong (non_crossing cursor high)).

Hypothesis kernel_crossing : forall m mfirst mf bf base bw edge cursor high low ,
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - n ->
  64 - n < cursor mod 64 < 64 ->
  8 * (2 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low) ->
  bf <> bw ->
  Mem.store Mint64 m bf (base + 8)
    (Vlong (Int64.repr (cursor + (64 - cursor mod 64)))) = Some mfirst ->
  Mem.store Mint64 mfirst bf (base + 8)
    (Vlong (Int64.repr (cursor + n))) = Some mf ->
  ClightBigstep.Clight2.eval_funcall ge0 m (Internal f)
    [Vptr bf (Ptrofs.repr base)] E0 mf
    (Vlong (crossing cursor high low)).

Theorem eval_reader_layout_total m bf base bw edge cursor high low :
  frame_base_valid base ->
  0 <= cursor <= Int64.max_unsigned - n ->
  8 * (1 + cursor / 64) <= edge <= Ptrofs.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.load Mint64 m bw (edge - 8 * (1 + cursor / 64)) = Some (Vlong high) ->
  (64 - n < cursor mod 64 ->
    8 * (2 + cursor / 64) <= edge /\
    Mem.load Mint64 m bw (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)) ->
  Mem.valid_access m Mint64 bf (base + 8) Writable -> bf <> bw ->
  exists mf,
    ClightBigstep.Clight2.eval_funcall ge0 m (Internal f)
      [Vptr bf (Ptrofs.repr base)] E0 mf
      (Vlong (reader_layout_value cursor high low)) /\
    frame_fields_at mf bf base bw edge (cursor + n) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HE HF HH HLow PW HD.
  destruct HF as [HFedge HFcursor].
  assert (HM : 0 <= cursor mod 64 < 64) by (apply Z.mod_pos_bound; lia).
  unfold reader_layout_value.
  destruct (Z_le_dec (cursor mod 64) (64 - n)) as [HN|HX].
  - destruct (Mem.valid_access_store m Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor + n))) PW) as [mf SF].
    exists mf. split.
    + exact (kernel_non_crossing m mf bf base bw edge cursor high
        HB HC HN HE (conj HFedge HFcursor) HH SF).
    + split.
      * unfold frame_fields_at; split.
        -- transitivity (Mem.load Mptr m bf base).
           ++ eapply Mem.load_store_other; [exact SF|].
              right; left; change (base + 8 <= base + 8); lia.
           ++ exact HFedge.
        -- exact (Mem.load_store_same _ _ _ _ _ _ SF).
      * split.
        -- intros chunk b ofs Hsep. eapply Mem.load_store_other; [exact SF|].
           change (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 8 + 8 <= ofs).
           tauto || lia.
        -- split.
           ++ intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
           ++ intros b HV. eapply Mem.store_valid_block_1; eauto.
  - assert (Hcross : 64 - n < cursor mod 64 < 64) by lia.
    destruct (HLow ltac:(lia)) as [HE2 HL].
    set (k := 64 - cursor mod 64).
    assert (HK : 1 <= k <= 64) by (unfold k; lia).
    assert (Hedge2 : 8 * (2 + cursor / 64) <= edge) by lia.
    destruct (Mem.valid_access_store m Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor + k))) PW) as [mfirst SF].
    assert (PWfirst : Mem.valid_access mfirst Mint64 bf (base + 8) Writable)
      by (eapply Mem.store_valid_access_1; eauto).
    destruct (Mem.valid_access_store mfirst Mint64 bf (base + 8)
        (Vlong (Int64.repr (cursor + n))) PWfirst) as [mf SFinal].
    assert (HLfirst : Mem.load Mint64 mfirst bw
        (edge - 8 * (2 + cursor / 64)) = Some (Vlong low)).
    { erewrite Mem.load_store_other; [exact HL|exact SF|]. left; congruence. }
    assert (HFfirst : frame_fields_at mfirst bf base bw edge (cursor + k)).
    { split.
      - transitivity (Mem.load Mptr m bf base).
        + eapply Mem.load_store_other; [exact SF|].
          right; left; change (base + 8 <= base + 8); lia.
        + exact HFedge.
      - exact (Mem.load_store_same _ _ _ _ _ _ SF). }
    exists mf. split.
    + exact (kernel_crossing m mfirst mf bf base bw edge cursor high low
        HB HC Hcross (conj Hedge2 (proj2 HE)) (conj HFedge HFcursor)
        HH HL HD SF SFinal).
    + split.
      * unfold frame_fields_at; split.
        -- transitivity (Mem.load Mptr mfirst bf base).
           ++ eapply Mem.load_store_other; [exact SFinal|].
              right; left; change (base + 8 <= base + 8); lia.
           ++ transitivity (Mem.load Mptr m bf base).
              ** eapply Mem.load_store_other; [exact SF|].
                 right; left; change (base + 8 <= base + 8); lia.
              ** exact HFedge.
        -- exact (Mem.load_store_same _ _ _ _ _ _ SFinal).
      * split.
        -- intros chunk b ofs Hsep.
           assert (Hsep' : b <> bf \/ ofs + size_chunk chunk <= base + 8 \/
               base + 8 + 8 <= ofs) by lia.
           erewrite Mem.load_store_other; [|exact SFinal|exact Hsep'].
           eapply Mem.load_store_other; eauto.
        -- split.
           ++ intros b ofs kind p HP. eauto using Mem.perm_store_1.
           ++ intros b HV. eauto using Mem.store_valid_block_1.
Qed.

End READER.
