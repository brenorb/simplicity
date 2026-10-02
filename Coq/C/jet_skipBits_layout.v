(** The actual generated skipBits helper.  It advances only the frame cursor;
    skipped cells retain arbitrary old contents.  All final contracts below
    derive execution and the store from initial memory facts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_write_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition skip_frame_env bf base n :=
  PTree.set _n (Vlong (Int64.repr n))
    (PTree.set _frame (Vptr bf (Ptrofs.repr base))
      (create_undef_temps f_skipBits.(fn_temps))).

Lemma skipBits_entry m bf base n :
  function_entry2 ge0 f_skipBits
    [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr n)]
    m empty_env (skip_frame_env bf base n) m.
Proof.
  constructor.
  - constructor.
  - change (list_norepet [_frame; _n]).
    unfold _frame, _n. repeat constructor; simpl; intuition discriminate.
  - change (list_disjoint [_frame; _n] [_t'2; _t'1]).
    intros i j HI HJ Heq; cbn in HI, HJ; subst j.
    repeat match goal with H : _ \/ _ |- _ => destruct H end;
      try contradiction; vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.

(** Padding cells require physical storage, but prescribe no value for it. *)
Lemma write_frame_padding_cells m bf base bw edge cursor count :
  write_frame_at m bf base bw edge cursor (Z.of_nat count) ->
  frame_output_cells_at m bw edge cursor (repeat None count).
Proof.
  intros [HB [HF [HE [HC [HM [HD [PW HW]]]]]]] i c Hi.
  change (nth_error (repeat (@None bool) count) i = Some c) in Hi.
  assert (HI : (i < count)%nat).
  { assert (HH : nth_error (repeat (@None bool) count) i <> None).
    { rewrite Hi; discriminate. }
    apply nth_error_Some in HH. rewrite repeat_length in HH. exact HH. }
  rewrite nth_error_repeat in Hi by exact HI. injection Hi as <-.
  destruct (HW (Z.of_nat i) ltac:(lia)) as [_ [_ [_ [w HL]]]].
  cbn [cell_matches]. exists (Int64.testbit w ((cursor - 1 - Z.of_nat i) mod 64)).
  split; [lia|]. exists w. split; [exact HL|reflexivity].
Qed.

(** Internal adapter for a specified cursor store; [eval_skipBits_layout]
    below proves that this store exists from writable initial permissions. *)
Lemma eval_skipBits_store m mf bf base cursor n :
  frame_base_valid base -> 0 <= n <= cursor -> cursor <= Int64.max_unsigned ->
  Mem.load Mint64 m bf (base + 8) = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor - n))) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_skipBits)
    [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr n)] E0 mf Vundef.
Proof.
  intros HB HN HM HO SF.
  set (le := skip_frame_env bf base n).
  assert (Hsub : Int64.sub (Int64.repr cursor) (Int64.repr n) =
    Int64.repr (cursor - n)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr by lia. reflexivity. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := le)
    (le2 := PTree.set _t'1 (Vlong (Int64.repr cursor)) le)
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply skipBits_entry.
  - unfold f_skipBits; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
    + eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0)
        (le1 := le) (m1 := m) (out1 := Out_normal) (out2 := Out_break).
      * eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := Datatypes.false).
        -- eapply eval_Eunop with (v1 := Vint Int.one).
           ++ apply eval_Econst_int.
           ++ reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
      * constructor.
      * apply exec_Sbreak.
      * constructor.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := PTree.set _t'1 (Vlong (Int64.repr cursor)) le).
      * apply exec_set. apply (eval_frame_offset_at m le bf base);
          [exact HB|reflexivity|exact HO].
      * eapply exec_Sassign_value with (v := Vlong (Int64.repr (cursor - n)))
          (v2 := Vlong (Int64.repr (cursor - n))).
        -- apply eval_frame_offset_lvalue_at; reflexivity.
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr cursor))
             (v2 := Vlong (Int64.repr n)).
           ++ apply eval_Etempvar; reflexivity.
           ++ apply eval_Etempvar; reflexivity.
           ++ change (Some (Vlong (Int64.sub (Int64.repr cursor) (Int64.repr n))) =
                Some (Vlong (Int64.repr (cursor - n)))). rewrite Hsub; reflexivity.
        -- reflexivity.
        -- apply assign_frame_offset_at; assumption.
  - reflexivity.
  - reflexivity.
Qed.

Theorem eval_skipBits_layout m bf base bw edge cursor n :
  frame_base_valid base -> 0 <= n <= cursor -> cursor <= Int64.max_unsigned ->
  frame_fields_at m bf base bw edge cursor ->
  Mem.valid_access m Mint64 bf (base + 8) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_skipBits)
      [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_fields_at mf bf base bw edge (cursor - n) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HN HM [HE HO] PW.
  destruct (Mem.valid_access_store m Mint64 bf (base + 8)
    (Vlong (Int64.repr (cursor - n))) PW) as [mf SF].
  exists mf. split.
  - eapply eval_skipBits_store; eauto.
  - split.
    + split.
      * erewrite Mem.load_store_other; [exact HE|exact SF|].
        right; left; change (base + 8 <= base + 8); lia.
      * exact (Mem.load_store_same _ _ _ _ _ _ SF).
    + split.
      * intros chunk b ofs Hsep. eapply Mem.load_store_other; [exact SF|].
        change (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 8 + 8 <= ofs). lia.
      * split.
        -- intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
        -- intros b HV. eapply Mem.store_valid_block_1; eauto.
Qed.

Theorem eval_skipBits_padding m bf base bw edge cursor count :
  write_frame_at m bf base bw edge cursor (Z.of_nat count) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_skipBits)
      [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr (Z.of_nat count))] E0 mf Vundef /\
    frame_output_cells_at mf bw edge cursor (repeat None count) /\
    write_prefix_at m mf bw edge cursor /\
    frame_fields_at mf bf base bw edge (cursor - Z.of_nat count) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HW. pose proof HW as [HB [HF [HE [HC [HM [HD [PW Hwords]]]]]]].
  destruct (eval_skipBits_layout m bf base bw edge cursor (Z.of_nat count)
    HB HC HM HF PW) as [mf [Hcall [Hfields [Hloads [Hperm Hvalid]]]]].
  exists mf. split; [exact Hcall|]. split.
  - pose proof (write_frame_padding_cells m bf base bw edge cursor count HW) as HP.
    intros i c Hi. specialize (HP i c Hi).
    assert (HBITS : forall q bit, frame_output_bit_at m bw edge q bit ->
      frame_output_bit_at mf bw edge q bit).
    { intros q bit [HQ [w [HL HX]]]. split; [exact HQ|]. exists w. split; [|exact HX].
      rewrite Hloads by (left; congruence). exact HL. }
    destruct c as [bit|]; cbn [cell_matches] in *.
    + apply HBITS; exact HP.
    + destruct HP as [bit HP]. exists bit. apply HBITS; exact HP.
  - split.
    + intros old HL. exists old. split.
      * rewrite Hloads by (left; congruence). exact HL.
      * intros i HI HO; reflexivity.
    + split; [exact Hfields|]. split; [exact Hloads|]. split; assumption.
Qed.
