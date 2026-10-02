(** Actual forwardBits, with a non-wrapping cursor and complete store framing.
    This is shared infrastructure for rightmost/padding/shifting jets, not
    additional public jet coverage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition forwardBits_env bf base n :=
  PTree.set _n (Vlong (Int64.repr n))
    (PTree.set _frame (Vptr bf (Ptrofs.repr base)) (create_undef_temps f_forwardBits.(fn_temps))).
Lemma forwardBits_entry m bf base n :
  function_entry2 ge0 f_forwardBits [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr n)]
    m empty_env (forwardBits_env bf base n) m.
Proof.
  constructor.
  - constructor.
  - constructor.
    + cbn. intros [H|H]; [vm_compute in H; discriminate|contradiction].
    + constructor; [cbn; tauto|constructor].
  - intros id1 id2 H1 H2 Heq. cbn in H1, H2. subst id2.
    repeat match goal with H : _ \/ _ |- _ => destruct H end.
    all: vm_compute in *; congruence.
  - constructor.
  - reflexivity.
Qed.
Lemma eval_forwardBits_layout_raw m mf bf base cursor n :
  frame_base_valid base -> 0 <= cursor -> 0 <= n -> cursor + n <= Int64.max_unsigned ->
  Mem.load Mint64 m bf (base + 8) = Some (Vlong (Int64.repr cursor)) ->
  Mem.store Mint64 m bf (base + 8) (Vlong (Int64.repr (cursor + n))) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_forwardBits)
    [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr n)] E0 mf Vundef.
Proof.
  intros HB HC HN Hmax HO SF.
  assert (HAdd : Int64.add (Int64.repr cursor) (Int64.repr n) = Int64.repr (cursor + n)).
  { unfold Int64.add. rewrite !Int64.unsigned_repr by lia. reflexivity. }
  eapply eval_funcall_internal with (e := empty_env) (le1 := forwardBits_env bf base n)
    (le2 := PTree.set _t'1 (Vlong (Int64.repr cursor)) (forwardBits_env bf base n))
    (m1 := m) (m2 := mf) (out := Out_normal).
  - apply forwardBits_entry.
  - unfold f_forwardBits; cbn [fn_body].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m).
    + apply exec_set with (v := Vlong (Int64.repr cursor)).
      eapply eval_frame_offset_at; [exact HB|reflexivity|exact HO].
    + eapply exec_Sassign_value with (v := Vlong (Int64.repr (cursor + n)))
        (v2 := Vlong (Int64.repr (cursor + n))).
      * apply eval_frame_offset_lvalue_at; reflexivity.
      * eapply eval_Ebinop with (v1 := Vlong (Int64.repr cursor)) (v2 := Vlong (Int64.repr n)).
        -- apply eval_Etempvar; reflexivity.
        -- apply eval_Etempvar; reflexivity.
        -- change (Some (Vlong (Int64.add (Int64.repr cursor) (Int64.repr n))) =
             Some (Vlong (Int64.repr (cursor + n)))). rewrite HAdd. reflexivity.
      * reflexivity.
      * eapply assign_frame_offset_at; eauto.
  - reflexivity.
  - reflexivity.
Qed.
Theorem eval_forwardBits_layout m bf base bi edge cursor n :
  frame_base_valid base -> 0 <= cursor -> 0 <= n -> cursor + n <= Int64.max_unsigned ->
  frame_fields_at m bf base bi edge cursor ->
  Mem.valid_access m Mint64 bf (base + 8) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_forwardBits)
      [Vptr bf (Ptrofs.repr base); Vlong (Int64.repr n)] E0 mf Vundef /\
    frame_fields_at mf bf base bi edge (cursor + n) /\
    (forall chunk b ofs, b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HB HC HN Hmax [HF HO] PW.
  destruct (Mem.valid_access_store m Mint64 bf (base + 8) (Vlong (Int64.repr (cursor + n))) PW)
    as [mf SF].
  exists mf. split.
  - eapply eval_forwardBits_layout_raw with (cursor := cursor); eauto.
  - split.
    + split.
      * erewrite Mem.load_store_other; [exact HF|exact SF|].
        right; left; change (base + 8 <= base + 8); lia.
      * exact (Mem.load_store_same _ _ _ _ _ _ SF).
    + split.
      * intros chunk b ofs Hsep. eapply Mem.load_store_other; [exact SF|].
        change (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 8 + 8 <= ofs). lia.
      * split.
        -- intros b ofs kind p HP. eapply Mem.perm_store_1; eauto.
        -- intros b HV. eapply Mem.store_valid_block_1; eauto.
Qed.
