(** Actual private length local of read_sha256_context, including allocation
    provenance, function entry and cleanup. No caller frame is copied here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_sha256_max_counter.
Require Import C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha256_read_env bl : env := PTree.set _len (bl,tulong) empty_env.
Definition sha256_read_temps bc cbase bf base : temp_env :=
  PTree.set _src (Vptr bf (Ptrofs.repr base))
    (PTree.set _ctx (Vptr bc (Ptrofs.repr cbase))
      (create_undef_temps (fn_temps f_simplicity_read_sha256_context))).

Lemma sha256_read_local_entry m ma bl bc cbase bf base :
  Mem.alloc m 0 8 = (ma,bl) ->
  function_entry2 ge0 f_simplicity_read_sha256_context
    [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] m
    (sha256_read_env bl) (sha256_read_temps bc cbase bf base) ma.
Proof.
  intro HA. constructor.
  - change (list_norepet [_len]); repeat constructor; simpl; tauto.
  - change (list_norepet [_ctx; _src]); vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]); constructor.
  - change (list_disjoint [_ctx; _src] [_compressionCount; _t'1; _t'5; _t'4; _t'3; _t'2]).
    vm_compute; intuition congruence.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 8 = (ma,bl)); exact HA.
    + constructor.
  - reflexivity.
Qed.

Theorem allocate_sha256_read_local m bc cbase bf base :
  sha256_max_counter_at m ->
  exists ma bl,
    Mem.alloc m 0 8 = (ma,bl) /\
    function_entry2 ge0 f_simplicity_read_sha256_context
      [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] m
      (sha256_read_env bl) (sha256_read_temps bc cbase bf base) ma /\
    Mem.range_perm ma bl 0 8 Cur Freeable /\
    Mem.valid_access ma Mint64 bl 0 Writable /\
    (forall b, Mem.valid_block m b -> b <> bl) /\
    (forall chunk b ofs, Mem.valid_block m b -> Mem.load chunk ma b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm ma b ofs kind p) /\
    sha256_max_counter_at ma.
Proof.
  intro HGlobal. destruct (Mem.alloc m 0 8) as [ma bl] eqn:HA.
  assert (HP : Mem.range_perm ma bl 0 8 Cur Freeable).
  { intros ofs HR. eapply Mem.perm_alloc_2; eauto. }
  exists ma, bl. split; [reflexivity|]. split; [apply sha256_read_local_entry; exact HA|].
  split; [exact HP|]. split.
  - split.
    + intros ofs HR. eapply Mem.perm_implies; [apply HP; exact HR|constructor].
    + exists 0; reflexivity.
  - split.
    + intros b HV Heq; subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ HA HV).
    + split.
      * intros chunk b ofs HV. eapply Mem.load_alloc_unchanged; eauto.
      * split; [intros; eapply Mem.perm_alloc_1; eauto|].
        exact (proj1 (sha256_max_counter_alloc _ _ _ _ _ HGlobal HA)).
Qed.

Lemma sha256_read_local_blocks bl : blocks_of_env ge0 (sha256_read_env bl) = [(bl,0,8)].
Proof. reflexivity. Qed.

Theorem free_sha256_read_local m bl :
  Mem.range_perm m bl 0 8 Cur Freeable ->
  exists mf,
    Mem.free_list m (blocks_of_env ge0 (sha256_read_env bl)) = Some mf /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, b <> bl -> Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intro HP. destruct (Mem.range_perm_free m bl 0 8 HP) as [mf HF].
  exists mf. split.
  - rewrite sha256_read_local_blocks. cbn [Mem.free_list]. rewrite HF; reflexivity.
  - split.
    + intros chunk b ofs HOther. eapply Mem.load_free; [exact HF|left; exact HOther].
    + split.
      * intros b ofs kind p HOther HPerm. eapply Mem.perm_free_1; [exact HF|left; exact HOther|exact HPerm].
      * exact (Mem.nextblock_free _ _ _ _ _ HF).
Qed.

(** Internal function-boundary adapter. Whole-reader consumers must derive
    the body execution and preservation of the local's Freeable permissions. *)
Theorem eval_sha256_read_context_from_body m ma mb bl bc cbase bf base le overflow :
  Mem.alloc m 0 8 = (ma,bl) ->
  Clight2.exec_stmt ge0 (sha256_read_env bl) (sha256_read_temps bc cbase bf base)
    ma (fn_body f_simplicity_read_sha256_context) E0 le mb
    (Out_return (Some (Vint (bit_int (negb overflow)), tint))) ->
  Mem.range_perm mb bl 0 8 Cur Freeable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_simplicity_read_sha256_context)
      [Vptr bc (Ptrofs.repr cbase); Vptr bf (Ptrofs.repr base)] E0 mf
      (Vint (bit_int (negb overflow))) /\
    Mem.free_list mb (blocks_of_env ge0 (sha256_read_env bl)) = Some mf /\
    (forall chunk b ofs, b <> bl -> Mem.load chunk mf b ofs = Mem.load chunk mb b ofs) /\
    (forall b ofs kind p, b <> bl -> Mem.perm mb b ofs kind p -> Mem.perm mf b ofs kind p) /\
    Mem.nextblock mf = Mem.nextblock mb.
Proof.
  intros HA HBody HFree.
  destruct (free_sha256_read_local mb bl HFree) as (mf & HF & HLoads & HPerms & HNext).
  exists mf. split; [|auto].
  eapply eval_funcall_internal with (e := sha256_read_env bl)
    (le1 := sha256_read_temps bc cbase bf base) (le2 := le)
    (m1 := ma) (m2 := mb)
    (out := Out_return (Some (Vint (bit_int (negb overflow)), tint))).
  - apply sha256_read_local_entry; exact HA.
  - exact HBody.
  - cbn; split; [discriminate|destruct overflow; reflexivity].
  - exact HF.
Qed.
