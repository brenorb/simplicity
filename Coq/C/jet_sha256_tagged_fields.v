(** Actual tagged SHA context initialization with counter 64. The existing
    byte-store execution is reused, including all 64 block-initializer writes. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Maps ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_sha256_context_fields C.jet_sha256_init_zero_exec C.jet_sha256_init_fields_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition sha_ctx_counter64_stmt := Sassign (sha_ctx_local_field CtxCounter) (Econst_int (Int.repr 64) tint).
Definition sha_ctx_tagged_fields_stmt := Ssequence
 (sha_ctx_zero_prefix (Ssequence sha_ctx_output_stmt sha_ctx_counter64_stmt) 64) sha_ctx_overflow_stmt.

Lemma exec_sha_ctx_counter64_store e le m mf bc :
  e!___compound = Some (bc,Tstruct _sha256_context noattr) ->
  Mem.store Mint64 m bc 8 (Vlong (Int64.repr 64)) = Some mf ->
  Clight2.exec_stmt ge0 e le m sha_ctx_counter64_stmt E0 le mf Out_normal.
Proof.
  intros HE HS. eapply exec_Sassign_value with (v := Vlong (Int64.repr 64)) (v2 := Vint (Int.repr 64))
    (b := bc) (ofs := Ptrofs.repr 8).
  - apply eval_sha_ctx_local_field; exact HE.
  - apply eval_Econst_int.
  - reflexivity.
  - apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HS].
Qed.
Theorem exec_sha_ctx_tagged_fields_layout e le m bc bi input :
  e!___compound = Some (bc,Tstruct _sha256_context noattr) -> le!_output = Some (Vptr bi input) ->
  Mem.range_perm m bc 0 88 Cur Writable ->
  exists mf,
    Clight2.exec_stmt ge0 e le m sha_ctx_tagged_fields_stmt E0 le mf Out_normal /\
    Mem.load Mptr mf bc 0 = Some (Vptr bi input) /\
    Mem.load Mint64 mf bc 8 = Some (Vlong (Int64.repr 64)) /\
    Mem.load Mint8unsigned mf bc 80 = Some (Vint Int.zero) /\
    (forall chunk b ofs, b <> bc \/ ofs + size_chunk chunk <= 0 \/ 88 <= ofs ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HE HO HR.
  assert (HW0 : Mem.valid_access m Mptr bc 0 Writable).
  { split; [intros ofs H; apply HR; change (size_chunk Mptr) with 8 in H; lia|].
    change (8 | 0); exists 0; reflexivity. }
  destruct (Mem.valid_access_store m Mptr bc 0 (Vptr bi input) HW0) as (mo & SO).
  assert (HW8 : Mem.valid_access mo Mint64 bc 8 Writable).
  { split; [intros ofs H; eapply Mem.perm_store_1; [exact SO|apply HR]; change (size_chunk Mint64) with 8 in H; lia|].
    change (8 | 8); exists 1; reflexivity. }
  destruct (Mem.valid_access_store mo Mint64 bc 8 (Vlong (Int64.repr 64)) HW8) as (mc & SC).
  assert (HHead : Clight2.exec_stmt ge0 e le m (Ssequence sha_ctx_output_stmt sha_ctx_counter64_stmt) E0 le mc Out_normal).
  { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mo);
      [eapply exec_sha_ctx_output_store; eauto|eapply exec_sha_ctx_counter64_store; eauto]. }
  assert (HRc : Mem.range_perm mc bc 16 80 Cur Writable).
  { intros ofs H. eapply Mem.perm_store_1; [exact SC|]. eapply Mem.perm_store_1; [exact SO|apply HR; lia]. }
  destruct (exec_sha_ctx_zero_prefix (Ssequence sha_ctx_output_stmt sha_ctx_counter64_stmt) 64 e le m mc bc
    ltac:(lia) HE HHead HRc) as (mz & HZero & HLoads & HPerm & HValid).
  assert (HW80 : Mem.valid_access mz Mint8unsigned bc 80 Writable).
  { split; [intros ofs H; apply HPerm; eapply Mem.perm_store_1; [exact SC|];
      eapply Mem.perm_store_1; [exact SO|apply HR]; change (size_chunk Mint8unsigned) with 1 in H; lia|].
    change (1 | 80); exists 80; reflexivity. }
  destruct (Mem.valid_access_store mz Mint8unsigned bc 80 (Vint Int.zero) HW80) as (mf & SF).
  exists mf. split.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mz);
      [exact HZero|eapply exec_sha_ctx_overflow_store; eauto].
  - split.
    + erewrite Mem.load_store_other; [|exact SF|right; left; change (8 <= 80); lia].
      rewrite HLoads by (right; left; change (8 <= 16); lia).
      erewrite Mem.load_store_other; [exact (Mem.load_store_same _ _ _ _ _ _ SO)|exact SC|right; left; reflexivity].
    + split.
      * erewrite Mem.load_store_other; [|exact SF|right; left; change (16 <= 80); lia].
        rewrite HLoads by (right; left; reflexivity). exact (Mem.load_store_same _ _ _ _ _ _ SC).
      * split; [exact (Mem.load_store_same _ _ _ _ _ _ SF)|]. split.
        -- intros chunk b ofs HX.
           erewrite Mem.load_store_other; [|exact SF|change (b <> bc \/ ofs + size_chunk chunk <= 80 \/ 81 <= ofs); lia].
           rewrite HLoads by (change (b <> bc \/ ofs + size_chunk chunk <= 16 \/ 80 <= ofs); lia).
           erewrite Mem.load_store_other; [|exact SC|change (b <> bc \/ ofs + size_chunk chunk <= 8 \/ 16 <= ofs); lia].
           eapply Mem.load_store_other; [exact SO|change (b <> bc \/ ofs + size_chunk chunk <= 0 \/ 8 <= ofs); lia].
        -- split.
           ++ intros b ofs kind p H. eapply Mem.perm_store_1; [exact SF|apply HPerm].
              eapply Mem.perm_store_1; [exact SC|]. eapply Mem.perm_store_1; eauto.
           ++ intros b H. eapply Mem.store_valid_block_1; [exact SF|apply HValid].
              eapply Mem.store_valid_block_1; [exact SC|]. eapply Mem.store_valid_block_1; eauto.
Qed.
