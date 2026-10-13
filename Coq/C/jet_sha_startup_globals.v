(** Persistent SHA global state against the current frame predicates.

    The definitions and proofs below are those of the archived startup
    sources [jet_sha_global_frame] and [jet_sha_persistent_globals]
    (proof-work/sha-support, unaccepted), restated here because the archived
    [jet_sha_global_frame] was written for an earlier shape of
    [write_frame_at] and no longer compiles at this revision.  The only change
    is the destructuring pattern in [sha_write_frame_global_separation]; the
    statements are unchanged.  The remaining prerequisites
    ([jet_clight_forward], [jet_sha_initial_globals]) are used as archived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Globalenvs Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local.
Require Import C.jet_sha_uchars_exec C.jet_sha_add_n_exec.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_clight_forward C.jet_sha_initial_globals.
Import Values Mem ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma sha_counter_writable_cell_other m b ofs :
  sha_original_global_state m ->
  Mem.valid_access m Mint64 b ofs Writable ->
  b <> sha_symbol_block _sha256_max_counter.
Proof.
  intros [_ [HNoWrite _]] HAccess HSame; subst b.
  apply (HNoWrite ofs).
  exact (Mem.valid_access_perm m Mint64 _ ofs Cur Writable HAccess).
Qed.

Theorem sha_write_frame_global_separation m bf base bw edge cursor count :
  sha_original_global_state m -> 0 < count ->
  write_frame_at m bf base bw edge cursor count ->
  bf <> sha_symbol_block _simplicity_sha256_compression /\
  bw <> sha_symbol_block _simplicity_sha256_compression /\
  bf <> sha_symbol_block _sha256_max_counter /\
  bw <> sha_symbol_block _sha256_max_counter.
Proof.
  intros HState HCount HFrame.
  pose proof HFrame as [HBase [_ [_ [_ [_ [HCursor _]]]]]].
  destruct (write_frame_at_head m bf base bw edge cursor count HCount HFrame)
    as [_ [_ [HWordAccess [old HWordLoad]]]].
  split.
  - eapply sha_dispatch_frame_cursor_other; [exact HState|exact (proj1 HBase)|exact HCursor].
  - split.
    + eapply sha_dispatch_long_cell_other; eassumption.
    + split; eapply sha_counter_writable_cell_other; eassumption.
Qed.

Theorem sha_globals_from_public_frame_observations m mf bf base bw edge cursor count :
  sha_original_global_state m -> 0 < count ->
  write_frame_at m bf base bw edge cursor count ->
  (forall chunk b ofs, Mem.valid_block m b ->
    (b <> bf \/ ofs + size_chunk chunk <= base + 8 \/ base + 16 <= ofs) ->
    (b <> bw \/ ofs + size_chunk chunk <= edge + 8 * ((cursor - count) / 64) \/
      write_word_address edge cursor + 8 <= ofs) ->
    Mem.load chunk mf b ofs = Mem.load chunk m b ofs) ->
  sha_globals_ok mf.
Proof.
  intros HState HCount HFrame HLoads.
  destruct (sha_write_frame_global_separation m bf base bw edge cursor count
    HState HCount HFrame) as [HFD [HWD [HFC HWC]]].
  destruct HState as [[HDispatch HCounter] _].
  split.
  - unfold sha_dispatch_ok in *.
    rewrite HLoads; [exact HDispatch| |left; congruence|left; congruence].
    eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Readable).
    eapply (Mem.valid_access_perm m Mptr _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HDispatch.
  - rewrite HLoads; [exact HCounter| |left; congruence|left; congruence].
    eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Readable).
    eapply (Mem.valid_access_perm m Mint64 _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HCounter.
Qed.

Definition sha_persistent_global_state (m : mem) : Prop :=
  sha_globals_ok m /\
  (forall ofs, ~ Mem.perm m (sha_symbol_block _sha256_max_counter) ofs Max Writable) /\
  (forall ofs p, Mem.perm m (sha_symbol_block _simplicity_sha256_compression) ofs Max p ->
    0 <= ofs < 8).

Theorem sha_persistent_globals_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_persistent_global_state m.
Proof.
  intro HInit.
  pose proof (sha_original_global_state_initialized m HInit) as [HGlobals [_ HBounds]].
  split; [exact HGlobals|]; split.
  - intros ofs HP.
    destruct (Genv.init_mem_characterization jets_sha.prog
      (sha_symbol_block _sha256_max_counter) sha_counter_var_info HInit)
      as [_ [HOnly _]].
    destruct (HOnly ofs Max Writable HP) as [_ HOrder].
    change (perm_order Readable Writable) in HOrder; inversion HOrder.
  - intros; eapply HBounds; eassumption.
Qed.

Lemma sha_persistent_globals_original m :
  sha_persistent_global_state m -> sha_original_global_state m.
Proof.
  intros [HGlobals [HNoWrite HBounds]]; split; [exact HGlobals|]; split.
  - intros ofs HP; apply (HNoWrite ofs); apply Mem.perm_cur_max; exact HP.
  - intros ofs k p HP; apply (HBounds ofs p); eapply Mem.perm_max; exact HP.
Qed.

Theorem sha_persistent_globals_forward m mf :
  sha_persistent_global_state m -> mem_forward m mf ->
  sha_globals_ok mf -> sha_persistent_global_state mf.
Proof.
  intros [[HD HC] [HNoWrite HBounds]] HForward HFinal.
  assert (HVD : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression)).
  { eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Readable).
    eapply (Mem.valid_access_perm m Mptr _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HD. }
  assert (HVC : Mem.valid_block m (sha_symbol_block _sha256_max_counter)).
  { eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Readable).
    eapply (Mem.valid_access_perm m Mint64 _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HC. }
  split; [exact HFinal|]; split.
  - intros ofs HP; apply (HNoWrite ofs).
    exact (proj2 (HForward _ HVC) ofs Writable HP).
  - intros ofs p HP; apply (HBounds ofs p).
    exact (proj2 (HForward _ HVD) ofs p HP).
Qed.
