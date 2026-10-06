(** Isolated continuation scratch: initial facts from the actual SHA AST.
    No repository proof sources or audit inputs are changed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Memory Globalenvs.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local.
Require Import C.jet_sha_uchars_exec C.jet_sha_add_n_exec C.jet_readonly_int64.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma scalar_pointer_global_initialized {F V} (p : AST.program F V)
    b info symbol target offset m readonly :
  Genv.find_var_info (Genv.globalenv p) b = Some
    {| gvar_info := info; gvar_init := [Init_addrof symbol offset];
       gvar_readonly := readonly; gvar_volatile := false |} ->
  Genv.find_symbol (Genv.globalenv p) symbol = Some target ->
  Genv.init_mem p = Some m ->
  Mem.load Mptr m b 0 = Some (Vptr target offset).
Proof.
  intros HInfo HSymbol HInit.
  destruct (Genv.init_mem_characterization p b HInfo HInit)
    as [_ [_ [HLoad _]]].
  destruct (proj1 (HLoad eq_refl)) as [actual [HSymbol' HLoad']].
  rewrite HSymbol in HSymbol'; inversion HSymbol'; subst actual.
  exact HLoad'.
Qed.

Lemma sha_dispatch_var_info :
  Genv.find_var_info (Genv.globalenv jets_sha.prog)
    (sha_symbol_block _simplicity_sha256_compression) =
    Some v_simplicity_sha256_compression.
Proof. vm_compute; reflexivity. Qed.

Lemma sha_counter_var_info :
  Genv.find_var_info (Genv.globalenv jets_sha.prog)
    (sha_symbol_block _sha256_max_counter) = Some v_sha256_max_counter.
Proof. vm_compute; reflexivity. Qed.

Local Opaque jets_sha.prog.

Lemma sha_compression_ast_symbol :
  Genv.find_symbol (Genv.globalenv jets_sha.prog) _sha256_compression_portable =
    Some (sha_symbol_block _sha256_compression_portable).
Proof.
  pose proof sha_compression_symbol as HSymbol.
  cbv beta iota zeta delta [sha_ge Clight.globalenv Clight.genv_genv] in HSymbol.
  exact HSymbol.
Time Qed.

Local Opaque sha_ge.

Theorem sha_dispatch_initialized_from_original_ast m :
  Genv.init_mem jets_sha.prog = Some m -> sha_dispatch_ok m.
Proof.
  intro HInit.
  exact (@scalar_pointer_global_initialized Clight.fundef type jets_sha.prog
    (sha_symbol_block _simplicity_sha256_compression)
    (gvar_info v_simplicity_sha256_compression)
    _sha256_compression_portable (sha_symbol_block _sha256_compression_portable)
    Ptrofs.zero m false sha_dispatch_var_info sha_compression_ast_symbol HInit).
Qed.

Theorem sha_globals_initialized_from_original_ast m :
  Genv.init_mem jets_sha.prog = Some m -> sha_globals_ok m.
Proof.
  intro HInit; split.
  - exact (sha_dispatch_initialized_from_original_ast m HInit).
  - exact (proj1 (@readonly_int64_global_initialized Clight.fundef type
      jets_sha.prog (sha_symbol_block _sha256_max_counter)
      (gvar_info v_sha256_max_counter) sha_max_counter m
      sha_counter_var_info HInit)).
Qed.

Lemma scalar_pointer_global_permissions {F V} (p : AST.program F V)
    b info symbol offset m readonly :
  Genv.find_var_info (Genv.globalenv p) b = Some
    {| gvar_info := info; gvar_init := [Init_addrof symbol offset];
       gvar_readonly := readonly; gvar_volatile := false |} ->
  Genv.init_mem p = Some m ->
  forall ofs k perm,
    Mem.perm m b ofs k perm -> 0 <= ofs < size_chunk Mptr.
Proof.
  intros HInfo HInit ofs k perm HP.
  destruct (Genv.init_mem_characterization p b HInfo HInit)
    as [_ [HOnly _]].
  pose proof (proj1 (HOnly ofs k perm HP)) as HBounds.
  change (0 <= ofs < init_data_size (Init_addrof symbol offset) + 0) in HBounds.
  rewrite Genv.init_data_size_addrof in HBounds.
  lia.
Qed.

Definition sha_original_global_state m : Prop :=
  sha_globals_ok m /\
  (forall ofs, ~ Mem.perm m (sha_symbol_block _sha256_max_counter) ofs Cur Writable) /\
  (forall ofs k perm,
    Mem.perm m (sha_symbol_block _simplicity_sha256_compression) ofs k perm ->
    0 <= ofs < 8).

Theorem sha_original_global_state_initialized m :
  Genv.init_mem jets_sha.prog = Some m -> sha_original_global_state m.
Proof.
  intro HInit; split.
  - exact (sha_globals_initialized_from_original_ast m HInit).
  - split.
    + exact (proj2 (@readonly_int64_global_initialized Clight.fundef type
        jets_sha.prog (sha_symbol_block _sha256_max_counter)
        (gvar_info v_sha256_max_counter) sha_max_counter m
        sha_counter_var_info HInit)).
    + intros ofs k perm HP.
      pose proof (@scalar_pointer_global_permissions Clight.fundef type
        jets_sha.prog (sha_symbol_block _simplicity_sha256_compression)
        (gvar_info v_simplicity_sha256_compression)
        _sha256_compression_portable Ptrofs.zero m false
        sha_dispatch_var_info HInit ofs k perm HP) as HBounds.
      exact HBounds.
Qed.

Lemma sha_dispatch_frame_cursor_other m b base :
  sha_original_global_state m -> 0 <= base ->
  Mem.valid_access m Mint64 b (base + 8) Writable ->
  b <> sha_symbol_block _simplicity_sha256_compression.
Proof.
  intros [_ [_ HBounds]] HBase HW HSame; subst b.
  pose proof (HBounds (base + 8) Cur Writable
    (Mem.valid_access_perm m Mint64 _ (base + 8) Cur Writable HW)) as HRange.
  lia.
Qed.

Lemma sha_dispatch_long_cell_other m b ofs old :
  sha_original_global_state m ->
  Mem.load Mint64 m b ofs = Some (Vlong old) ->
  Mem.valid_access m Mint64 b ofs Writable ->
  b <> sha_symbol_block _simplicity_sha256_compression.
Proof.
  intros [[HDispatch _] [_ HBounds]] HLoad [HRange HAlign] HSame; subst b.
  assert (HFirst : 0 <= ofs < 8).
  { apply (HBounds ofs Cur Writable); apply HRange; cbn; lia. }
  assert (HLast : 0 <= ofs + 7 < 8).
  { apply (HBounds (ofs + 7) Cur Writable); apply HRange; cbn; lia. }
  assert (HZero : ofs = 0) by lia; subst ofs.
  change (Mem.load Mint64 m (sha_symbol_block _simplicity_sha256_compression) 0 =
    Some (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero)) in HDispatch.
  rewrite HDispatch in HLoad; discriminate.
Qed.

Theorem sha_original_global_state_store m mf chunk b ofs value :
  sha_original_global_state m ->
  b <> sha_symbol_block _simplicity_sha256_compression ->
  Mem.store chunk m b ofs value = Some mf ->
  sha_original_global_state mf.
Proof.
  intros [[HD HC] [HNoWrite HBounds]] HOtherD HS.
  assert (HOtherC : b <> sha_symbol_block _sha256_max_counter).
  { intro HSame; subst b. apply (HNoWrite ofs).
    eapply Mem.valid_access_perm.
    eapply Mem.store_valid_access_3; exact HS. }
  split.
  - split.
    + unfold sha_dispatch_ok in *.
      erewrite Mem.load_store_other; [exact HD|exact HS|left; congruence].
    + erewrite Mem.load_store_other; [exact HC|exact HS|left; congruence].
  - split.
    + intros pos HP; apply (HNoWrite pos); eapply Mem.perm_store_2; eauto.
    + intros pos k perm HP; apply (HBounds pos k perm).
      eapply Mem.perm_store_2; eauto.
Qed.

Theorem sha_original_global_state_store_long_cell m mf b ofs old value :
  sha_original_global_state m ->
  Mem.load Mint64 m b ofs = Some (Vlong old) ->
  Mem.store Mint64 m b ofs value = Some mf ->
  sha_original_global_state mf.
Proof.
  intros HState HLoad HS.
  eapply sha_original_global_state_store; [exact HState| |exact HS].
  eapply sha_dispatch_long_cell_other; [exact HState|exact HLoad|].
  eapply Mem.store_valid_access_3; exact HS.
Qed.

Theorem sha_original_global_state_store_frame_cursor m mf b base value :
  sha_original_global_state m -> 0 <= base ->
  Mem.store Mint64 m b (base + 8) value = Some mf ->
  sha_original_global_state mf.
Proof.
  intros HState HBase HS.
  eapply sha_original_global_state_store; [exact HState| |exact HS].
  eapply sha_dispatch_frame_cursor_other; [exact HState|exact HBase|].
  eapply Mem.store_valid_access_3; exact HS.
Qed.

Theorem sha_original_global_state_alloc m mf lo hi fresh :
  sha_original_global_state m -> Mem.alloc m lo hi = (mf, fresh) ->
  sha_original_global_state mf /\
  fresh <> sha_symbol_block _simplicity_sha256_compression /\
  fresh <> sha_symbol_block _sha256_max_counter.
Proof.
  intros [[HD HC] [HNoWrite HBounds]] HA.
  assert (HVD : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression)).
  { eapply Mem.perm_valid_block.
    eapply (Mem.valid_access_perm m Mptr _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HD. }
  assert (HVC : Mem.valid_block m (sha_symbol_block _sha256_max_counter)).
  { eapply Mem.perm_valid_block.
    eapply (Mem.valid_access_perm m Mint64 _ 0 Cur Readable).
    eapply Mem.load_valid_access; exact HC. }
  assert (HOtherD : sha_symbol_block _simplicity_sha256_compression <> fresh).
  { intro HSame; rewrite HSame in HVD.
    exact (Mem.fresh_block_alloc _ _ _ _ _ HA HVD). }
  assert (HOtherC : sha_symbol_block _sha256_max_counter <> fresh).
  { intro HSame; rewrite HSame in HVC.
    exact (Mem.fresh_block_alloc _ _ _ _ _ HA HVC). }
  split; [|split; congruence]. split.
  - split.
    + unfold sha_dispatch_ok in *; eapply Mem.load_alloc_other; eauto.
    + eapply Mem.load_alloc_other; eauto.
  - split.
    + intros pos HP; apply (HNoWrite pos); eapply Mem.perm_alloc_4; eauto.
    + intros pos k perm HP; apply (HBounds pos k perm).
      eapply Mem.perm_alloc_4; eauto.
Qed.

Theorem sha_original_global_state_free m mf b lo hi :
  sha_original_global_state m ->
  b <> sha_symbol_block _simplicity_sha256_compression ->
  b <> sha_symbol_block _sha256_max_counter ->
  Mem.free m b lo hi = Some mf -> sha_original_global_state mf.
Proof.
  intros [[HD HC] [HNoWrite HBounds]] HOtherD HOtherC HF; split.
  - split.
    + unfold sha_dispatch_ok in *.
      erewrite Mem.load_free; [exact HD|exact HF|left; congruence].
    + erewrite Mem.load_free; [exact HC|exact HF|left; congruence].
  - split.
    + intros pos HP; apply (HNoWrite pos); eapply Mem.perm_free_3; eauto.
    + intros pos k perm HP; apply (HBounds pos k perm).
      eapply Mem.perm_free_3; eauto.
Qed.

Theorem sha_original_global_state_storebytes m mf b ofs bytes :
  sha_original_global_state m ->
  b <> sha_symbol_block _simplicity_sha256_compression ->
  0 < Z.of_nat (length bytes) ->
  Mem.storebytes m b ofs bytes = Some mf ->
  sha_original_global_state mf.
Proof.
  intros [[HD HC] [HNoWrite HBounds]] HOtherD HLen HS.
  assert (HOtherC : b <> sha_symbol_block _sha256_max_counter).
  { intro HSame; subst b. apply (HNoWrite ofs).
    eapply (Mem.storebytes_range_perm _ _ _ _ _ HS); lia. }
  split.
  - split.
    + unfold sha_dispatch_ok in *.
      erewrite Mem.load_storebytes_other; [exact HD|exact HS|left; congruence].
    + erewrite Mem.load_storebytes_other; [exact HC|exact HS|left; congruence].
  - split.
    + intros pos HP; apply (HNoWrite pos); eapply Mem.perm_storebytes_2; eauto.
    + intros pos k perm HP; apply (HBounds pos k perm).
      eapply Mem.perm_storebytes_2; eauto.
Qed.
