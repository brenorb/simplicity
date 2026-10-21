(** Execution preparation for the original Elements input_utxo_hash:
    actual body shape, four local allocations and frame copy. Reuses the
    existing indexed-frame execution and the Elements SHA translation unit. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_application_sep.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_output_layout_step C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_wide C.jet_complement_wide_layout.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_transport C.jet_elements_field_eval.
Require Import C.jet_elements_indexed_exec C.jet_elements_index_eval C.jet_elements_wrapper.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init C.jet_elements_support_sha_tapdata_prep.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.
Local Notation FR := (Tstruct _frameItem noattr).
Local Notation ENVT := (Tstruct _txEnv noattr).
Local Notation TXT := (Tstruct _elementsTransaction noattr).
Local Notation SOT := (Tstruct _utxo noattr).

Notation SIT := (Tstruct _sigInput noattr).

Definition eiu_env (bl bm bx br : block) : env :=
  PTree.set __res (br, CTX) (PTree.set _ctx (bx, CTX)
    (PTree.set _midstate (bm, MID) (PTree.set _src (bl, FR) empty_env))).

Definition eiu_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_input_utxo_hash)))).

Definition eiu_then : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_input_utxo_hash fn_body] beta iota in
      (fn_body f_simplicity_input_utxo_hash) in
    lazymatch b with Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _ ?t _)) _)) => exact t end).

Definition eiu_else : statement :=
  Scall None (Evar _skipBits (Tfunction (Tcons FRP (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst FRP; Econst_int (Int.repr 256) tint].

Lemma eiu_body :
  fn_body f_simplicity_input_utxo_hash =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR))
      (elements_indexed_rest _t'5 _t'6 _numInputs eiu_then eiu_else).
Proof. reflexivity. Qed.

Lemma eiu_blocks bl bm bx br :
  blocks_of_env sha_ge (eiu_env bl bm bx br) = [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (br, 0, 88)].
Proof. vm_compute. reflexivity. Qed.

Lemma eiu_entry env m m1 m2 m3 m4 bl bm bx br bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) -> Mem.alloc m2 0 88 = (m3, bx) ->
  Mem.alloc m3 0 88 = (m4, br) ->
  function_entry2 sha_ge f_simplicity_input_utxo_hash
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (eiu_env bl bm bx br) (eiu_temps env bd dbase bs sbase) m4.
Proof.
  intros HA HB HC HD. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact HA|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bm); [change (Mem.alloc m1 0 32 = (m2, bm)); exact HB|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bx); [change (Mem.alloc m2 0 88 = (m3, bx)); exact HC|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := br); [change (Mem.alloc m3 0 88 = (m4, br)); exact HD|].
    constructor.
  - reflexivity.
Qed.

Lemma eiu_copy m mc bl bm bx br bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (eiu_env bl bm bx br) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)). rewrite HA; exact HS.
    + intros _. change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Lemma eiu_so_script : elements_field_at _utxo _scriptPubKey 0.
Proof. vm_compute; reflexivity. Qed.
Lemma eiu_env_tx : elements_field_at _txEnv _tx 0.
Proof. vm_compute; reflexivity. Qed.
Lemma eiu_sizeof_so : sizeof (Clight.genv_cenv sha_ge) SOT = 112.
Proof. vm_compute; reflexivity. Qed.
Lemma eiu_in_skipBits : In (jets._skipBits, jets.f_skipBits) elements_core_helpers.
Proof. unfold elements_core_helpers. simpl. tauto. Qed.
Lemma eiu_cast256 m : sem_cast (Vint (Int.repr 256)) tint tulong m = Some (Vlong (Int64.repr 256)).
Proof. vm_compute. reflexivity. Qed.

Lemma eiu_encode_some (h : Ty.tySem (Word 8)) :
  @encode (Ty.Sum Ty.Unit (Word 8)) (inr h) = [Some true] ++ @encode (Word 8) h.
Proof. reflexivity. Qed.
Lemma eiu_encode_none :
  @encode (Ty.Sum Ty.Unit (Word 8)) (inl tt) = [Some false] ++ repeat None 256.
Proof. vm_compute. reflexivity. Qed.


Lemma eiu_conf_asset_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_sha256_confAsset =
    Some (sha_symbol_block _simplicity_sha256_confAsset).
Proof. vm_compute; reflexivity. Qed.
Lemma eiu_conf_asset_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _simplicity_sha256_confAsset) Ptrofs.zero) =
    Some (Internal f_simplicity_sha256_confAsset).
Proof. vm_compute; reflexivity. Qed.
Lemma eiu_conf_amt_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_sha256_confAmt =
    Some (sha_symbol_block _simplicity_sha256_confAmt).
Proof. vm_compute; reflexivity. Qed.
Lemma eiu_conf_amt_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _simplicity_sha256_confAmt) Ptrofs.zero) =
    Some (Internal f_simplicity_sha256_confAmt).
Proof. vm_compute; reflexivity. Qed.
