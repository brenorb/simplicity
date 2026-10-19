(** [simplicity_elements_build_txEnv] (elements/txEnv.c), complete: the call
    stores the transaction pointer, the taproot pointer, a copy of the
    genesis hash, the input index and [sigAllHash] -- SHA-256 of the genesis
    hash (twice), the transaction hash, the taproot environment hash and the
    big-endian index, computed by the actual C code -- into the result
    structure.  Conditional on [memcpy_model].  Hand-written for the
    Elements unit (the structure differs from the Bitcoin one); the generic
    live-context toolkit is the generated port. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_call C.jet_sha_add_n_calls C.jet_sha_tapdata_prep C.jet_struct_copy_loads.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_env_store_words C.jet_elements_env_field_eval C.jet_elements_env_tomidstate.
Require Import C.jet_elements_env_ctxo C.jet_elements_env_ctxs C.jet_elements_env_ctxs_ops C.jet_elements_env_ctxs_calls.
Require Import C.jet_elements_env_ctxs_core C.jet_elements_env_tapenv_prelude C.jet_elements_env_tapenv_fill.
Require Import C.jet_elements_env_tapenv_path C.jet_elements_env_tapenv_tail C.jet_elements_env_tx_calls.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation TXE := (Tstruct _txEnv noattr).
Notation TAPE := (Tstruct _elementsTapEnv noattr).
Notation ETX := (Tstruct _elementsTransaction noattr).
Notation RES := (Evar _result TXE).
Notation SIGALL := (Efield RES _sigAllHash MID).

Lemma envu_txEnv_tx : envu_field_at _txEnv _tx 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_txEnv_taproot : envu_field_at _txEnv _taproot 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_txEnv_genesisHash : envu_field_at _txEnv _genesisHash 16.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_txEnv_sigAllHash : envu_field_at _txEnv _sigAllHash 48.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_txEnv_ix : envu_field_at _txEnv _ix 80.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_etx_txHash : envu_field_at _elementsTransaction _txHash 632.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma bt_sizeof_TXE : sizeof sha_ge TXE = 88.
Proof. vm_compute; reflexivity. Qed.
Lemma bt_blockcopy_TXE : alignof_blockcopy sha_ge TXE = 8.
Proof. vm_compute; reflexivity. Qed.
Lemma bt_sizeof_MID : sizeof sha_ge MID = 32.
Proof. vm_compute; reflexivity. Qed.
Lemma bt_blockcopy_MID : alignof_blockcopy sha_ge MID = 4.
Proof. vm_compute; reflexivity. Qed.

Definition bt_env (bRes bC bR : block) : env :=
  PTree.set __res__1 (bR, CTX) (PTree.set _ctx (bC, CTX) (PTree.set _result (bRes, TXE) empty_env)).

Section Blocks.
Variables (bRes bC bR : block).
Definition bt_block_list : list (block * Z * Z) :=
  ltac:(let r := eval vm_compute in (blocks_of_env sha_ge (bt_env bRes bC bR)) in exact r).
Lemma bt_blocks : blocks_of_env sha_ge (bt_env bRes bC bR) = bt_block_list.
Proof. vm_compute. reflexivity. Qed.
End Blocks.

Definition bt_le (vdst vtx vtap vgen : val) (ix : int64) : temp_env :=
  PTree.set _ix (Vlong ix) (PTree.set _genesisHash vgen (PTree.set _taproot vtap (PTree.set _tx vtx
    (PTree.set __res vdst (create_undef_temps (fn_temps f_simplicity_elements_build_txEnv)))))).

Lemma bt_entry m m1 m2 m3 bRes bC bR vdst vtx vtap vgen ix :
  Mem.alloc m 0 88 = (m1, bRes) -> Mem.alloc m1 0 88 = (m2, bC) -> Mem.alloc m2 0 88 = (m3, bR) ->
  function_entry2 sha_ge f_simplicity_elements_build_txEnv [vdst; vtx; vtap; vgen; Vlong ix] m
    (bt_env bRes bC bR) (bt_le vdst vtx vtap vgen ix) m3.
Proof.
  intros A1 A2 A3. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY. contradiction.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bRes); [rewrite bt_sizeof_TXE; exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bC); [change (Mem.alloc m1 0 88 = (m2, bC)); exact A2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bR); [change (Mem.alloc m2 0 88 = (m3, bR)); exact A3|].
    constructor.
  - reflexivity.
Qed.

Definition zero_g (a : expr) (k : nat) : statement :=
  Sassign (Ederef (Ebinop Oadd (Efield a _s A8)
    (Econst_int (Int.repr (Z.of_nat k)) tint) (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint).

Fixpoint zrr (a : expr) (lo n : nat) (rest : statement) : statement :=
  match n with
  | O => rest
  | S k => Ssequence (zero_g a lo) (zrr a (S lo) k rest)
  end.

Definition bt_rest : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_elements_build_txEnv fn_body] beta iota in
                 (fn_body f_simplicity_elements_build_txEnv) in
        let r := drop_seq 11%nat b in exact r).

Lemma bt_body_shape :
  fn_body f_simplicity_elements_build_txEnv =
    Ssequence (Sassign (Efield RES _tx (tptr ETX)) (Etempvar _tx (tptr ETX)))
      (Ssequence (Sassign (Efield RES _taproot (tptr TAPE)) (Etempvar _taproot (tptr TAPE)))
        (Ssequence (Sassign (Efield RES _genesisHash MID) (Ederef (Etempvar _genesisHash (tptr MID)) MID))
          (zrr SIGALL 0 8 bt_rest))).
Proof. reflexivity. Qed.

Local Opaque sha_ge.

Lemma bt_off delta : 0 <= delta <= 4000 ->
  Ptrofs.unsigned (Ptrofs.add Ptrofs.zero (Ptrofs.repr delta)) = delta.
Proof.
  intros H. rewrite Ptrofs.add_zero_l. apply Ptrofs.unsigned_repr.
  change Ptrofs.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma exec_zero_g (e : env) (b : block) (a : expr) (delta : Z) le m m' k :
  (forall le m, eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr delta))) -> typeof a = MID ->
  0 <= delta <= 4000 -> (k < 8)%nat ->
  Mem.store Mint32 m b (delta + 4 * Z.of_nat k) (Vint Int.zero) = Some m' ->
  Clight2.exec_stmt sha_ge e le m (zero_g a k) E0 le m' Out_normal.
Proof.
  intros Ha Hty Hd Hk HS.
  eapply exec_Sassign with (v2 := Vint Int.zero) (v := Vint Int.zero).
  - pose proof (eval_envu_field_array e le m a _sha256_midstate _s 0 A8 b (Ptrofs.repr delta)
      Hty envu_sha256_midstate_s ltac:(intros chunk; discriminate) eq_refl (Ha le m)) as HE.
    rewrite Ptrofs.add_zero in HE.
    eapply eval_Ederef. eapply eval_Ebinop; [exact HE|apply eval_Econst_int|reflexivity].
  - apply eval_Econst_int.
  - reflexivity.
  - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
    assert (HU : Ptrofs.unsigned (Ptrofs.repr delta) = delta)
      by (apply Ptrofs.unsigned_repr; change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite ptr_word_offset_from by (rewrite ?HU; change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite HU. exact HS.
Qed.

Lemma zrr_exec (e : env) (b : block) (a : expr) (delta : Z) (rest : statement) :
  (forall le m, eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr delta))) -> typeof a = MID ->
  0 <= delta <= 4000 ->
  forall n lo le m1 m2 t le' mf out, (lo + n <= 8)%nat ->
  store_words m1 b (delta + 4 * Z.of_nat lo) (repeat Int.zero n) = Some m2 ->
  Clight2.exec_stmt sha_ge e le m2 rest t le' mf out ->
  Clight2.exec_stmt sha_ge e le m1 (zrr a lo n rest) t le' mf out.
Proof.
  intros Ha Hty Hd. induction n as [|n IH]; intros lo le m1 m2 t le' mf out Hn HS HR.
  - cbn in HS. injection HS as <-. exact HR.
  - cbn [repeat store_words] in HS.
    destruct (Mem.store Mint32 m1 b (delta + 4 * Z.of_nat lo) (Vint Int.zero)) as [mm|] eqn:HSt; [|discriminate].
    cbn [zrr]. change t with (E0 ** t).
    eapply exec_Sseq_1 with (le1 := le) (m1 := mm).
    + eapply (exec_zero_g e b a delta le m1 mm lo Ha Hty Hd); [lia|exact HSt].
    + eapply IH; [lia| |exact HR].
      replace (delta + 4 * Z.of_nat (S lo)) with (delta + 4 * Z.of_nat lo + 4) by lia. exact HS.
Qed.

Lemma ev_adr e le m a sid f delta ty b base :
  typeof a = Tstruct sid noattr -> envu_field_at sid f delta ->
  eval_expr sha_ge e le m a (Vptr b (Ptrofs.repr base)) ->
  0 <= base -> 0 <= delta -> base + delta <= Ptrofs.max_unsigned ->
  eval_expr sha_ge e le m (Eaddrof (Efield a f ty) (tptr ty)) (Vptr b (Ptrofs.repr (base + delta))).
Proof.
  intros HT HF HA H0 H1 H2. rewrite <- envu_ptr_add_repr by lia.
  eapply eval_Eaddrof. eapply eval_envu_field_lvalue; eassumption.
Qed.

Lemma sep_one bA bC : GC <> bA -> GM <> bA -> bC <> bA -> GC <> bC -> GM <> bC ->
  ctxs_sep bA [(bC, 48, [], sha256_iv_words, Int64.zero, false)].
Proof.
  intros NG NM NC NGC NMC. split; [exact NG|]. split; [exact NM|]. split.
  - intros [|k] c Hk; cbn in Hk; [injection Hk as <-|destruct k; discriminate].
    cbn [ctx_block ctx_out]. repeat split; try assumption; try lia.
    change Ptrofs.max_unsigned with 18446744073709551615. lia.
  - intros [|i] [|j] ci cj Hi Hj Hij; try congruence; cbn in Hi, Hj;
      try (destruct i; discriminate); destruct j; discriminate.
Qed.

Ltac ls_cores H := lazymatch type of H with LS _ _ ?c _ => c end.

(** The state written to [sigAllHash]. *)
Definition ab (st : list int * list int) (bs : list int) := absorb_i (fst st) (snd st) bs.
Definition fin_regs (st : list int * list int) (c : int64) : list int :=
  snd (absorb_i (fst st) (snd st) (sha_pad c)).
Definition c32 (c : int64) : int64 := Int64.add c (Int64.repr 32).
Definition el_sigall_regs (G T E : list int) (ix : int64) : list int :=
  fin_regs (ab (ab (ab (ab (ab ([], sha256_iv_words) (be_bytes (norm8 G))) (be_bytes (norm8 G)))
                       (be_bytes (norm8 T))) (be_bytes (norm8 E))) (c_be32_bytes ix))
    (Int64.add (c32 (c32 (c32 (c32 Int64.zero)))) (Int64.repr 4)).

Theorem eval_build_txEnv (Hmodel : memcpy_model) m bD oD btx otx btap otap bg og (ix : int64)
    (G T E : list int) :
  0 <= oD /\ oD + 88 <= Ptrofs.max_unsigned -> (8 | oD) ->
  Mem.range_perm m bD oD (oD + 88) Cur Writable ->
  0 <= otx /\ otx + 760 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m btx (otx + 632 + 4 * Z.of_nat j) = Some (Vint (nth j T Int.zero))) ->
  0 <= otap /\ otap + 104 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m btap (otap + 72 + 4 * Z.of_nat j) = Some (Vint (nth j E Int.zero))) ->
  0 <= og /\ og + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bg (og + 4 * Z.of_nat j) = Some (Vint (nth j G Int.zero))) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_elements_build_txEnv)
      [Vptr bD (Ptrofs.repr oD); Vptr btx (Ptrofs.repr otx); Vptr btap (Ptrofs.repr otap);
       Vptr bg (Ptrofs.repr og); Vlong ix] E0 m' Vundef /\
    Mem.load Mptr m' bD oD = Some (Vptr btx (Ptrofs.repr otx)) /\
    Mem.load Mptr m' bD (oD + 8) = Some (Vptr btap (Ptrofs.repr otap)) /\
    (forall j, (j < 8)%nat -> Mem.load Mint32 m' bD (oD + 16 + 4 * Z.of_nat j) = Some (Vint (nth j G Int.zero))) /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bD (oD + 48 + 4 * Z.of_nat j) = Some (Vint (nth j (el_sigall_regs G T E ix) Int.zero))) /\
    Mem.load Mint64 m' bD (oD + 80) = Some (Vlong ix) /\
    (forall ch b ofs, Mem.valid_block m b -> (b <> bD \/ ofs + size_chunk ch <= oD \/ oD + 88 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HoD HaD PD Hotx HT Hotap HE Hog HG Hdisp HMax.
  set (vdst := Vptr bD (Ptrofs.repr oD)). set (vtx := Vptr btx (Ptrofs.repr otx)).
  set (vtap := Vptr btap (Ptrofs.repr otap)). set (vgen := Vptr bg (Ptrofs.repr og)).
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (VD : Mem.valid_block m bD) by (eapply Mem.perm_valid_block; apply (PD oD); lia).
  assert (Vtx : Mem.valid_block m btx) by (eapply load_valid_block; exact (HT 0%nat ltac:(lia))).
  assert (Vtap : Mem.valid_block m btap) by (eapply load_valid_block; exact (HE 0%nat ltac:(lia))).
  assert (Vg : Mem.valid_block m bg) by (eapply load_valid_block; exact (HG 0%nat ltac:(lia))).
  destruct (Mem.alloc m 0 88) as [ma1 bRes] eqn:A1.
  destruct (Mem.alloc ma1 0 88) as [ma2 bC] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [m0 bR] eqn:A3.
  assert (HAL : alloc_list m [88; 88; 88] = (m0, [bRes; bC; bR])).
  { cbn [alloc_list]. rewrite A1, A2, A3. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PRes0 VRes0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PC0 VC0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PR0 VR0] FA3]; subst. clear FA FA1 FA2 FA3 HAL.
  apply NoDup_cons_iff in ND. destruct ND as [ND1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [ND2 _].
  assert (NResC : bRes <> bC) by (intros E0'; apply ND1; left; symmetry; exact E0').
  assert (NResR : bRes <> bR) by (intros E0'; apply ND1; right; left; symmetry; exact E0').
  assert (NCR : bC <> bR) by (intros E0'; apply ND2; left; symmetry; exact E0').
  assert (Fresh : forall b, Mem.valid_block m b -> b <> bRes /\ b <> bC /\ b <> bR).
  { intros b Hb. pose proof (FRh b Hb) as F. cbn [In] in F. repeat split; intros E0'; apply F; subst; tauto. }
  destruct (Fresh GC VG) as (NGRes & NGC & NGR). destruct (Fresh GM VM) as (NMRes & NMC & NMR).
  destruct (Fresh bD VD) as (NDRes & NDC & NDR). destruct (Fresh bg Vg) as (NgRes & NgC & NgR).
  set (e := bt_env bRes bC bR).
  set (le := bt_le vdst vtx vtap vgen ix).
  assert (HeRes : e!_result = Some (bRes, TXE)) by reflexivity.
  assert (HeC : e!_ctx = Some (bC, CTX)) by reflexivity.
  assert (HeR : e!__res__1 = Some (bR, CTX)) by reflexivity.
  assert (EvRes : forall lx mx, eval_expr sha_ge e lx mx RES (Vptr bRes Ptrofs.zero)).
  { intros lx mx. eapply eval_Elvalue; [apply eval_Evar_local; exact HeRes|apply deref_loc_copy; reflexivity]. }
  assert (EvSig : forall lx mx, eval_expr sha_ge e lx mx SIGALL (Vptr bRes (Ptrofs.repr 48))).
  { intros lx mx. pose proof (eval_envu_field_struct e lx mx RES _txEnv _sigAllHash 48 _sha256_midstate
      bRes Ptrofs.zero eq_refl envu_txEnv_sigAllHash (EvRes lx mx)) as HEv.
    rewrite Ptrofs.add_zero_l in HEv. exact HEv. }
  (* result.tx, result.taproot *)
  destruct (Mem.valid_access_store m0 Mptr bRes 0 vtx) as [m1 S1].
  { split; [|exists 0; reflexivity]. intros o Ho. change (size_chunk Mptr) with 8 in Ho.
    eapply Mem.perm_implies; [apply PRes0; lia|constructor]. }
  destruct (Mem.valid_access_store m1 Mptr bRes 8 vtap) as [m2 S2].
  { split; [|exists 1; reflexivity]. intros o Ho. change (size_chunk Mptr) with 8 in Ho.
    eapply Mem.perm_store_1; [exact S1|]. eapply Mem.perm_implies; [apply PRes0; lia|constructor]. }
  assert (P2 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|exact Hp]. }
  assert (L2 : forall ch b ofs, b <> bRes -> Mem.load ch m2 b ofs = Mem.load ch m0 b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (left; exact Hb).
    apply (Mem.load_store_other _ _ _ _ _ _ S1). left. exact Hb. }
  (* result.genesisHash = *genesisHash *)
  assert (HG2 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m2 bg (og + 4 * Z.of_nat j) = Some (Vint (nth j G Int.zero))).
  { intros j Hj. rewrite L2 by exact NgRes. rewrite XL by exact Vg. apply HG, Hj. }
  assert (PG2 : Mem.range_perm m2 bg og (og + 32) Cur Readable).
  { intros o Ho. set (j := Z.to_nat ((o - og) / 4)).
    assert (Hj : (j < 8)%nat) by (unfold j; apply Nat2Z.inj_lt; rewrite Z2Nat.id by (apply Z.div_pos; lia);
      apply Z.div_lt_upper_bound; lia).
    pose proof (Mem.load_valid_access _ _ _ _ _ (HG2 j Hj)) as [HR _]. apply HR.
    change (size_chunk Mint32) with 4. unfold j. rewrite Z2Nat.id by (apply Z.div_pos; lia).
    pose proof (Z.div_mod (o - og) 4 ltac:(lia)). pose proof (Z.mod_pos_bound (o - og) 4 ltac:(lia)). lia. }
  assert (AG : (4 | og)).
  { pose proof (Mem.load_valid_access _ _ _ _ _ (HG2 0%nat ltac:(lia))) as [_ HA].
    change (align_chunk Mint32) with 4 in HA. rewrite Z.add_0_r in HA. exact HA. }
  destruct (Mem.range_perm_loadbytes m2 bg og 32 PG2) as (gb & HGB).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HGB) as HGBL.
  destruct (Mem.range_perm_storebytes m2 bRes 16 gb) as (m2g & SGen).
  { rewrite HGBL. change (Z.of_nat (Z.to_nat 32)) with 32. intros o Ho.
    eapply Mem.perm_implies; [apply P2, PRes0; lia|constructor]. }
  assert (HGR : Mem.loadbytes m2g bRes 16 32 = Some gb).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ SGen) as H. rewrite HGBL in H. exact H. }
  assert (HGenRes : forall j, (j < 8)%nat ->
    Mem.load Mint32 m2g bRes (16 + 4 * Z.of_nat j) = Some (Vint (nth j G Int.zero))).
  { intros j Hj.
    apply (equal_loadbytes_field Mint32 m2 m2g bg bRes og 16 32 (4 * Z.of_nat j) gb _
             ltac:(clear; lia) ltac:(change (size_chunk Mint32) with 4; clear - Hj; lia) HGB HGR).
    - exists (4 + Z.of_nat j). change (align_chunk Mint32) with 4. clear. lia.
    - apply HG2, Hj. }
  assert (P2g : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m2g b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_storebytes_1; [exact SGen|apply P2, Hp]. }
  assert (L2g : forall ch b ofs, b <> bRes -> Mem.load ch m2g b ofs = Mem.load ch m0 b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_storebytes_other _ _ _ _ _ SGen) by (left; exact Hb). apply L2, Hb. }
  (* the zeroed midstate, result.ix *)
  destruct (store_words_exists (repeat Int.zero 8) m2g bRes 48) as [m3 SW].
  { rewrite repeat_length. intros o Ho. eapply Mem.perm_implies; [apply P2g, PRes0; cbn in Ho; lia|constructor]. }
  { exists 12. reflexivity. }
  assert (P3 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ SW). apply P2g, Hp. }
  destruct (Mem.valid_access_store m3 Mint64 bRes 80 (Vlong ix)) as [m4 S4].
  { split; [|exists 10; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_implies; [apply P3, PRes0; lia|constructor]. }
  assert (P4 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S4|]. apply P3, Hp. }
  assert (V4 : forall b, Mem.valid_block m0 b -> Mem.valid_block m4 b).
  { intros b Hb. eapply Mem.store_valid_block_1; [exact S4|]. unfold Mem.valid_block.
    rewrite (store_words_nextblock _ _ _ _ _ SW).
    eapply Mem.storebytes_valid_block_1; [exact SGen|].
    eapply Mem.store_valid_block_1; [exact S2|]. eapply Mem.store_valid_block_1; [exact S1|exact Hb]. }
  assert (L4 : forall ch b ofs, b <> bRes -> Mem.load ch m4 b ofs = Mem.load ch m0 b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by (left; exact Hb).
    rewrite (store_words_load_other _ _ _ _ _ SW) by (left; exact Hb). apply L2g, Hb. }
  assert (LR4 : forall ch ofs, ofs + size_chunk ch <= 48 ->
    Mem.load ch m4 bRes ofs = Mem.load ch m2g bRes ofs).
  { intros ch ofs Hr. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by (right; left; lia).
    apply (store_words_load_other _ _ _ _ _ SW). right; left. exact Hr. }
  assert (R0 : Mem.load Mptr m4 bRes 0 = Some vtx).
  { rewrite LR4 by (change (size_chunk Mptr) with 8; clear; lia).
    rewrite (Mem.load_storebytes_other _ _ _ _ _ SGen) by (right; left; change (size_chunk Mptr) with 8; clear; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (right; left; change (size_chunk Mptr) with 8; clear; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ S1). reflexivity. }
  assert (R8 : Mem.load Mptr m4 bRes 8 = Some vtap).
  { rewrite LR4 by (change (size_chunk Mptr) with 8; clear; lia).
    rewrite (Mem.load_storebytes_other _ _ _ _ _ SGen) by (right; left; change (size_chunk Mptr) with 8; clear; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ S2). reflexivity. }
  assert (R16 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m4 bRes (16 + 4 * Z.of_nat j) = Some (Vint (nth j G Int.zero))).
  { intros j Hj. rewrite LR4 by (change (size_chunk Mint32) with 4; clear - Hj; lia). apply HGenRes, Hj. }
  assert (R80 : Mem.load Mint64 m4 bRes 80 = Some (Vlong ix)).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ S4). reflexivity. }
  assert (Kold4 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite L4 by (apply (Fresh b Hb)). apply XL, Hb. }
  (* sha256_init(result.sigAllHash.s) *)
  destruct (ctxo_init bC bRes 48 NResC NGC NGRes NMC NMRes
              ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) m4 bR
              (not_eq_sym NResR) (not_eq_sym NCR) ltac:(exists 12; reflexivity)
              (V4 _ (XV _ VG)) (V4 _ (XV _ VM)) NGR NMR)
    as (mi & m5 & bytes & HInit & HLB & HSB & HC0 & HL5 & HP5 & HV5).
  { intros o Ho. apply P4, PR0, Ho. }
  { intros o Ho. apply P4, PC0, Ho. }
  { intros o Ho. eapply Mem.perm_implies; [apply P4, PRes0; lia|constructor]. }
  { unfold sha_dispatch_ok. rewrite Kold4 by exact VG. exact Hdisp. }
  { rewrite Kold4 by exact VM. exact HMax. }
  pose proof (sep_one bRes bC NGRes NMRes (not_eq_sym NResC) NGC NMC) as HSep.
  assert (HLive : ctxs_live m5 bRes [(bC, 48, [], sha256_iv_words, Int64.zero, false)] (fun _ => True)).
  { intros j cj Hj _. destruct j as [|j]; cbn in Hj; [injection Hj as <-; exact HC0|destruct j; discriminate]. }
  pose proof (LS_intro m5 bRes _ (fun _ : nat => True) HSep HLive) as HLS5. cbn [map core_of] in HLS5.
  assert (Vold5 : forall b, Mem.valid_block m b -> Mem.valid_block m5 b) by (intros b Hb; apply HV5, V4, XV, Hb).
  assert (Kold5 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m5 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (Fresh b Hb) as (F1 & F2 & F3).
    rewrite HL5; [apply Kold4, Hb|apply V4, XV, Hb|exact F3|exact F2|left; exact F1]. }
  (* the old blocks through any run of context operations *)
  assert (KoldQ : forall mi' mj, mfrP (opP bRes bC 48) mi' mj ->
    (forall b, Mem.valid_block m b -> Mem.valid_block mi' b) ->
    (forall ch b ofs, Mem.valid_block m b -> Mem.load ch mi' b ofs = Mem.load ch m b ofs) ->
    (forall b, Mem.valid_block m b -> Mem.valid_block mj b) /\
    (forall ch b ofs, Mem.valid_block m b -> Mem.load ch mj b ofs = Mem.load ch m b ofs)).
  { intros mi' mj (L & _ & V) HVi HKi. split; [intros b Hb; apply V, HVi, Hb|].
    intros ch b ofs Hb. destruct (Fresh b Hb) as (F1 & F2 & F3).
    rewrite L; [apply HKi, Hb|apply HVi, Hb|split; [exact F2|left; exact F1]]. }
  set (oGp := Ptrofs.repr og).
  assert (HoGp : Ptrofs.unsigned oGp = og) by (apply Ptrofs.unsigned_repr; lia).
  (* sha256_hash(&ctx, genesisHash) twice *)
  let cc := ls_cores HLS5 in
  destruct (LS_hash Hmodel bRes cc (fun _ : nat => True) 0%nat bC 48 _ _ _ eq_refl Logic.I m5 bg oGp (norm8 G) HLS5 eq_refl)
    as (m6 & HCall6 & HLS6 & HF6).
  { rewrite HoGp. lia. }
  { intros j Hj. rewrite HoGp, norm8_nth by exact Hj. rewrite Kold5 by exact Vg. apply HG, Hj. }
  cbn [upd] in HLS6. destruct (KoldQ m5 m6 HF6 Vold5 Kold5) as (Vold6 & Kold6).
  let cc := ls_cores HLS6 in
  destruct (LS_hash Hmodel bRes cc (fun _ : nat => True) 0%nat bC 48 _ _ _ eq_refl Logic.I m6 bg oGp (norm8 G) HLS6 eq_refl)
    as (m7 & HCall7 & HLS7 & HF7).
  { rewrite HoGp. lia. }
  { intros j Hj. rewrite HoGp, norm8_nth by exact Hj. rewrite Kold6 by exact Vg. apply HG, Hj. }
  cbn [upd] in HLS7. destruct (KoldQ m6 m7 HF7 Vold6 Kold6) as (Vold7 & Kold7).
  (* sha256_hash(&ctx, &tx->txHash) *)
  set (oT := Ptrofs.repr (otx + 632)).
  assert (HoT : Ptrofs.unsigned oT = otx + 632) by (apply Ptrofs.unsigned_repr; lia).
  let cc := ls_cores HLS7 in
  destruct (LS_hash Hmodel bRes cc (fun _ : nat => True) 0%nat bC 48 _ _ _ eq_refl Logic.I m7 btx oT (norm8 T) HLS7 eq_refl)
    as (m8 & HCall8 & HLS8 & HF8).
  { rewrite HoT. lia. }
  { intros j Hj. rewrite HoT, norm8_nth by exact Hj. rewrite Kold7 by exact Vtx. apply HT, Hj. }
  cbn [upd] in HLS8. destruct (KoldQ m7 m8 HF8 Vold7 Kold7) as (Vold8 & Kold8).
  (* sha256_hash(&ctx, &taproot->tapEnvHash) *)
  set (oE := Ptrofs.repr (otap + 72)).
  assert (HoE : Ptrofs.unsigned oE = otap + 72) by (apply Ptrofs.unsigned_repr; lia).
  let cc := ls_cores HLS8 in
  destruct (LS_hash Hmodel bRes cc (fun _ : nat => True) 0%nat bC 48 _ _ _ eq_refl Logic.I m8 btap oE (norm8 E) HLS8 eq_refl)
    as (m9 & HCall9 & HLS9 & HF9).
  { rewrite HoE. lia. }
  { intros j Hj. rewrite HoE, norm8_nth by exact Hj. rewrite Kold8 by exact Vtap. apply HE, Hj. }
  cbn [upd] in HLS9. destruct (KoldQ m8 m9 HF9 Vold8 Kold8) as (Vold9 & Kold9).
  (* sha256_u32be(&ctx, ix), sha256_finalize(&ctx) *)
  let cc := ls_cores HLS9 in
  destruct (LS_u32be Hmodel bRes cc (fun _ : nat => True) 0%nat bC 48 _ _ _ eq_refl Logic.I m9 ix HLS9)
    as (m10 & vr10 & HCall10 & HLS10 & HF10).
  cbn [upd] in HLS10. destruct (KoldQ m9 m10 HF10 Vold9 Kold9) as (Vold10 & Kold10).
  let cc := ls_cores HLS10 in
  destruct (LS_finalize Hmodel bRes cc (fun _ : nat => True) 0%nat bC 48 _ _ _ eq_refl Logic.I m10 HLS10)
    as (m11 & vr11 & HCall11 & HReg11 & _ & HF11).
  change (forall i, (i < 8)%nat ->
    Mem.load Mint32 m11 bRes (48 + 4 * Z.of_nat i) = Some (Vint (nth i (el_sigall_regs G T E ix) Int.zero))) in HReg11.
  destruct (KoldQ m10 m11 HF11 Vold10 Kold10) as (Vold11 & Kold11).
  pose proof (mfrP_trans _ _ _ _ (mfrP_trans _ _ _ _ (mfrP_trans _ _ _ _ (mfrP_trans _ _ _ _
    (mfrP_trans _ _ _ _ HF6 HF7) HF8) HF9) HF10) HF11) as (L11 & P11 & V11).
  assert (VRes5 : Mem.valid_block m5 bRes) by (apply HV5, V4, VRes0).
  assert (LRes11 : forall ch ofs, (ofs + size_chunk ch <= 48 \/ 80 <= ofs) ->
    Mem.load ch m11 bRes ofs = Mem.load ch m4 bRes ofs).
  { intros ch ofs Hr. rewrite L11; [|exact VRes5|split; [exact NResC|right; lia]].
    apply HL5; [apply V4, VRes0|exact NResR|exact NResC|right; lia]. }
  assert (Pall11 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m11 b ofs k p).
  { intros b ofs k p Hp. apply P11, HP5, P4, Hp. }
  (* *_res = result *)
  destruct (Mem.range_perm_loadbytes m11 bRes 0 88) as (cb & HCB).
  { intros o Ho. eapply Mem.perm_implies; [apply Pall11, PRes0, Ho|constructor]. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HCB) as HCBL.
  destruct (Mem.range_perm_storebytes m11 bD oD cb) as (m12 & SG).
  { rewrite HCBL. change (Z.of_nat (Z.to_nat 88)) with 88. intros o Ho. apply Pall11, XP, PD, Ho. }
  assert (HDB : Mem.loadbytes m12 bD oD 88 = Some cb).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ SG) as H. rewrite HCBL in H. exact H. }
  assert (Pall12 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m12 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_storebytes_1; [exact SG|apply Pall11, Hp]. }
  (* freeing the locals *)
  destruct (free_list_blocks (bt_block_list bRes bC bR) m12) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn ofs Hr. apply Pall12. cbn [bt_block_list In] in HIn.
    repeat (destruct HIn as [E0'|HIn]; [injection E0' as <- <- <-; first [apply PRes0|apply PC0|apply PR0]; exact Hr|]).
    contradiction. }
  { cbn [bt_block_list map fst].
    repeat (apply NoDup_cons;
      [let HIn := fresh in intro HIn; cbn [In] in HIn;
       repeat (destruct HIn as [HIn|HIn]; [first [exact (NResC HIn)|exact (NResR HIn)|exact (NCR HIn)
         |exact (NResC (eq_sym HIn))|exact (NResR (eq_sym HIn))|exact (NCR (eq_sym HIn))]|]); exact HIn|]).
    apply NoDup_nil. }
  cbn [bt_block_list map fst] in HLf, HPf.
  assert (LDf : forall ch ofs, Mem.load ch mf bD ofs = Mem.load ch m12 bD ofs).
  { intros ch ofs. apply HLf. intros HIn. cbn [In] in HIn.
    repeat (destruct HIn as [HIn|HIn]; [congruence|]). exact HIn. }
  exists mf. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply eval_funcall_internal with (e := e) (m1 := m0) (m2 := m12) (out := Out_return None).
    + apply bt_entry with (m1 := ma1) (m2 := ma2); assumption.
    + rewrite bt_body_shape.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
      { eapply exec_Sassign with (v2 := vtx) (v := vtx).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_txEnv_tx|apply EvRes].
        - apply eval_Etempvar. reflexivity.
        - reflexivity.
        - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite bt_off by lia. exact S1. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2).
      { eapply exec_Sassign with (v2 := vtap) (v := vtap).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_txEnv_taproot|apply EvRes].
        - apply eval_Etempvar. reflexivity.
        - reflexivity.
        - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite bt_off by lia. exact S2. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2g).
      { eapply exec_Sassign with (v2 := vgen) (v := vgen).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_txEnv_genesisHash|apply EvRes].
        - eapply eval_Elvalue; [eapply eval_Ederef; apply eval_Etempvar; reflexivity|apply deref_loc_copy; reflexivity].
        - reflexivity.
        - eapply assign_loc_copy with (bytes := gb); cbn [typeof].
          + reflexivity.
          + intros _. rewrite bt_blockcopy_MID. rewrite Ptrofs.unsigned_repr by lia. exact AG.
          + intros _. rewrite bt_blockcopy_MID, bt_off by lia. exists 4. reflexivity.
          + left. exact NgRes.
          + rewrite bt_sizeof_MID, Ptrofs.unsigned_repr by lia. exact HGB.
          + rewrite bt_off by lia. exact SGen. }
      eapply (zrr_exec e bRes SIGALL 48 bt_rest EvSig eq_refl ltac:(lia) 8 0 le m2g m3); [lia|exact SW|].
      cbv delta [bt_rest] beta iota.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m4).
      { eapply exec_Sassign with (v2 := Vlong ix) (v := Vlong ix).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_txEnv_ix|apply EvRes].
        - apply eval_Etempvar. reflexivity.
        - reflexivity.
        - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite bt_off by lia. exact S4. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m5).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi).
        - pose proof (eval_envu_field_array e le m4 SIGALL _sha256_midstate _s 0 A8 bRes (Ptrofs.repr 48)
            eq_refl envu_sha256_midstate_s ltac:(intros chunk; discriminate) eq_refl (EvSig le m4)) as HEv.
          rewrite Ptrofs.add_zero in HEv.
          exact (te_call_init e le m4 mi __res__1 (Efield SIGALL _s A8) bR bRes (Ptrofs.repr 48)
                   eq_refl HeR HEv eq_refl HInit).
        - exact (exec_ctx_struct_copy e le mi m5 _ctx __res__1 bC bR bytes HeC HeR NCR HLB HSB). }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m6).
      { eapply mt_call_hash with (bx := bC) (bt := bg) (ot := oGp);
          [reflexivity|exact HeC|apply eval_Etempvar; reflexivity|reflexivity|exact HCall6]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m7).
      { eapply mt_call_hash with (bx := bC) (bt := bg) (ot := oGp);
          [reflexivity|exact HeC|apply eval_Etempvar; reflexivity|reflexivity|exact HCall7]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m8).
      { eapply mt_call_hash with (bx := bC) (bt := btx) (ot := oT); [reflexivity|exact HeC| |reflexivity|exact HCall8].
        unfold oT. eapply ev_adr; [reflexivity|exact envu_etx_txHash| |lia|lia|lia].
        apply eval_envu_deref_struct. reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m9).
      { eapply mt_call_hash with (bx := bC) (bt := btap) (ot := oE); [reflexivity|exact HeC| |reflexivity|exact HCall9].
        unfold oE. eapply ev_adr; [reflexivity|exact envu_elementsTapEnv_tapEnvHash| |lia|lia|lia].
        apply eval_envu_deref_struct. reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m10).
      { eapply mt_call_u32be with (bx := bC) (x := ix);
          [reflexivity|exact HeC|apply eval_Etempvar; reflexivity|reflexivity|exact HCall10]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m11).
      { eapply mt_call_finalize; [reflexivity|exact HeC|exact HCall11]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m12).
      { eapply exec_Sassign with (v2 := Vptr bRes Ptrofs.zero) (v := Vptr bRes Ptrofs.zero).
        - eapply eval_Ederef. apply eval_Etempvar. reflexivity.
        - apply EvRes.
        - reflexivity.
        - eapply assign_loc_copy with (bytes := cb); cbn [typeof].
          + reflexivity.
          + intros _. rewrite bt_blockcopy_TXE. exists 0. reflexivity.
          + intros _. rewrite bt_blockcopy_TXE. rewrite Ptrofs.unsigned_repr by lia. exact HaD.
          + left. exact (not_eq_sym NDRes).
          + rewrite bt_sizeof_TXE. exact HCB.
          + rewrite Ptrofs.unsigned_repr by lia. exact SG. }
      apply exec_Sreturn_none.
    + cbn. reflexivity.
    + unfold e. rewrite bt_blocks. exact HFL.
  - rewrite LDf. replace oD with (oD + 0) at 1 by lia.
    apply (equal_loadbytes_field Mptr m11 m12 bRes bD 0 oD 88 0 cb vtx ltac:(clear; lia)
             ltac:(change (size_chunk Mptr) with 8; clear; lia) HCB HDB).
    + rewrite Z.add_0_r. exact HaD.
    + rewrite Z.add_0_l, LRes11 by (left; change (size_chunk Mptr) with 8; clear; lia). exact R0.
  - rewrite LDf.
    apply (equal_loadbytes_field Mptr m11 m12 bRes bD 0 oD 88 8 cb vtap ltac:(clear; lia)
             ltac:(change (size_chunk Mptr) with 8; clear; lia) HCB HDB).
    + destruct HaD as [k Hk]. exists (k + 1). change (align_chunk Mptr) with 8. clear - Hk. lia.
    + rewrite Z.add_0_l, LRes11 by (left; change (size_chunk Mptr) with 8; clear; lia). exact R8.
  - intros j Hj. rewrite LDf. replace (oD + 16 + 4 * Z.of_nat j) with (oD + (16 + 4 * Z.of_nat j)) by lia.
    apply (equal_loadbytes_field Mint32 m11 m12 bRes bD 0 oD 88 (16 + 4 * Z.of_nat j) cb _
             ltac:(clear; lia) ltac:(change (size_chunk Mint32) with 4; clear - Hj; lia) HCB HDB).
    + destruct HaD as [k Hk]. exists (2 * k + 4 + Z.of_nat j). change (align_chunk Mint32) with 4. clear - Hk. lia.
    + rewrite Z.add_0_l, LRes11 by (left; change (size_chunk Mint32) with 4; clear - Hj; lia). apply R16, Hj.
  - intros j Hj. rewrite LDf. replace (oD + 48 + 4 * Z.of_nat j) with (oD + (48 + 4 * Z.of_nat j)) by lia.
    apply (equal_loadbytes_field Mint32 m11 m12 bRes bD 0 oD 88 (48 + 4 * Z.of_nat j) cb _
             ltac:(clear; lia) ltac:(change (size_chunk Mint32) with 4; clear - Hj; lia) HCB HDB).
    + destruct HaD as [k Hk]. exists (2 * k + 12 + Z.of_nat j). change (align_chunk Mint32) with 4. clear - Hk. lia.
    + rewrite Z.add_0_l. apply HReg11, Hj.
  - rewrite LDf.
    apply (equal_loadbytes_field Mint64 m11 m12 bRes bD 0 oD 88 80 cb (Vlong ix) ltac:(clear; lia)
             ltac:(change (size_chunk Mint64) with 8; clear; lia) HCB HDB).
    + destruct HaD as [k Hk]. exists (k + 10). change (align_chunk Mint64) with 8. clear - Hk. lia.
    + rewrite Z.add_0_l, LRes11 by (right; clear; lia). exact R80.
  - intros ch b ofs Hb Hr. destruct (Fresh b Hb) as (F1 & F2 & F3).
    rewrite HLf by (intros HIn; cbn [In] in HIn; repeat (destruct HIn as [HIn|HIn]; [congruence|]); exact HIn).
    rewrite (Mem.load_storebytes_other _ _ _ _ _ SG);
      [apply Kold11, Hb|rewrite HCBL; change (Z.of_nat (Z.to_nat 88)) with 88; exact Hr].
  - intros b ofs k p Hp. pose proof (Fresh b (Mem.perm_valid_block _ _ _ _ _ Hp)) as (F1 & F2 & F3).
    apply HPf; [|apply Pall12, XP, Hp].
    intros HIn; cbn [In] in HIn; repeat (destruct HIn as [HIn|HIn]; [congruence|]); exact HIn.
  - intros b Hb. apply HVf. eapply Mem.storebytes_valid_block_1; [exact SG|]. apply Vold11, Hb.
Qed.
