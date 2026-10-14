(** [simplicity_bitcoin_build_txEnv] (bitcoin/txEnv.c), complete: the call
    stores the transaction pointer, the taproot pointer, the input index and
    [sigAllHash] -- SHA-256 of the transaction hash, the taproot environment
    hash and the big-endian index, computed by the actual C code -- into the
    result structure.  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_call C.jet_sha_add_n_calls C.jet_sha_tapdata_prep C.jet_struct_copy_loads.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate C.jet_bitcoin_env_hashbuffer.
Require Import C.jet_bitcoin_env_ctxo C.jet_bitcoin_env_ctxs C.jet_bitcoin_env_ctxs_ops C.jet_bitcoin_env_ctxs_calls.
Require Import C.jet_bitcoin_env_ctxs_core C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_fill.
Require Import C.jet_bitcoin_env_tapenv_path C.jet_bitcoin_env_tapenv_tail.
Require Import C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill C.jet_bitcoin_env_copyinput.
Require Import C.jet_bitcoin_env_tx_prelude C.jet_bitcoin_env_tx_fill C.jet_bitcoin_env_tx_init.
Require Import C.jet_bitcoin_env_tx_txhash C.jet_bitcoin_env_tx_calls C.jet_bitcoin_env_tx_outdefs C.jet_bitcoin_env_tx_outloop.
Require Import C.jet_bitcoin_env_tx_indefs C.jet_bitcoin_env_tx_inops C.jet_bitcoin_env_tx_inexec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation TXE := (Tstruct _txEnv noattr).
Notation TAPE := (Tstruct _bitcoinTapEnv noattr).
Notation RES := (Evar _result TXE).
Notation SIGALL := (Efield RES _sigAllHash MID).

Lemma envu_txEnv_tx : envu_field_at _txEnv _tx 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_txEnv_taproot : envu_field_at _txEnv _taproot 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_txEnv_sigAllHash : envu_field_at _txEnv _sigAllHash 16.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_txEnv_ix : envu_field_at _txEnv _ix 48.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma bt_sizeof_TXE : sizeof sha_ge TXE = 56.
Proof. vm_compute; reflexivity. Qed.
Lemma bt_blockcopy_TXE : alignof_blockcopy sha_ge TXE = 8.
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

Definition bt_le (vdst vtx vtap : val) (ix : int64) : temp_env :=
  PTree.set _ix (Vlong ix) (PTree.set _taproot vtap (PTree.set _tx vtx (PTree.set __res vdst
    (create_undef_temps (fn_temps f_simplicity_bitcoin_build_txEnv))))).

Lemma bt_entry m m1 m2 m3 bRes bC bR vdst vtx vtap ix :
  Mem.alloc m 0 56 = (m1, bRes) -> Mem.alloc m1 0 88 = (m2, bC) -> Mem.alloc m2 0 88 = (m3, bR) ->
  function_entry2 sha_ge f_simplicity_bitcoin_build_txEnv [vdst; vtx; vtap; Vlong ix] m
    (bt_env bRes bC bR) (bt_le vdst vtx vtap ix) m3.
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

(** A run of zero assignments in a right-nested sequence. *)
Fixpoint zrr (a : expr) (lo n : nat) (rest : statement) : statement :=
  match n with
  | O => rest
  | S k => Ssequence (zero_g a lo) (zrr a (S lo) k rest)
  end.

Definition bt_rest : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_bitcoin_build_txEnv fn_body] beta iota in
                 (fn_body f_simplicity_bitcoin_build_txEnv) in
        let r := drop_seq 10%nat b in exact r).

Lemma bt_body_shape :
  fn_body f_simplicity_bitcoin_build_txEnv =
    Ssequence (Sassign (Efield RES _tx (tptr TX)) (Etempvar _tx (tptr TX)))
      (Ssequence (Sassign (Efield RES _taproot (tptr TAPE)) (Etempvar _taproot (tptr TAPE)))
        (zrr SIGALL 0 8 bt_rest)).
Proof. reflexivity. Qed.

Local Opaque sha_ge.

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
    + eapply (exec_zero_g e b a delta Ha Hty Hd); [lia|exact HSt].
    + eapply IH; [lia| |exact HR].
      replace (delta + 4 * Z.of_nat (S lo)) with (delta + 4 * Z.of_nat lo + 4) by lia. exact HS.
Qed.

(** The state written to [sigAllHash]. *)
Definition sigall_regs (T E : list int) (ix : int64) : list int :=
  fin_regs (ab (ab (ab st0 (be_bytes (norm8 T))) (be_bytes (norm8 E))) (c_be32_bytes ix))
    (Int64.add (c32 (c32 Int64.zero)) (Int64.repr 4)).

Theorem eval_build_txEnv (Hmodel : memcpy_model) m bD oD btx otx btap otap (ix : int64) (T E : list int) :
  0 <= oD /\ oD + 56 <= Ptrofs.max_unsigned -> (8 | oD) ->
  Mem.range_perm m bD oD (oD + 56) Cur Writable ->
  0 <= otx /\ otx + 400 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m btx (otx + 368 + 4 * Z.of_nat j) = Some (Vint (nth j T Int.zero))) ->
  0 <= otap /\ otap + 104 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m btap (otap + 72 + 4 * Z.of_nat j) = Some (Vint (nth j E Int.zero))) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_bitcoin_build_txEnv)
      [Vptr bD (Ptrofs.repr oD); Vptr btx (Ptrofs.repr otx); Vptr btap (Ptrofs.repr otap); Vlong ix] E0 m' Vundef /\
    Mem.load Mptr m' bD oD = Some (Vptr btx (Ptrofs.repr otx)) /\
    Mem.load Mptr m' bD (oD + 8) = Some (Vptr btap (Ptrofs.repr otap)) /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bD (oD + 16 + 4 * Z.of_nat j) = Some (Vint (nth j (sigall_regs T E ix) Int.zero))) /\
    Mem.load Mint64 m' bD (oD + 48) = Some (Vlong ix) /\
    (forall ch b ofs, Mem.valid_block m b -> (b <> bD \/ ofs + size_chunk ch <= oD \/ oD + 56 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HoD HaD PD Hotx HT Hotap HE Hdisp HMax.
  set (vdst := Vptr bD (Ptrofs.repr oD)). set (vtx := Vptr btx (Ptrofs.repr otx)).
  set (vtap := Vptr btap (Ptrofs.repr otap)).
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (VD : Mem.valid_block m bD) by (eapply Mem.perm_valid_block; apply (PD oD); lia).
  assert (Vtx : Mem.valid_block m btx) by (eapply load_valid_block; exact (HT 0%nat ltac:(lia))).
  assert (Vtap : Mem.valid_block m btap) by (eapply load_valid_block; exact (HE 0%nat ltac:(lia))).
  destruct (Mem.alloc m 0 56) as [ma1 bRes] eqn:A1.
  destruct (Mem.alloc ma1 0 88) as [ma2 bC] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [m0 bR] eqn:A3.
  assert (HAL : alloc_list m [56; 88; 88] = (m0, [bRes; bC; bR])).
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
  destruct (Fresh bD VD) as (NDRes & NDC & NDR).
  destruct (Fresh btx Vtx) as (NtxRes & NtxC & NtxR). destruct (Fresh btap Vtap) as (NtapRes & NtapC & NtapR).
  set (e := bt_env bRes bC bR).
  set (le := bt_le vdst vtx vtap ix).
  assert (HeRes : e!_result = Some (bRes, TXE)) by reflexivity.
  assert (HeC : e!_ctx = Some (bC, CTX)) by reflexivity.
  assert (HeR : e!__res__1 = Some (bR, CTX)) by reflexivity.
  assert (EvRes : forall lx mx, eval_expr sha_ge e lx mx RES (Vptr bRes Ptrofs.zero)).
  { intros lx mx. eapply eval_Elvalue; [apply eval_Evar_local; exact HeRes|apply deref_loc_copy; reflexivity]. }
  assert (EvSig : forall lx mx, eval_expr sha_ge e lx mx SIGALL (Vptr bRes (Ptrofs.repr 16))).
  { intros lx mx. pose proof (eval_envu_field_struct e lx mx RES _txEnv _sigAllHash 16 _sha256_midstate
      bRes Ptrofs.zero eq_refl envu_txEnv_sigAllHash (EvRes lx mx)) as HEv.
    rewrite Ptrofs.add_zero_l in HEv. exact HEv. }
  (* result.tx, result.taproot, the zeroed midstate, result.ix *)
  destruct (Mem.valid_access_store m0 Mptr bRes 0 vtx) as [m1 S1].
  { split; [|exists 0; reflexivity]. intros o Ho. change (size_chunk Mptr) with 8 in Ho.
    eapply Mem.perm_implies; [apply PRes0; lia|constructor]. }
  destruct (Mem.valid_access_store m1 Mptr bRes 8 vtap) as [m2 S2].
  { split; [|exists 1; reflexivity]. intros o Ho. change (size_chunk Mptr) with 8 in Ho.
    eapply Mem.perm_store_1; [exact S1|]. eapply Mem.perm_implies; [apply PRes0; lia|constructor]. }
  assert (P2 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m2 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|exact Hp]. }
  destruct (store_words_exists (repeat Int.zero 8) m2 bRes 16) as [m3 SW].
  { rewrite repeat_length. intros o Ho. eapply Mem.perm_implies; [apply P2, PRes0; cbn in Ho; lia|constructor]. }
  { exists 4. reflexivity. }
  assert (P3 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. apply (store_words_perm _ _ _ _ _ SW). apply P2, Hp. }
  destruct (Mem.valid_access_store m3 Mint64 bRes 48 (Vlong ix)) as [m4 S4].
  { split; [|exists 6; reflexivity]. intros o Ho. change (size_chunk Mint64) with 8 in Ho.
    eapply Mem.perm_implies; [apply P3, PRes0; lia|constructor]. }
  assert (P4 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S4|]. apply P3, Hp. }
  assert (V4 : forall b, Mem.valid_block m0 b -> Mem.valid_block m4 b).
  { intros b Hb. eapply Mem.store_valid_block_1; [exact S4|]. unfold Mem.valid_block.
    rewrite (store_words_nextblock _ _ _ _ _ SW).
    eapply Mem.store_valid_block_1; [exact S2|]. eapply Mem.store_valid_block_1; [exact S1|exact Hb]. }
  assert (L4 : forall ch b ofs, b <> bRes -> Mem.load ch m4 b ofs = Mem.load ch m0 b ofs).
  { intros ch b ofs Hb. rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by (left; exact Hb).
    rewrite (store_words_load_other _ _ _ _ _ SW) by (left; exact Hb).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (left; exact Hb).
    apply (Mem.load_store_other _ _ _ _ _ _ S1). left. exact Hb. }
  assert (R0 : Mem.load Mptr m4 bRes 0 = Some vtx).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by (right; left; cbn; lia).
    rewrite (store_words_load_other _ _ _ _ _ SW) by (right; left; cbn; lia).
    rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (right; left; cbn; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ S1). reflexivity. }
  assert (R8 : Mem.load Mptr m4 bRes 8 = Some vtap).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ S4) by (right; left; cbn; lia).
    rewrite (store_words_load_other _ _ _ _ _ SW) by (right; left; cbn; lia).
    rewrite (Mem.load_store_same _ _ _ _ _ _ S2). reflexivity. }
  assert (R48 : Mem.load Mint64 m4 bRes 48 = Some (Vlong ix)).
  { rewrite (Mem.load_store_same _ _ _ _ _ _ S4). reflexivity. }
  assert (Kold4 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. rewrite L4 by (apply (Fresh b Hb)). apply XL, Hb. }
  (* sha256_init(result.sigAllHash.s) *)
  destruct (ctxo_init bC bRes 16 NResC NGC NGRes NMC NMRes
              ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) m4 bR
              (not_eq_sym NResR) (not_eq_sym NCR) ltac:(exists 4; reflexivity)
              (V4 _ (XV _ VG)) (V4 _ (XV _ VM)) NGR NMR)
    as (mi & m5 & bytes & HInit & HLB & HSB & HC0 & HL5 & HP5 & HV5).
  { intros o Ho. apply P4, PR0, Ho. }
  { intros o Ho. apply P4, PC0, Ho. }
  { intros o Ho. eapply Mem.perm_implies; [apply P4, PRes0; lia|constructor]. }
  { unfold sha_dispatch_ok. rewrite Kold4 by exact VG. exact Hdisp. }
  { rewrite Kold4 by exact VM. exact HMax. }
  assert (HSep : ctxs_sep bRes [(bC, 16, [], sha256_iv_words, Int64.zero, false)]).
  { apply ctxs_sep_cons; cbn [ctx_block ctx_out];
      [apply ctxs_sep_nil; assumption|exact (not_eq_sym NResC)|exact NGC|exact NMC|lia
      |change Ptrofs.max_unsigned with 18446744073709551615; lia|intros c []]. }
  assert (HLive : ctxs_live m5 bRes [(bC, 16, [], sha256_iv_words, Int64.zero, false)] (fun _ => True)).
  { intros j cj Hj _. destruct j as [|j]; cbn in Hj; [injection Hj as <-; exact HC0|destruct j; discriminate]. }
  pose proof (LS_intro m5 bRes _ (fun _ : nat => True) HSep HLive) as HLS5. cbn [map core_of] in HLS5.
  assert (Kold5 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m5 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (Fresh b Hb) as (F1 & F2 & F3).
    rewrite HL5; [apply Kold4, Hb|apply V4, XV, Hb|exact F3|exact F2|left; exact F1]. }
  (* sha256_hash(&ctx, &tx->txHash) *)
  set (oT := Ptrofs.repr (otx + 368)).
  assert (HoT : Ptrofs.unsigned oT = otx + 368) by (apply Ptrofs.unsigned_repr; lia).
  let cc := ls_cores HLS5 in
  destruct (LS_hash Hmodel bRes cc (fun _ : nat => True) 0%nat bC 16 _ _ _ eq_refl Logic.I m5 btx oT (norm8 T) HLS5 eq_refl)
    as (m6 & HCall6 & HLS6 & HF6).
  { rewrite HoT. lia. }
  { intros j Hj. rewrite HoT, norm8_nth by exact Hj. rewrite Kold5 by exact Vtx. apply HT, Hj. }
  cbn [upd] in HLS6.
  (* sha256_hash(&ctx, &taproot->tapEnvHash) *)
  set (oE := Ptrofs.repr (otap + 72)).
  assert (HoE : Ptrofs.unsigned oE = otap + 72) by (apply Ptrofs.unsigned_repr; lia).
  assert (Vold5 : forall b, Mem.valid_block m b -> Mem.valid_block m5 b) by (intros b Hb; apply HV5, V4, XV, Hb).
  assert (Kold6 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m6 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (Fresh b Hb) as (F1 & F2 & F3).
    rewrite (proj1 HF6); [apply Kold5, Hb|apply Vold5, Hb|split; [exact F2|left; exact F1]]. }
  let cc := ls_cores HLS6 in
  destruct (LS_hash Hmodel bRes cc (fun _ : nat => True) 0%nat bC 16 _ _ _ eq_refl Logic.I m6 btap oE (norm8 E) HLS6 eq_refl)
    as (m7 & HCall7 & HLS7 & HF7).
  { rewrite HoE. lia. }
  { intros j Hj. rewrite HoE, norm8_nth by exact Hj. rewrite Kold6 by exact Vtap. apply HE, Hj. }
  cbn [upd] in HLS7.
  (* sha256_u32be(&ctx, ix), sha256_finalize(&ctx) *)
  let cc := ls_cores HLS7 in
  destruct (LS_u32be Hmodel bRes cc (fun _ : nat => True) 0%nat bC 16 _ _ _ eq_refl Logic.I m7 ix HLS7)
    as (m8 & vr8 & HCall8 & HLS8 & HF8).
  cbn [upd] in HLS8.
  let cc := ls_cores HLS8 in
  destruct (LS_finalize Hmodel bRes cc (fun _ : nat => True) 0%nat bC 16 _ _ _ eq_refl Logic.I m8 HLS8)
    as (m9 & vr9 & HCall9 & HReg9 & _ & HF9).
  change (forall i, (i < 8)%nat ->
    Mem.load Mint32 m9 bRes (16 + 4 * Z.of_nat i) = Some (Vint (nth i (sigall_regs T E ix) Int.zero))) in HReg9.
  pose proof (mfrP_trans _ _ _ _ (mfrP_trans _ _ _ _ (mfrP_trans _ _ _ _ HF6 HF7) HF8) HF9) as (L9 & P9 & V9).
  assert (VRes5 : Mem.valid_block m5 bRes) by (apply HV5, V4, VRes0).
  assert (LRes9 : forall ch ofs, (ofs + size_chunk ch <= 16 \/ 48 <= ofs) ->
    Mem.load ch m9 bRes ofs = Mem.load ch m4 bRes ofs).
  { intros ch ofs Hr. rewrite L9; [|exact VRes5|split; [exact NResC|right; lia]].
    apply HL5; [apply V4, VRes0|exact NResR|exact NResC|right; lia]. }
  assert (Kold9 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m9 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (Fresh b Hb) as (F1 & F2 & F3).
    rewrite L9; [apply Kold5, Hb|apply Vold5, Hb|split; [exact F2|left; exact F1]]. }
  assert (Pall9 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m9 b ofs k p).
  { intros b ofs k p Hp. apply P9, HP5, P4, Hp. }
  (* *_res = result *)
  destruct (Mem.range_perm_loadbytes m9 bRes 0 56) as (cb & HCB).
  { intros o Ho. eapply Mem.perm_implies; [apply Pall9, PRes0, Ho|constructor]. }
  pose proof (Mem.loadbytes_length _ _ _ _ _ HCB) as HCBL.
  destruct (Mem.range_perm_storebytes m9 bD oD cb) as (m10 & SG).
  { rewrite HCBL. change (Z.of_nat (Z.to_nat 56)) with 56. intros o Ho. apply Pall9, XP, PD, Ho. }
  assert (HGB : Mem.loadbytes m10 bD oD 56 = Some cb).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ SG) as H. rewrite HCBL in H. exact H. }
  assert (Pall10 : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m10 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_storebytes_1; [exact SG|apply Pall9, Hp]. }
  (* freeing the locals *)
  destruct (free_list_blocks (bt_block_list bRes bC bR) m10) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn ofs Hr. apply Pall10. cbn [bt_block_list In] in HIn.
    repeat (destruct HIn as [E0'|HIn]; [injection E0' as <- <- <-; first [apply PRes0|apply PC0|apply PR0]; exact Hr|]).
    contradiction. }
  { cbn [bt_block_list map fst].
    repeat (apply NoDup_cons;
      [let HIn := fresh in intro HIn; cbn [In] in HIn;
       repeat (destruct HIn as [HIn|HIn]; [first [exact (NResC HIn)|exact (NResR HIn)|exact (NCR HIn)
         |exact (NResC (eq_sym HIn))|exact (NResR (eq_sym HIn))|exact (NCR (eq_sym HIn))]|]); exact HIn|]).
    apply NoDup_nil. }
  cbn [bt_block_list map fst] in HLf, HPf.
  assert (NDl : ~ In bD [bC; bRes; bR] /\ ~ In bD [bRes; bC; bR]).
  { split; intros HIn; cbn [In] in HIn; repeat (destruct HIn as [HIn|HIn]; [congruence|]); exact HIn. }
  assert (LDf : forall ch ofs, Mem.load ch mf bD ofs = Mem.load ch m10 bD ofs).
  { intros ch ofs. apply HLf. intros HIn. cbn [In] in HIn.
    repeat (destruct HIn as [HIn|HIn]; [congruence|]). exact HIn. }
  exists mf. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
  - eapply eval_funcall_internal with (e := e) (m1 := m0) (m2 := m10) (out := Out_return None).
    + apply bt_entry with (m1 := ma1) (m2 := ma2); assumption.
    + rewrite bt_body_shape.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
      { eapply exec_Sassign with (v2 := vtx) (v := vtx).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_txEnv_tx|apply EvRes].
        - apply eval_Etempvar. reflexivity.
        - reflexivity.
        - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite mt_off by lia. exact S1. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2).
      { eapply exec_Sassign with (v2 := vtap) (v := vtap).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_txEnv_taproot|apply EvRes].
        - apply eval_Etempvar. reflexivity.
        - reflexivity.
        - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite mt_off by lia. exact S2. }
      eapply (zrr_exec e bRes SIGALL 16 bt_rest EvSig eq_refl ltac:(lia) 8 0 le m2 m3); [lia|exact SW|].
      cbv delta [bt_rest] beta iota.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m4).
      { eapply exec_Sassign with (v2 := Vlong ix) (v := Vlong ix).
        - eapply eval_envu_field_lvalue; [reflexivity|exact envu_txEnv_ix|apply EvRes].
        - apply eval_Etempvar. reflexivity.
        - reflexivity.
        - eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite mt_off by lia. exact S4. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m5).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi).
        - pose proof (eval_envu_field_array e le m4 SIGALL _sha256_midstate _s 0 A8 bRes (Ptrofs.repr 16)
            eq_refl envu_sha256_midstate_s ltac:(intros chunk; discriminate) eq_refl (EvSig le m4)) as HEv.
          rewrite Ptrofs.add_zero in HEv.
          exact (te_call_init e le m4 mi __res__1 (Efield SIGALL _s A8) bR bRes (Ptrofs.repr 16)
                   eq_refl HeR HEv eq_refl HInit).
        - exact (exec_ctx_struct_copy e le mi m5 _ctx __res__1 bC bR bytes HeC HeR NCR HLB HSB). }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m6).
      { eapply mt_call_hash with (bx := bC) (bt := btx) (ot := oT); [reflexivity|exact HeC| |reflexivity|exact HCall6].
        unfold oT. eapply ev_adr; [reflexivity|exact envu_tx_txHash| |lia|lia|lia].
        apply eval_envu_deref_struct. reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m7).
      { eapply mt_call_hash with (bx := bC) (bt := btap) (ot := oE); [reflexivity|exact HeC| |reflexivity|exact HCall7].
        unfold oE. eapply ev_adr; [reflexivity|exact envu_bitcoinTapEnv_tapEnvHash| |lia|lia|lia].
        apply eval_envu_deref_struct. reflexivity. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m8).
      { eapply mt_call_u32be with (bx := bC) (x := ix);
          [reflexivity|exact HeC|apply eval_Etempvar; reflexivity|reflexivity|exact HCall8]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m9).
      { eapply mt_call_finalize; [reflexivity|exact HeC|exact HCall9]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m10).
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
    apply (equal_loadbytes_field Mptr m9 m10 bRes bD 0 oD 56 0 cb vtx ltac:(clear; lia) ltac:(change (size_chunk Mptr) with 8; clear; lia) HCB HGB).
    + rewrite Z.add_0_r. exact HaD.
    + rewrite Z.add_0_l, LRes9 by (left; change (size_chunk Mptr) with 8; clear; lia). exact R0.
  - rewrite LDf.
    apply (equal_loadbytes_field Mptr m9 m10 bRes bD 0 oD 56 8 cb vtap ltac:(clear; lia) ltac:(change (size_chunk Mptr) with 8; clear; lia) HCB HGB).
    + destruct HaD as [k Hk]. exists (k + 1). change (align_chunk Mptr) with 8. clear - Hk. lia.
    + rewrite Z.add_0_l, LRes9 by (left; change (size_chunk Mptr) with 8; clear; lia). exact R8.
  - intros j Hj. rewrite LDf. replace (oD + 16 + 4 * Z.of_nat j) with (oD + (16 + 4 * Z.of_nat j)) by lia.
    apply (equal_loadbytes_field Mint32 m9 m10 bRes bD 0 oD 56 (16 + 4 * Z.of_nat j) cb _
             ltac:(clear; lia) ltac:(change (size_chunk Mint32) with 4; clear - Hj; lia) HCB HGB).
    + destruct HaD as [k Hk]. exists (2 * k + 4 + Z.of_nat j). change (align_chunk Mint32) with 4. clear - Hk. lia.
    + rewrite Z.add_0_l. apply HReg9, Hj.
  - rewrite LDf.
    apply (equal_loadbytes_field Mint64 m9 m10 bRes bD 0 oD 56 48 cb (Vlong ix) ltac:(clear; lia) ltac:(change (size_chunk Mint64) with 8; clear; lia) HCB HGB).
    + destruct HaD as [k Hk]. exists (k + 6). change (align_chunk Mint64) with 8. clear - Hk. lia.
    + rewrite Z.add_0_l, LRes9 by (right; clear; lia). exact R48.
  - intros ch b ofs Hb Hr. destruct (Fresh b Hb) as (F1 & F2 & F3).
    rewrite HLf by (intros HIn; cbn [In] in HIn; repeat (destruct HIn as [HIn|HIn]; [congruence|]); exact HIn).
    rewrite (Mem.load_storebytes_other _ _ _ _ _ SG);
      [apply Kold9, Hb|rewrite HCBL; change (Z.of_nat (Z.to_nat 56)) with 56; exact Hr].
  - intros b ofs k p Hp. pose proof (Fresh b (Mem.perm_valid_block _ _ _ _ _ Hp)) as (F1 & F2 & F3).
    apply HPf; [|apply Pall10, XP, Hp].
    intros HIn; cbn [In] in HIn; repeat (destruct HIn as [HIn|HIn]; [congruence|]); exact HIn.
  - intros b Hb. apply HVf. eapply Mem.storebytes_valid_block_1; [exact SG|]. apply V9, Vold5, Hb.
Qed.
