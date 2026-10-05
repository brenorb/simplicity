(** The jet sha_256_ctx_8_finalize of the SHA translation unit against the
    literal ctx8Finalize program.  Partial (assertion) contract; conditional
    on the explicit [memcpy_model], with the state premise [sha_globals_ok]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_partial.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_bitmachine_rep.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks C.jet_uint32_array_init.
Require Import C.jet_write32s_layout C.jet_write_sha256_context_layout.
Require Import C.jet_read_sha256_counter C.jet_read_sha256_overflow C.jet_sha256_counter_representation.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_read_context_layout C.jet_sha_ctx8_bridge.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_finalize_exec C.jet_sha_finalize_spec C.jet_sha_finalize_bridge.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition fz_env (bl bm bx : block) : env :=
  PTree.set _ctx (bx, CTX) (PTree.set _midstate (bm, MID) (PTree.set _src (bl, FR) empty_env)).

Definition fz_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_sha_256_ctx_8_finalize)))).

Definition fz_read : statement :=
  Ssequence
    (Scall (Some _t'1) (Evar _simplicity_read_sha256_context
        (Tfunction (Tcons CTXP (Tcons FRP Tnil)) tbool cc_default))
      [Eaddrof (Evar _ctx CTX) CTXP; Eaddrof (Evar _src FR) FRP])
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip).
Definition fz_finalize : statement :=
  Scall None (Evar _sha256_finalize (Tfunction (Tcons CTXP Tnil) tbool cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP].
Definition fz_write : statement :=
  Scall None (Evar _write32s (Tfunction (Tcons FRP (Tcons (tptr tuint) (Tcons tulong Tnil))) tvoid cc_default))
    [Etempvar _dst FRP; Efield (Evar _midstate MID) _s (tarray tuint 8); Econst_int (Int.repr 8) tint].
Definition fz_rest : statement :=
  Ssequence fz_read (Ssequence fz_finalize
    (Ssequence fz_write (Sreturn (Some (Econst_int (Int.repr 1) tint))))).

Lemma fz_body :
  fn_body f_simplicity_sha_256_ctx_8_finalize =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR)) (an_init fz_rest).
Proof. reflexivity. Qed.

Lemma fz_blocks bl bm bx :
  blocks_of_env sha_ge (fz_env bl bm bx) = [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32)].
Proof. vm_compute. reflexivity. Qed.

Lemma fz_write32s_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _write32s = Some (sha_symbol_block _write32s).
Proof. vm_compute; reflexivity. Qed.
Lemma fz_write32s_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _write32s) Ptrofs.zero) =
    Some (Internal jets.f_write32s).
Proof. vm_compute; reflexivity. Qed.

Lemma fz_entry env m m1 m2 m3 bl bm bx bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) -> Mem.alloc m2 0 88 = (m3, bx) ->
  function_entry2 sha_ge f_simplicity_sha_256_ctx_8_finalize
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (fz_env bl bm bx) (fz_temps env bd dbase bs sbase) m3.
Proof.
  intros HA HB HC. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl).
    + change (Mem.alloc m 0 16 = (m1, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := m2) (b1 := bm).
      * change (Mem.alloc m1 0 32 = (m2, bm)); exact HB.
      * eapply alloc_variables_cons with (m1 := m3) (b1 := bx).
        -- change (Mem.alloc m2 0 88 = (m3, bx)); exact HC.
        -- constructor.
  - reflexivity.
Qed.

Lemma fz_copy m mc bl bm bx bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (fz_env bl bm bx) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
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

Local Opaque sha_ge ge0.

Lemma sg_in_write32s : In (jets._write32s, jets.f_write32s) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.

Lemma state_regs_cells (h : Ty.tySem (Word 8)) : uint32_word_cells (state_regs h) = encode h.
Proof.
  unfold state_regs. rewrite uint32_word_cells_encode. symmetry. apply (word32_chunks_encode 3).
Qed.

Lemma frame_input_cells_valid m bi edge rc (cells : list Cell) :
  cells <> [] -> frame_input_cells_at m bi edge rc cells -> Mem.valid_block m bi.
Proof.
  intros Hne HC. destruct cells as [|c0 cells]; [contradiction|].
  pose proof (HC 0%nat c0 eq_refl) as H0. destruct c0 as [bit|]; cbn [cell_matches] in H0.
  - destruct H0 as [_ [_ [w [HL _]]]]. eapply load_valid_block; exact HL.
  - destruct H0 as [bit [_ [_ [w [HL _]]]]]. eapply load_valid_block; exact HL.
Qed.

Theorem sha_256_ctx_8_finalize_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_finalize sha256_ctx8_type (Word 8)
    (fun a => @ctx8_finalize_spec optalg a).
Proof.
  intros Hmodel env m bd dbase bs sbase bi bw edge outedge cursor rc [buf [count state]]
    [Hdisp HMaxC] HSbase HSAlign [HSE HSO] H0 Hmax Hin Hout.
  rewrite sha256_ctx8_type_bits in Hmax. change (Z.of_nat 830) with 830 in Hmax.
  change (Z.of_nat (bitSize (Word 8))) with 256 in *.
  change (frame_input_cells_at m bi edge rc (encode buf ++ encode count ++ encode state)) in Hin.
  cbv beta.
  match goal with |- context[jet_partial_return ?sp] => set (spec := sp) end.
  set (G := sha_symbol_block _simplicity_sha256_compression) in *.
  set (MAXC := sha_symbol_block _sha256_max_counter) in *.
  set (lbuf := byte_chunks_values (buffer_byte_chunks 5 buf)).
  pose proof (sha256_buffer63_length_range buf) as Hlbuf. fold lbuf in Hlbuf.
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (VG : Mem.valid_block m G) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m MAXC) by (eapply load_valid_block; exact HMaxC).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 256 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (Vi : Mem.valid_block m bi).
  { eapply frame_input_cells_valid; [|exact Hin]. intro HN.
    apply (f_equal (@length Cell)) in HN. rewrite !app_length, !encode_length in HN. cbn in HN. lia. }
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hbyteslen.
  (* locals *)
  destruct (Mem.alloc m 0 16) as [ma1 bl] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 bm] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [m0 bx] eqn:A3.
  pose proof (mext_alloc _ _ _ _ _ A1) as X1. pose proof (mext_alloc _ _ _ _ _ A2) as X2.
  pose proof (mext_alloc _ _ _ _ _ A3) as X3.
  assert (X : mext m m0) by (eapply mext_trans; [exact X1|eapply mext_trans; eassumption]).
  destruct X as (XV & XL & XP & XA).
  assert (Fl : forall b0, Mem.valid_block m b0 -> b0 <> bl).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Fm : forall b0, Mem.valid_block m b0 -> b0 <> bm).
  { intros b0 Hv Heq. subst b0. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). apply (proj1 X1). exact Hv. }
  assert (Fx : forall b0, Mem.valid_block m b0 -> b0 <> bx).
  { intros b0 Hv Heq. subst b0. apply (Mem.fresh_block_alloc _ _ _ _ _ A3).
    apply (proj1 X2). apply (proj1 X1). exact Hv. }
  assert (Hlm : bl <> bm).
  { intro Heq. subst bm. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). eapply Mem.valid_new_block; exact A1. }
  assert (Hlx : bl <> bx).
  { intro Heq. subst bx. apply (Mem.fresh_block_alloc _ _ _ _ _ A3). apply (proj1 X2).
    eapply Mem.valid_new_block; exact A1. }
  assert (Hmx : bm <> bx).
  { intro Heq. subst bx. apply (Mem.fresh_block_alloc _ _ _ _ _ A3). eapply Mem.valid_new_block; exact A2. }
  assert (PL0 : Mem.range_perm m0 bl 0 16 Cur Freeable).
  { intros ofs Hr. apply (proj1 (proj2 (proj2 X3))). apply (proj1 (proj2 (proj2 X2))).
    eapply Mem.perm_alloc_2; eauto. }
  assert (PM0 : Mem.range_perm m0 bm 0 32 Cur Freeable).
  { intros ofs Hr. apply (proj1 (proj2 (proj2 X3))). eapply Mem.perm_alloc_2; eauto. }
  assert (PX0 : Mem.range_perm m0 bx 0 88 Cur Freeable).
  { intros ofs Hr. eapply Mem.perm_alloc_2; eauto. }
  set (e := fz_env bl bm bx).
  set (le0 := fz_temps env bd dbase bs sbase).
  (* the frame copy *)
  assert (HB0 : Mem.loadbytes m0 bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [|exact A3|apply (proj1 X2); apply (proj1 X1); exact Vs].
    erewrite Mem.loadbytes_alloc_unchanged; [|exact A2|apply (proj1 X1); exact Vs].
    erewrite Mem.loadbytes_alloc_unchanged; [exact HB|exact A1|exact Vs]. }
  assert (PLW : Mem.range_perm m0 bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm m0 bl 0 16 Cur Writable).
    intros ofs Hr. eapply Mem.perm_implies; [apply PL0; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m0 bl 0 bytes PLW) as [mcp SC].
  assert (HSE0 : Mem.load Mptr m0 bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSO0 : Mem.load Mint64 m0 bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_copy_fields_at m0 mcp bs sbase bl bytes _ _ HB0 SC HSE0 HSO0) as [HLE HLO].
  assert (Kc : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mcp b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. erewrite Mem.load_storebytes_other; [|exact SC|left; apply Fl; exact Hv].
    apply XL. exact Hv. }
  assert (Pc : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm mcp b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; eauto. }
  assert (Vc : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block mcp b0).
  { intros b0 Hv. eapply Mem.storebytes_valid_block_1; eauto. }
  (* initialisation *)
  destruct (an_init_exec e bx bm eq_refl eq_refl le0 mcp
    ltac:(intros ofs Hr; apply Pc; eapply Mem.perm_implies; [apply PX0; exact Hr|constructor]))
    as (m1 & HInitEx & HOut1 & (L1 & P1 & V1)).
  assert (K1 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m1 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. rewrite L1 by (left; apply Fx; exact Hv). apply Kc. exact Hv. }
  assert (Q1 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m1 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply P1, Pc, Hp. }
  assert (W1 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m1 b0).
  { intros b0 Hv. apply V1, Vc, XV, Hv. }
  assert (Vl1 : Mem.valid_block m1 bl).
  { apply V1, Vc. apply (proj1 X3). apply (proj1 X2). eapply Mem.valid_new_block; exact A1. }
  assert (Vm1 : Mem.valid_block m1 bm).
  { apply V1, Vc. apply (proj1 X3). eapply Mem.valid_new_block; exact A2. }
  assert (Vx1 : Mem.valid_block m1 bx) by (apply V1, Vc; eapply Mem.valid_new_block; exact A3).
  (* the context reader *)
  destruct (Mem.alloc m1 0 8) as [ma bq] eqn:AL.
  pose proof (mext_alloc _ _ _ _ _ AL) as (YV & YL & YP & YA).
  assert (Fq : forall b0, Mem.valid_block m1 b0 -> b0 <> bq).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ AL Hv). }
  assert (PXa : Mem.range_perm ma bx 0 88 Cur Freeable).
  { intros ofs Hr. apply YP, Q1, PX0, Hr. }
  assert (PMa : Mem.range_perm ma bm 0 32 Cur Freeable).
  { intros ofs Hr. apply YP, Q1, PM0, Hr. }
  assert (PLa : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hr. apply YP, Q1, PL0, Hr. }
  assert (Ka : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch ma b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. rewrite YL by (apply W1; exact Hv). apply K1. exact Hv. }
  assert (R4 : Mem.range_perm ma bx (0 + 16) (0 + 79) Cur Writable).
  { intros ofs Hr. eapply Mem.perm_implies with (p1 := Freeable); [apply PXa; lia|constructor]. }
  assert (R5 : Mem.valid_access ma Mint64 bx (0 + 8) Writable).
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies with (p1 := Freeable); [apply PXa; lia|constructor]. }
  assert (R6 : Mem.valid_access ma Mint8unsigned bx (0 + 80) Writable).
  { split; [|exists 80; reflexivity]. intros ofs Hr. change (size_chunk Mint8unsigned) with 1 in Hr.
    eapply Mem.perm_implies with (p1 := Freeable); [apply PXa; lia|constructor]. }
  assert (R7 : Mem.load Mptr ma bx 0 = Some (Vptr bm (Ptrofs.repr 0))).
  { rewrite YL by exact Vx1. exact HOut1. }
  assert (R11 : Mem.range_perm ma bm 0 (0 + 32) Cur Writable).
  { intros ofs Hr. eapply Mem.perm_implies with (p1 := Freeable); [apply PMa; lia|constructor]. }
  assert (R26 : Mem.load Mint64 ma MAXC 0 = Some (Vlong (Int64.repr 2305843009213693952))).
  { rewrite Ka by exact VM. exact HMaxC. }
  assert (HLE1 : Mem.load Mptr ma bl 0 = Some (Vptr bi (Ptrofs.repr edge))).
  { rewrite YL by exact Vl1. rewrite L1 by (left; exact Hlx). exact HLE. }
  assert (HLO1 : Mem.load Mint64 ma bl 8 = Some (Vlong (Int64.repr rc))).
  { rewrite YL by exact Vl1. rewrite L1 by (left; exact Hlx). exact HLO. }
  assert (R31 : Mem.valid_access ma Mint64 bl (0 + 8) Writable).
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies with (p1 := Freeable); [apply PLa; lia|constructor]. }
  assert (R32 : frame_input_cells_at ma bi edge rc (encode buf ++ encode count ++ encode state)).
  { eapply buffer_input_cells_preserved; [|exact Hin]. intros ofs w HL. rewrite Ka by exact Vi. exact HL. }
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  destruct (sg_eval_read_sha256_context_allocated_layout m1 ma bl 0 bi edge rc bx 0 bq bm 0 buf count state
    AL ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) R4 R5 R6 R7
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(exists 0; reflexivity) R11
    Hlx (not_eq_sym (Fl bi Vi)) (not_eq_sym (Fx bi Vi))
    (not_eq_sym (Fq bl Vl1)) (not_eq_sym (Fq bx Vx1)) (not_eq_sym (Fq bi (W1 bi Vi)))
    (not_eq_sym Hlm) (not_eq_sym (Fm bi Vi)) Hmx (not_eq_sym (Fq bm Vm1))
    (not_eq_sym (Fl MAXC VM)) (not_eq_sym (Fx MAXC VM)) (not_eq_sym (Fq MAXC (W1 MAXC VM))) (not_eq_sym (Fm MAXC VM))
    R26 HLocalBase H0 ltac:(lia) (conj HLE1 HLO1) R31 R32)
    as (m2 & r & HRd & Hr & HOut2 & HArr2 & HSt2 & HCnt2 & HOvf2 & HFld2 & HMax2 & HPerm2 & HMem2 & HVal2).
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv.
    rewrite HMem2; [apply Ka; exact Hv|apply Fq, W1, Hv|left; apply Fl; exact Hv
                   |left; apply Fx; exact Hv|left; apply Fm; exact Hv]. }
  assert (W2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HVal2, YV, W1, Hv. }
  assert (HFree : forall m5,
    (forall b0 ofs kd p, b0 <> bq -> Mem.perm ma b0 ofs kd p -> Mem.perm m5 b0 ofs kd p) ->
    exists mf, Mem.free_list m5 [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32)] = Some mf /\
      (forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mf b0 ofs = Mem.load ch m5 b0 ofs)).
  { intros m5 HP5.
    destruct (free_list_blocks [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32)] m5) as (mf & HFL & HLf & _ & _).
    - intros b0 lo hi Hin0. cbn in Hin0.
      destruct Hin0 as [Heq|[Heq|[Heq|[]]]]; injection Heq as <- <- <-; intros ofs Hr0; apply HP5.
      + apply Fq; exact Vx1.
      + apply PXa; exact Hr0.
      + apply Fq; exact Vl1.
      + apply PLa; exact Hr0.
      + apply Fq; exact Vm1.
      + apply PMa; exact Hr0.
    - cbn. repeat constructor; cbn; intuition congruence.
    - exists mf. split; [exact HFL|]. intros ch b0 ofs Hv. apply HLf. cbn.
      intros [E|[E|[E|[]]]]; subst b0;
        [exact (Fx _ Hv eq_refl)|exact (Fl _ Hv eq_refl)|exact (Fm _ Hv eq_refl)]. }
  (* the specification *)
  assert (Hlist : lbuf = buffer_list (Word 3) 5 buf) by (apply buffer_values_list).
  pose proof (ctx8_finalize_closed buf count state) as HClosed. cbv zeta in HClosed.
  rewrite <- Hlist in HClosed. destruct HClosed as [HCa HCb].
  assert (HCallRead : forall v,
    Clight2.eval_funcall sha_ge m1 (Internal jets.f_simplicity_read_sha256_context)
      [Vptr bx Ptrofs.zero; Vptr bl Ptrofs.zero] E0 m2 v ->
    Clight2.exec_stmt sha_ge e le0 m1
      (Scall (Some _t'1) (Evar _simplicity_read_sha256_context
          (Tfunction (Tcons CTXP (Tcons FRP Tnil)) tbool cc_default))
        [Eaddrof (Evar _ctx CTX) CTXP; Eaddrof (Evar _src FR) FRP])
      E0 (PTree.set _t'1 v le0) m2 Out_normal).
  { intros v HC. change (PTree.set _t'1 v le0) with (set_opttemp (Some _t'1) v le0).
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_read_sha256_context) Ptrofs.zero)
      (vargs := [Vptr bx Ptrofs.zero; Vptr bl Ptrofs.zero]).
    - reflexivity.
    - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_read_context_symbol]|].
      apply deref_loc_reference; reflexivity.
    - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
      eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
    - exact an_read_context_funct.
    - reflexivity.
    - exact HC. }
  assert (HCopy : Clight2.exec_stmt sha_ge e le0 m0 (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le0 mcp Out_normal).
  { eapply fz_copy; [exact HSbase|exact HSAlign| |reflexivity|exact HB0|exact SC].
    intro Heq. apply (Fl bs Vs). congruence. }
  destruct (sha256_read_overflow r) eqn:Hovr.
  - (* the stored compression count is out of range *)
    apply sha256_read_overflow_true in Hovr.
    assert (HNone : spec = None)
      by (apply HCb; unfold ctx8_limit; rewrite <- Hr; lia).
    destruct (HFree m2 HPerm2) as (mf & HFL & HLf).
    exists mf. rewrite HNone. split; [|split; [exact I|]].
    + eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0)
        (le2 := PTree.set _t'1 (Vint (bit_int (negb true))) le0) (m2 := m2)
        (out := Out_return (Some (Vint (Int.repr 0), tint))).
      * eapply fz_entry; eassumption.
      * rewrite fz_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
        apply HInitEx. unfold fz_rest.
        eapply exec_Sseq_2; [|discriminate]. unfold fz_read.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply HCallRead. exact HRd.
        -- eapply exec_Sifthenelse with (b := true);
             [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
           apply exec_Sreturn_some. apply eval_Econst_int.
      * cbn. split; [discriminate|reflexivity].
      * unfold e. rewrite fz_blocks. exact HFL.
    + intros ch b0 ofs Hv Hd Hw. rewrite HLf by exact Hv. apply K2; exact Hv.
  - (* the reader succeeds *)
    apply sha256_read_overflow_false in Hovr.
    set (l := map word8_array_value lbuf).
    set (regs := state_regs state).
    set (cc := sha256_read_counter r (Int64.repr (Z.of_nat (length lbuf)))) in *.
    assert (Hll : length l = length lbuf) by (unfold l; apply map_length).
    assert (Hlr : length regs = 8%nat).
    { unfold regs, state_regs. rewrite map_length. apply (word32_chunks_length 3). }
    assert (HccU : Int64.unsigned cc = 64 * Int64.unsigned r + Z.of_nat (length lbuf)).
    { apply add_counter_c; [exact Hovr|exact Hlbuf]. }
    assert (Q2 : forall b0 ofs kd p, b0 <> bq -> Mem.perm ma b0 ofs kd p -> Mem.perm m2 b0 ofs kd p)
      by exact HPerm2.
    destruct (eval_sha256_finalize Hmodel m2 bx 0 bm 0 l regs cc false
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
      Hmx (Fx G VG) (Fm G VG) (Fx MAXC VM) (Fm MAXC VM) Hlr HOut2 HCnt2)
      as (m3 & HFin & HReg3 & HMem3 & HPerm3 & HVal3).
    { rewrite HccU, Hll. replace (64 * Int64.unsigned r + Z.of_nat (length lbuf)) with
        (Z.of_nat (length lbuf) + Int64.unsigned r * 64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    { exact HOvf2. }
    { intros i Hi. apply (u8_nth _ _ _ _ HArr2). exact Hi. }
    { intros i Hi. split.
      - apply (u32_nth m2 bm 0 regs HSt2). rewrite Hlr. exact Hi.
      - split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; lia].
        intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
        eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
        apply Q2; [apply Fq; exact Vm1|apply PMa; lia]. }
    { unfold sha_dispatch_ok. fold G. rewrite K2 by exact VG. exact Hdisp. }
    { exact HMax2. }
    { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
      apply Q2; [apply Fq; exact Vx1|apply PXa; lia]. }
    { exists 0. reflexivity. }
    assert (HT : @toZ (WordToZ 6) count < ctx8_limit) by (unfold ctx8_limit; rewrite <- Hr; exact Hovr).
    destruct (HCa HT) as (hf & HSpec0 & HRegsF).
    assert (HSpec : spec = Some hf) by exact HSpec0.
    assert (Hcc : Int64.repr (64 * @toZ (WordToZ 6) count + Z.of_nat (length lbuf)) = cc).
    { rewrite <- Hr, <- HccU. apply Int64.repr_unsigned. }
    rewrite Hcc in HRegsF. fold l regs in HRegsF. rewrite <- HRegsF in HReg3.
    assert (HlF : length (state_regs hf) = 8%nat).
    { unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
    assert (K3 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m3 b0 ofs = Mem.load ch m b0 ofs).
    { intros ch b0 ofs Hv.
      rewrite HMem3; [apply K2; exact Hv|apply W2; exact Hv|left; apply Fx; exact Hv|left; apply Fm; exact Hv]. }
    assert (Q3 : forall b0 ofs kd p, Mem.perm m b0 ofs kd p -> Mem.perm m3 b0 ofs kd p).
    { intros b0 ofs kd p Hp. assert (Hv : Mem.valid_block m b0) by (eapply Mem.perm_valid_block; exact Hp).
      apply HPerm3; [apply W2; exact Hv|]. apply Q2; [apply Fq, W1; exact Hv|]. apply YP, Q1, XP, Hp. }
    assert (HArr3 : uint32_array_at m3 bm 0 (state_regs hf)).
    { apply u32_of_nth. intros i Hi. apply HReg3. rewrite <- HlF. exact Hi. }
    assert (HOut3 : write_frame_at m3 bd dbase bw outedge cursor (32 * Z.of_nat (length (state_regs hf)))).
    { rewrite HlF. change (32 * Z.of_nat 8) with 256.
      eapply write_frame_at_preserved; [| |exact Hout].
      - intros ch b0 ofs v0 Hb HL. rewrite K3; [exact HL|destruct Hb; subst; assumption].
      - exact Q3. }
    destruct (eval_write32s_layout m3 bm 0 bd dbase bw outedge cursor (state_regs hf)
      ltac:(lia) ltac:(rewrite HlF; change Ptrofs.max_unsigned with 18446744073709551615; lia)
      (not_eq_sym (Fm bd Vd)) (not_eq_sym (Fm bw Vw)) HArr3 HOut3)
      as (m4 & HWr & HCells & HPrefix & HFldE & HLoadsE & HPermE & HValE).
    rewrite HlF in HWr, HFldE, HLoadsE. change (32 * Z.of_nat 8) with 256 in HFldE, HLoadsE.
    apply (sha_transport_call _ _ sg_in_write32s) in HWr.
    destruct (HFree m4) as (mf & HFL & HLf).
    { intros b0 ofs kd p Hb Hp. apply HPermE.
      apply HPerm3; [|apply Q2; assumption].
      eapply Mem.perm_valid_block. apply Q2; eassumption. }
    set (le2 := PTree.set _t'1 (Vint (bit_int (negb false))) le0).
    exists mf. rewrite HSpec. split; [|split].
    + eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le2) (m2 := m4)
        (out := Out_return (Some (Vint (Int.repr 1), tint))).
      * eapply fz_entry; eassumption.
      * rewrite fz_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
        apply HInitEx. unfold fz_rest.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
        { unfold fz_read. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
          - apply HCallRead. exact HRd.
          - eapply exec_Sifthenelse with (b := false);
              [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
            apply exec_Sskip. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
        { unfold fz_finalize.
          change le2 with (set_opttemp None (Vint (bit_int (negb false))) le2) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_finalize) Ptrofs.zero)
            (vargs := [Vptr bx Ptrofs.zero]) (f := Internal f_sha256_finalize).
          - reflexivity.
          - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_finalize_symbol]|].
            apply deref_loc_reference; reflexivity.
          - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
          - exact sha_finalize_funct.
          - reflexivity.
          - exact HFin. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m4).
        { unfold fz_write. change le2 with (set_opttemp None Vundef le2) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _write32s) Ptrofs.zero)
            (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bm Ptrofs.zero; Vlong (Int64.repr 8)])
            (f := Internal jets.f_write32s).
          - reflexivity.
          - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact fz_write32s_symbol]|].
            apply deref_loc_reference; reflexivity.
          - eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
            eapply eval_Econs; [apply eval_local_midstate_s; reflexivity|reflexivity|].
            eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
          - exact fz_write32s_funct.
          - reflexivity.
          - exact HWr. }
        apply exec_Sreturn_some. apply eval_Econst_int.
      * cbn. split; [discriminate|reflexivity].
      * unfold e. rewrite fz_blocks. exact HFL.
    + split; [|split].
      * rewrite <- state_regs_cells. eapply frame_output_cells_preserved; [|exact HCells].
        intros ofs w HL. rewrite HLf by exact Vw. exact HL.
      * eapply write_prefix_at_preserved; [| |exact HPrefix].
        -- intros ofs w HL. rewrite K3 by exact Vw. exact HL.
        -- intros ofs w HL. rewrite HLf by exact Vw. exact HL.
      * destruct HFldE as [HE1 HE2]. split; rewrite HLf by exact Vd; assumption.
    + intros ch b0 ofs Hv Hd Hw. rewrite HLf by exact Hv.
      rewrite HLoadsE by assumption. apply K3; exact Hv.
Qed.
