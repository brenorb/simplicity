(** The Bitcoin jet annex_hash against the literal annexHash program.
    Partial (assertion) contract; conditional on the explicit [memcpy_model],
    with the state premise [sha_globals_ok]. *)
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
Require Import C.jet_wide C.jet_wide_spec.
Require Import C.jet_write_sha256_context_layout C.jet_read_buffer8_511_layout.
Require Import C.jet_read_sha256_counter C.jet_read_sha256_overflow C.jet_sha256_counter_representation.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_read_context_layout C.jet_sha_ctx8_bridge.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_finalize_exec C.jet_sha_ctx8_finalize_jet C.jet_sha_add_buffer_spec.
Require Import C.jet_sha_ctx8_add_buffer_jet C.jet_sha_tapdata_prep C.jet_sha_tapdata_jet C.jet_bitcoin_ctx_hash_spec.
Require Import C.jet_sha_uchar_exec C.jet_sha_ctx_abs.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition ah_env (bl bm bb bx : block) : env :=
  PTree.set _ctx (bx, CTX) (PTree.set _buf (bb, tarray tuchar 32)
    (PTree.set _midstate (bm, MID) (PTree.set _src (bl, FR) empty_env))).

Definition ah_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_bitcoin_annex_hash)))).

Definition uchar_ty : type := Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default.

Definition ah_readbit : statement :=
  Scall (Some _t'2) (Evar _readBit (Tfunction (Tcons FRP Tnil) tbool cc_default)) [Eaddrof (Evar _src FR) FRP].
Definition ah_read8s : statement :=
  Scall None (Evar _read8s (Tfunction (Tcons (tptr tuchar) (Tcons tulong (Tcons FRP Tnil))) tvoid cc_default))
    [Evar _buf (tarray tuchar 32); Econst_int (Int.repr 32) tint; Eaddrof (Evar _src FR) FRP].
Definition ah_uchar (k : Z) : statement :=
  Scall None (Evar _sha256_uchar uchar_ty) [Eaddrof (Evar _ctx CTX) CTXP; Econst_int (Int.repr k) tint].
Definition ah_uchars : statement :=
  Scall None (Evar _sha256_uchars uchars_ty)
    [Eaddrof (Evar _ctx CTX) CTXP; Evar _buf (tarray tuchar 32); Econst_int (Int.repr 32) tint].
Definition ah_mid : statement :=
  Ssequence ah_readbit
    (Sifthenelse (Etempvar _t'2 tbool)
      (Ssequence ah_read8s (Ssequence (ah_uchar 1) ah_uchars)) (ah_uchar 0)).
Definition ah_write : statement :=
  Ssequence
    (Scall (Some _t'3) (Evar _simplicity_write_sha256_context
        (Tfunction (Tcons FRP (Tcons CTXP Tnil)) tbool cc_default))
      [Etempvar _dst FRP; Eaddrof (Evar _ctx CTX) CTXP])
    (Sreturn (Some (Etempvar _t'3 tbool))).
Definition ah_rest : statement := Ssequence fz_read (Ssequence ah_mid ah_write).

Lemma ah_body :
  fn_body f_simplicity_bitcoin_annex_hash =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR)) (an_init ah_rest).
Proof. reflexivity. Qed.

Lemma ah_blocks bl bm bb bx :
  blocks_of_env sha_ge (ah_env bl bm bb bx) = [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bb, 0, 32)].
Proof. vm_compute. reflexivity. Qed.

Lemma ah_entry env m m1 m2 m3 m4 bl bm bb bx bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) -> Mem.alloc m2 0 32 = (m3, bb) ->
  Mem.alloc m3 0 88 = (m4, bx) ->
  function_entry2 sha_ge f_simplicity_bitcoin_annex_hash
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (ah_env bl bm bb bx) (ah_temps env bd dbase bs sbase) m4.
Proof.
  intros HA HB HC HD. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact HA|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bm); [change (Mem.alloc m1 0 32 = (m2, bm)); exact HB|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bb); [change (Mem.alloc m2 0 32 = (m3, bb)); exact HC|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := bx); [change (Mem.alloc m3 0 88 = (m4, bx)); exact HD|].
    constructor.
  - reflexivity.
Qed.

Lemma ah_copy m mc bl bm bb bx bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (ah_env bl bm bb bx) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
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

Lemma ah_readBit_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _readBit = Some (sha_symbol_block _readBit).
Proof. vm_compute; reflexivity. Qed.
Lemma ah_readBit_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _readBit) Ptrofs.zero) =
    Some (Internal jets.f_readBit).
Proof. vm_compute; reflexivity. Qed.
Lemma ah_uchar_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_uchar = Some (sha_symbol_block _sha256_uchar).
Proof. vm_compute; reflexivity. Qed.
Lemma ah_uchar_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero) =
    Some (Internal f_sha256_uchar).
Proof. vm_compute; reflexivity. Qed.
Lemma ah_in_readBit : In (jets._readBit, jets.f_readBit) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.

Local Opaque sha_ge ge0.

Lemma ah_cast32 m :
  Cop.sem_cast (Vint (Int.repr 32)) tint tulong m = Some (Vlong (Int64.repr 32)).
Proof. vm_compute. reflexivity. Qed.
Lemma ah_cast0 m :
  Cop.sem_cast (Vint (Int.repr 0)) tint tuchar m = Some (Vint (word8_array_value byte_zero)).
Proof. vm_compute. reflexivity. Qed.
Lemma ah_cast1 m :
  Cop.sem_cast (Vint (Int.repr 1)) tint tuchar m = Some (Vint (word8_array_value byte_one)).
Proof. vm_compute. reflexivity. Qed.
Lemma ah_len n k : Z.of_nat n = k -> Int64.repr (Z.of_nat n) = Int64.repr k.
Proof. intro H. rewrite H. reflexivity. Qed.

(** Context facts survive steps that leave the context blocks and the two
    globals alone. *)
Lemma ctx_abs_other m m' bx bm l regs c ovf :
  ctx_abs m bx bm l regs c ovf ->
  (forall ch b ofs, b = bx \/ b = bm \/ b = GC \/ b = GM -> Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) ->
  ctx_abs m' bx bm l regs c ovf.
Proof.
  intros (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax) HL HP.
  split; [rewrite HL by tauto; exact HOut|]. split; [rewrite HL by tauto; exact HCnt|].
  split; [rewrite HL by tauto; exact HOvf|].
  split; [intros i Hi; rewrite HL by tauto; apply HBlk; exact Hi|].
  split; [intros i Hi; rewrite HL by tauto; apply HRegs; exact Hi|].
  split; [exact HMod|]. split; [exact HLen|]. split; [exact Hr|].
  split; [intros ofs Hr0; apply HP, PX, Hr0|]. split; [intros ofs Hr0; apply HP, PM, Hr0|].
  split; [unfold sha_dispatch_ok; rewrite HL by tauto; exact Hdisp|rewrite HL by tauto; exact HMax].
Qed.

(** Two successive additions to the counter agree with one. *)
Lemma ah_counter_two (r : int64) (len : Z) :
  Int64.unsigned r < 36028797018963968 -> 0 <= len < 64 ->
  let c := sha256_read_counter r (Int64.repr len) in
  Int64.add (Int64.add c (Int64.repr 1)) (Int64.repr 32) = Int64.add c (Int64.repr 33) /\
  uc_overflow (uc_overflow false c (Int64.repr 1)) (Int64.add c (Int64.repr 1)) (Int64.repr 32) =
    uc_overflow false c (Int64.repr 33).
Proof.
  intros Hr Hlen c. split; [rewrite Int64.add_assoc; reflexivity|].
  pose proof (Int64.unsigned_range r) as HR.
  pose proof (add_counter_c r len Hr Hlen) as HC. fold c in HC.
  pose proof (add_counter_sum r len 1 Hr Hlen ltac:(lia)) as HS. fold c in HS.
  unfold uc_overflow. cbn [orb]. rewrite !cmpu_le_bool.
  rewrite !long_sub_unsigned by
    (change (Int64.unsigned sha_max_counter) with 2305843009213693952; lia).
  change (Int64.unsigned sha_max_counter) with 2305843009213693952.
  change (Int64.unsigned (Int64.repr 1)) with 1. change (Int64.unsigned (Int64.repr 32)) with 32.
  change (Int64.unsigned (Int64.repr 33)) with 33. rewrite HS, HC.
  destruct (Z.leb_spec (2305843009213693952 - (64 * Int64.unsigned r + len)) 1);
    destruct (Z.leb_spec (2305843009213693952 - (64 * Int64.unsigned r + len + 1)) 32);
    destruct (Z.leb_spec (2305843009213693952 - (64 * Int64.unsigned r + len)) 33);
    cbn [orb]; try reflexivity; lia.
Qed.

Definition annex_bytes (a : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) : list (Ty.tySem (Word 3)) :=
  match a with
  | inl _ => [byte_zero]
  | inr h => byte_one :: vector_values (Word 3) 5 h
  end.
Definition annex_count (a : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) : Z :=
  match a with inl _ => 1 | inr _ => 33 end.
Definition annex_bit (a : Ty.tySem (Ty.Sum Ty.Unit (Word 8))) : bool :=
  match a with inl _ => false | inr _ => true end.

Lemma annex_bytes_length a : Z.of_nat (length (annex_bytes a)) = annex_count a.
Proof.
  destruct a as [u|h]; [reflexivity|]. unfold annex_bytes, annex_count. cbn [length].
  rewrite vector_values_length. reflexivity.
Qed.

Theorem bitcoin_annex_hash_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_bitcoin_annex_hash
    (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))) sha256_ctx8_type
    (fun a => @annex_hash_spec optalg a).
Proof.
  intros Hmodel env m bd dbase bs sbase bi bw edge outedge cursor rc [[buf [count state]] a]
    [Hdisp HMaxC] HSbase HSAlign [HSE HSO] H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod sha256_ctx8_type (Ty.Sum Ty.Unit (Word 8))))) with 1087 in Hmax.
  rewrite sha256_ctx8_type_bits in *. change (Z.of_nat 830) with 830 in *.
  change (frame_input_cells_at m bi edge rc
    ((encode buf ++ encode count ++ encode state) ++ @encode (Ty.Sum Ty.Unit (Word 8)) a)) in Hin.
  cbv beta.
  match goal with |- context[jet_partial_return ?sp] => set (spec := sp) end.
  set (G := sha_symbol_block _simplicity_sha256_compression) in *.
  set (MAXC := sha_symbol_block _sha256_max_counter) in *.
  set (lbuf := byte_chunks_values (buffer_byte_chunks 5 buf)).
  pose proof (sha256_buffer63_length_range buf) as Hlbuf. fold lbuf in Hlbuf.
  set (vs := annex_bytes a).
  set (nvs := annex_count a).
  assert (Hnvs : Z.of_nat (length vs) = nvs) by apply annex_bytes_length.
  assert (HnR : 0 <= nvs <= 4096) by (unfold nvs, annex_count; destruct a; lia).
  apply frame_input_cells_at_app in Hin. destruct Hin as [HinC HinB].
  rewrite !app_length, !encode_length in HinB.
  change (Z.of_nat (bitSize (buffer_type (Word 3) 5) + (bitSize (Word 6) + bitSize (Word 8)))) with 830 in HinB.
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (VG : Mem.valid_block m G) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m MAXC) by (eapply load_valid_block; exact HMaxC).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 830 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (Vi : Mem.valid_block m bi).
  { eapply frame_input_cells_valid; [|exact HinC]. intro HN.
    apply (f_equal (@length Cell)) in HN. rewrite !app_length, !encode_length in HN. cbn in HN. lia. }
  (* locals *)
  destruct (Mem.alloc m 0 16) as [ma1 bl] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 bm] eqn:A2.
  destruct (Mem.alloc ma2 0 32) as [ma3 bb] eqn:A3.
  destruct (Mem.alloc ma3 0 88) as [m0 bx] eqn:A5.
  assert (HAL : alloc_list m [16; 32; 32; 88] = (m0, [bl; bm; bb; bx])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A5. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  assert (FR5 : forall b0, Mem.valid_block m b0 -> b0 <> bl /\ b0 <> bm /\ b0 <> bb /\ b0 <> bx).
  { intros b0 Hv. pose proof (FRh b0 Hv) as HN. cbn in HN. repeat split; intro; subst; apply HN; tauto. }
  inversion FA as [|? ? ? ? [PL0 VL0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PM0 VM0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PB0 VB0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PX0 VX0] FA4]; subst. clear FA FA1 FA2 FA3 FA4.
  assert (Hlt : bl <> bm /\ bl <> bb /\ bl <> bx /\ bm <> bb /\ bm <> bx /\ bb <> bx).
  { clear - ND. repeat (apply NoDup_cons_iff in ND; destruct ND as [? ND]). cbn in *. intuition congruence. }
  destruct Hlt as (Hlm & Hlb & Hlx & Hmb & Hmx & Hbx).
  clear HAL ND FRh.
  assert (Fl : forall b0, Mem.valid_block m b0 -> b0 <> bl) by (intros b0 Hv; apply (FR5 b0 Hv)).
  assert (Fm : forall b0, Mem.valid_block m b0 -> b0 <> bm) by (intros b0 Hv; apply (FR5 b0 Hv)).
  assert (Fb : forall b0, Mem.valid_block m b0 -> b0 <> bb) by (intros b0 Hv; apply (FR5 b0 Hv)).
  assert (Fx : forall b0, Mem.valid_block m b0 -> b0 <> bx) by (intros b0 Hv; apply (FR5 b0 Hv)).
  set (e := ah_env bl bm bb bx).
  set (le0 := ah_temps env bd dbase bs sbase).
  (* the frame copy *)
  assert (HSE0 : Mem.load Mptr m0 bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSO0 : Mem.load Mint64 m0 bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_loadbytes_at m0 bs sbase _ _ HSE0 HSO0) as [bytes HB0].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB0) as Hbyteslen.
  assert (PLW : Mem.range_perm m0 bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm m0 bl 0 16 Cur Writable).
    intros ofs Hr. eapply Mem.perm_implies; [apply PL0; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m0 bl 0 bytes PLW) as [mcp SC].
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
  assert (Vl1 : Mem.valid_block m1 bl) by (apply V1, Vc; exact VL0).
  assert (Vm1 : Mem.valid_block m1 bm) by (apply V1, Vc; exact VM0).
  assert (Vb1 : Mem.valid_block m1 bb) by (apply V1, Vc; exact VB0).
  assert (Vx1 : Mem.valid_block m1 bx) by (apply V1, Vc; exact VX0).
  (* the context reader *)
  destruct (Mem.alloc m1 0 8) as [ma bq] eqn:AL.
  pose proof (mext_alloc _ _ _ _ _ AL) as (YV & YL & YP & YA).
  assert (Fq : forall b0, Mem.valid_block m1 b0 -> b0 <> bq).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ AL Hv). }
  assert (PXa : Mem.range_perm ma bx 0 88 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PX0, Hr).
  assert (PMa : Mem.range_perm ma bm 0 32 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PM0, Hr).
  assert (PLa : Mem.range_perm ma bl 0 16 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PL0, Hr).
  assert (PBa : Mem.range_perm ma bb 0 32 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PB0, Hr).
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
  { eapply buffer_input_cells_preserved; [|exact HinC]. intros ofs w HL. rewrite Ka by exact Vi. exact HL. }
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
    exists mf, Mem.free_list m5 [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bb, 0, 32)] = Some mf /\
      (forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mf b0 ofs = Mem.load ch m5 b0 ofs)).
  { intros m5 HP5.
    destruct (free_list_blocks [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bb, 0, 32)] m5)
      as (mf & HFL & HLf & _ & _).
    - intros b0 lo hi Hin0. cbn in Hin0.
      destruct Hin0 as [Heq|[Heq|[Heq|[Heq|[]]]]]; injection Heq as <- <- <-; intros ofs Hr0; apply HP5.
      + apply Fq; exact Vx1.
      + apply PXa; exact Hr0.
      + apply Fq; exact Vl1.
      + apply PLa; exact Hr0.
      + apply Fq; exact Vm1.
      + apply PMa; exact Hr0.
      + apply Fq; exact Vb1.
      + apply PBa; exact Hr0.
    - cbn. repeat constructor; cbn; intuition congruence.
    - exists mf. split; [exact HFL|]. intros ch b0 ofs Hv. apply HLf. cbn.
      intros [E|[E|[E|[E|[]]]]]; subst b0;
        [exact (Fx _ Hv eq_refl)|exact (Fl _ Hv eq_refl)|exact (Fm _ Hv eq_refl)|exact (Fb _ Hv eq_refl)]. }
  (* the specification *)
  assert (Hlist : lbuf = buffer_list (Word 3) 5 buf) by (apply buffer_values_list).
  set (total := @toZ (WordToZ 6) count + (Z.of_nat (length lbuf) + nvs) / 64).
  assert (HSpecV : exists (buf' : Ty.tySem (buffer_type (Word 3) 5)) (h' : Ty.tySem (Word 8)),
    byte_chunks_values (buffer_byte_chunks 5 buf') = fst (absorb lbuf (state_regs state) vs) /\
    state_regs h' = snd (absorb lbuf (state_regs state) vs) /\
    spec = (if total <? ctx8_limit then Some (buf', (@fromZ (WordToZ 6) total, h')) else None)).
  { destruct (ctx8_add_values buf count state vs) as (buf' & h' & HS1 & HS2 & HS3).
    rewrite <- Hlist in HS1, HS2, HS3. rewrite Hnvs in HS3. fold total in HS3.
    exists buf', h'. rewrite buffer_values_list. split; [exact HS1|]. split; [exact HS2|].
    etransitivity; [|exact HS3]. unfold spec. rewrite annex_hash_option.
    unfold vs, annex_bytes. destruct a; reflexivity. }
  destruct HSpecV as (buf' & h' & Hbuf' & Hh' & HSpec).
  clearbody spec.
  assert (HDiv : 0 <= (Z.of_nat (length lbuf) + nvs) / 64) by (apply div64_nonneg; lia).
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
  { eapply ah_copy; [exact HSbase|exact HSAlign| |reflexivity|exact HB0|exact SC].
    intro Heq. apply (Fl bs Vs). congruence. }
  destruct (sha256_read_overflow r) eqn:Hovr.
  - (* the stored compression count is out of range *)
    apply sha256_read_overflow_true in Hovr.
    assert (HNone : spec = None).
    { rewrite HSpec. assert (HF : (total <? ctx8_limit) = false)
        by (apply Z.ltb_ge; unfold total, ctx8_limit; rewrite <- Hr; lia).
      rewrite HF. reflexivity. }
    destruct (HFree m2 HPerm2) as (mf & HFL & HLf).
    exists mf. rewrite HNone. split; [|split; [exact I|]].
    + eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0)
        (le2 := PTree.set _t'1 (Vint (bit_int (negb true))) le0) (m2 := m2)
        (out := Out_return (Some (Vint (Int.repr 0), tint))).
      * eapply ah_entry; eassumption.
      * rewrite ah_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
        apply HInitEx. unfold ah_rest.
        eapply exec_Sseq_2; [|discriminate]. unfold fz_read.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply HCallRead. exact HRd.
        -- eapply exec_Sifthenelse with (b := true);
             [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
           apply exec_Sreturn_some. apply eval_Econst_int.
      * cbn. split; [discriminate|reflexivity].
      * unfold e. rewrite ah_blocks. exact HFL.
    + intros ch b0 ofs Hv Hd Hw. rewrite HLf by exact Hv. apply K2; exact Hv.
  - (* the reader succeeds *)
    apply sha256_read_overflow_false in Hovr.
    assert (Q2 : forall b0 ofs kd p, b0 <> bq -> Mem.perm ma b0 ofs kd p -> Mem.perm m2 b0 ofs kd p)
      by exact HPerm2.
    set (regs := state_regs state) in *.
    set (cc := sha256_read_counter r (Int64.repr (Z.of_nat (length lbuf)))) in *.
    set (vn := Int64.repr nvs).
    assert (Hlr : length regs = 8%nat).
    { unfold regs, state_regs. rewrite map_length. apply (word32_chunks_length 3). }
    assert (HccU : Int64.unsigned cc = 64 * Int64.unsigned r + Z.of_nat (length lbuf)).
    { apply add_counter_c; [exact Hovr|exact Hlbuf]. }
    assert (HAbs2 : ctx_abs m2 bx bm lbuf regs cc false).
    { split; [exact HOut2|]. split; [exact HCnt2|]. split; [exact HOvf2|].
      split; [intros i Hi; apply (u8_nth _ _ _ _ HArr2); exact Hi|].
      split; [intros i Hi; apply (u32_nth m2 bm 0 regs HSt2); rewrite Hlr; exact Hi|].
      split.
      { rewrite HccU. replace (64 * Int64.unsigned r + Z.of_nat (length lbuf)) with
          (Z.of_nat (length lbuf) + Int64.unsigned r * 64) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      split; [lia|]. split; [exact Hlr|].
      split; [intros ofs Hr0; apply Q2; [apply Fq; exact Vx1|apply PXa; exact Hr0]|].
      split; [intros ofs Hr0; apply Q2; [apply Fq; exact Vm1|apply PMa; exact Hr0]|].
      split; [unfold sha_dispatch_ok; fold G; rewrite K2 by exact VG; exact Hdisp|].
      fold MAXC. rewrite K2 by exact VM. exact HMaxC. }
    set (le2 := PTree.set _t'1 (Vint (bit_int (negb false))) le0).
    assert (HMid : exists m4,
      Clight2.exec_stmt sha_ge e le2 m2 ah_mid E0
        (PTree.set _t'2 (Vint (bit_int (annex_bit a))) le2) m4 Out_normal /\
      ctx_abs m4 bx bm (fst (absorb lbuf regs vs)) (snd (absorb lbuf regs vs))
        (Int64.add cc vn) (uc_overflow false cc vn) /\
      (forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m4 b0 ofs = Mem.load ch m b0 ofs) /\
      (forall b0 ofs kd p, b0 <> bq -> Mem.perm ma b0 ofs kd p -> Mem.perm m4 b0 ofs kd p)).
    { (* the tag bit *)
      assert (HBit : frame_input_bit_at m2 bi edge (rc + 830) (annex_bit a)).
      { pose proof (HinB 0%nat (Some (annex_bit a))) as HB1.
        assert (HN : nth_error (@encode (Ty.Sum Ty.Unit (Word 8)) a) 0 = Some (Some (annex_bit a)))
          by (destruct a; reflexivity).
        specialize (HB1 HN). cbn [cell_matches] in HB1.
        change (Z.of_nat 0) with 0 in HB1. rewrite Z.add_0_r in HB1.
        destruct HB1 as (HB1 & HB2 & w & HW & HT). split; [exact HB1|]. split; [exact HB2|].
        exists w. split; [rewrite K2 by exact Vi; exact HW|exact HT]. }
      assert (SW2 : Mem.valid_access m2 Mint64 bl (0 + 8) Writable).
      { destruct R31 as [Pr Al]. split; [|exact Al]. intros ofs Hr0.
        apply Q2; [apply Fq; exact Vl1|apply Pr; exact Hr0]. }
      destruct (eval_readBit_layout m2 bl 0 bi edge (rc + 830) (annex_bit a) HLocalBase
        ltac:(lia) HFld2 HBit SW2) as (m2b & HRB & HFld2b & HMem2b & HPerm2b & HVal2b).
      apply (sha_transport_call _ _ ah_in_readBit) in HRB.
      assert (K2b : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2b b0 ofs = Mem.load ch m b0 ofs).
      { intros ch b0 ofs Hv. rewrite HMem2b by (left; apply Fl; exact Hv). apply K2; exact Hv. }
      assert (Q2b : forall b0 ofs kd p, b0 <> bq -> Mem.perm ma b0 ofs kd p -> Mem.perm m2b b0 ofs kd p).
      { intros b0 ofs kd p Hb Hp. apply HPerm2b, Q2; assumption. }
      assert (HAbs2b : ctx_abs m2b bx bm lbuf regs cc false).
      { eapply ctx_abs_other; [exact HAbs2| |exact HPerm2b].
        intros ch b0 ofs Hb. apply HMem2b. left.
        destruct Hb as [E|[E|[E|E]]]; subst b0;
          [exact (not_eq_sym Hlx)|exact (not_eq_sym Hlm)|exact (Fl G VG)|exact (Fl MAXC VM)]. }
      assert (HCallBit : Clight2.exec_stmt sha_ge e le2 m2 ah_readbit E0
        (PTree.set _t'2 (Vint (bit_int (annex_bit a))) le2) m2b Out_normal).
      { unfold ah_readbit.
        eapply exec_Scall with (optid := Some _t'2) (vf := Vptr (sha_symbol_block _readBit) Ptrofs.zero)
          (vargs := [Vptr bl Ptrofs.zero]) (f := Internal jets.f_readBit).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ah_readBit_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        - exact ah_readBit_funct.
        - reflexivity.
        - exact HRB. }
      unfold ah_mid.
      destruct a as [u|h].
      + (* no annex *)
        pose proof (ctx_abs_uchar bx bm Hmx (Fx G VG) (Fm G VG) (Fx MAXC VM) (Fm MAXC VM) Hmodel
          m2b lbuf regs byte_zero cc false HAbs2b) as HU.
        cbv zeta in HU. destruct HU as (m4 & HUc & HAbs4 & HL4 & HP4 & HV4).
        exists m4. split; [|split; [exact HAbs4|split]].
        * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCallBit|].
          eapply exec_Sifthenelse with (b := false);
            [apply eval_Etempvar; apply PTree.gss|reflexivity|].
          unfold ah_uchar.
          eapply exec_Scall with (optid := None) (vf := Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero)
            (vargs := [Vptr bx Ptrofs.zero; Vint (word8_array_value byte_zero)]) (f := Internal f_sha256_uchar).
          -- reflexivity.
          -- eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ah_uchar_symbol]|].
             apply deref_loc_reference; reflexivity.
          -- eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
             eapply eval_Econs; [apply eval_Econst_int|apply ah_cast0|apply eval_Enil].
          -- exact ah_uchar_funct.
          -- reflexivity.
          -- exact HUc.
        * intros ch b0 ofs Hv.
          rewrite HL4; [apply K2b; exact Hv|apply HVal2b, W2, Hv|apply Fx; exact Hv|apply Fm; exact Hv].
        * intros b0 ofs kd p Hb Hp. apply HP4; [|apply Q2b; assumption].
          eapply Mem.perm_valid_block. apply Q2b; eassumption.
      + (* an annex hash *)
        set (vs32 := vector_values (Word 3) 5 h).
        assert (Hlen32 : length vs32 = 32%nat) by (unfold vs32; rewrite vector_values_length; reflexivity).
        assert (HWords : forall i x, nth_error vs32 i = Some x ->
          frame_input_word_at m2b bi edge (rc + 831 + 8 * Z.of_nat i) x).
        { assert (HinW : frame_input_cells_at m bi edge (rc + 831) (concat (map (@encode (Word 3)) vs32))).
          { change (@encode (Ty.Sum Ty.Unit (Word 8)) (inr h)) with ([Some true] ++ @encode (Word 8) h) in HinB.
            apply frame_input_cells_at_app in HinB. destruct HinB as [_ HinB].
            change (rc + 830 + Z.of_nat (length [Some true])) with (rc + 830 + 1) in HinB.
            replace (rc + 830 + 1) with (rc + 831) in HinB by lia.
            unfold vs32. rewrite <- (encode_vector_values (Word 3) 5 h). exact HinB. }
          rewrite frame_input_byte_list in HinW.
          intros i x Hi. eapply frame_input_bits_at_preserved; [|exact (HinW i x Hi)].
          intros ofs w HL. rewrite K2b by exact Vi. exact HL. }
        assert (PB2 : Mem.range_perm m2b bb 0 (0 + Z.of_nat (length vs32)) Cur Writable).
        { rewrite Hlen32. intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
          apply Q2b; [apply Fq; exact Vb1|apply PBa; lia]. }
        assert (SW2b : Mem.valid_access m2b Mint64 bl (0 + 8) Writable).
        { destruct SW2 as [Pr Al]. split; [|exact Al]. intros ofs Hr0. apply HPerm2b, Pr, Hr0. }
        assert (HFld2b' : frame_fields_at m2b bl 0 bi edge (rc + 831)).
        { replace (rc + 831) with (rc + 830 + 1) by lia. exact HFld2b. }
        destruct (eval_read8s_layout m2b bb 0 bl 0 bi edge (rc + 831) vs32 ltac:(lia)
          ltac:(rewrite Hlen32; change Ptrofs.max_unsigned with 18446744073709551615; lia) PB2
          Hlb (not_eq_sym (Fl bi Vi)) (not_eq_sym (Fb bi Vi)) HLocalBase ltac:(lia) ltac:(rewrite Hlen32; lia)
          HFld2b' SW2b HWords)
          as (m3 & HR8 & HArr3 & HFld3 & HMem3 & HPerm3 & HVal3).
        rewrite Hlen32 in HR8. change (Z.of_nat 32) with 32 in HR8.
        apply (sha_transport_call _ _ sg_in_read8s) in HR8.
        assert (HAbs3 : ctx_abs m3 bx bm lbuf regs cc false).
        { eapply ctx_abs_other; [exact HAbs2b| |exact HPerm3].
          intros ch b0 ofs Hb. apply HMem3.
          - left. destruct Hb as [E|[E|[E|E]]]; subst b0;
              [exact (not_eq_sym Hlx)|exact (not_eq_sym Hlm)|exact (Fl G VG)|exact (Fl MAXC VM)].
          - left. destruct Hb as [E|[E|[E|E]]]; subst b0;
              [exact (not_eq_sym Hbx)|exact Hmb|exact (Fb G VG)|exact (Fb MAXC VM)]. }
        pose proof (ctx_abs_uchar bx bm Hmx (Fx G VG) (Fm G VG) (Fx MAXC VM) (Fm MAXC VM) Hmodel
          m3 lbuf regs byte_one cc false HAbs3) as HU1.
        cbv zeta in HU1. destruct HU1 as (m3b & HUc1 & HAbs3b & HL3b & HP3b & HV3b).
        assert (Vb3 : Mem.valid_block m3 bb) by (apply HVal3, HVal2b, HVal2, YV; exact Vb1).
        assert (HaM : Ptrofs.unsigned Ptrofs.zero + Z.of_nat (length vs32) <= Ptrofs.max_unsigned).
        { change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Hlen32.
          change Ptrofs.max_unsigned with 18446744073709551615. lia. }
        assert (HBs : forall i, (i < length (map word8_array_value vs32))%nat ->
          Mem.load Mint8unsigned m3b bb (Ptrofs.unsigned Ptrofs.zero + Z.of_nat i) =
            Some (Vint (nth i (map word8_array_value vs32) Int.zero))).
        { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0.
          rewrite (HL3b _ bb _ Vb3 Hbx (not_eq_sym Hmb)).
          apply (u8_nth _ _ _ _ HArr3). exact Hi. }
        pose proof (ctx_abs_uchars bx bm Hmx (Fx G VG) (Fm G VG) (Fx MAXC VM) (Fm MAXC VM) Hmodel
          m3b bb Ptrofs.zero (fst (absorb lbuf regs [byte_one])) (snd (absorb lbuf regs [byte_one])) vs32
          (Int64.add cc (Int64.repr 1)) (uc_overflow false cc (Int64.repr 1)) HAbs3b
          Hbx (not_eq_sym Hmb) HaM HBs) as HU.
        cbv zeta in HU. destruct HU as (m4 & HUc & HAbs4 & HL4 & HP4 & HV4).
        rewrite absorb_app in HAbs4.
        rewrite (ah_len (length vs32) 32 ltac:(rewrite Hlen32; reflexivity)) in HAbs4, HUc.
        pose proof (ah_counter_two r (Z.of_nat (length lbuf)) Hovr Hlbuf) as HC2.
        cbv zeta in HC2. fold cc in HC2. destruct HC2 as [HC2 HO2].
        rewrite HC2, HO2 in HAbs4.
        exists m4. split; [|split; [exact HAbs4|split]].
        * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCallBit|].
          eapply exec_Sifthenelse with (b := true);
            [apply eval_Etempvar; apply PTree.gss|reflexivity|].
          set (le3 := PTree.set _t'2 (Vint (bit_int (annex_bit (inr h)))) le2).
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m3).
          { unfold ah_read8s.
            eapply exec_Scall with (optid := None) (vf := Vptr (sha_symbol_block _read8s) Ptrofs.zero)
              (vargs := [Vptr bb Ptrofs.zero; Vlong (Int64.repr 32); Vptr bl Ptrofs.zero])
              (f := Internal jets.f_read8s).
            - reflexivity.
            - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_read8s_symbol]|].
              apply deref_loc_reference; reflexivity.
            - eapply eval_Econs.
              + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
              + reflexivity.
              + eapply eval_Econs; [apply eval_Econst_int|apply ah_cast32|].
                eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
            - exact an_read8s_funct.
            - reflexivity.
            - exact HR8. }
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m3b).
          { unfold ah_uchar.
            eapply exec_Scall with (optid := None) (vf := Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero)
              (vargs := [Vptr bx Ptrofs.zero; Vint (word8_array_value byte_one)]) (f := Internal f_sha256_uchar).
            - reflexivity.
            - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ah_uchar_symbol]|].
              apply deref_loc_reference; reflexivity.
            - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs; [apply eval_Econst_int|apply ah_cast1|apply eval_Enil].
            - exact ah_uchar_funct.
            - reflexivity.
            - exact HUc1. }
          unfold ah_uchars.
          eapply exec_Scall with (optid := None) (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
            (vargs := [Vptr bx Ptrofs.zero; Vptr bb Ptrofs.zero; Vlong (Int64.repr 32)])
            (f := Internal f_sha256_uchars).
          -- reflexivity.
          -- eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_uchars_symbol]|].
             apply deref_loc_reference; reflexivity.
          -- eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
             eapply eval_Econs.
             ++ eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
             ++ reflexivity.
             ++ eapply eval_Econs; [apply eval_Econst_int|apply ah_cast32|apply eval_Enil].
          -- exact an_uchars_funct.
          -- reflexivity.
          -- exact HUc.
        * intros ch b0 ofs Hv.
          rewrite HL4; [|apply HV3b, HVal3, HVal2b, W2, Hv|apply Fx; exact Hv|apply Fm; exact Hv].
          rewrite HL3b; [|apply HVal3, HVal2b, W2, Hv|apply Fx; exact Hv|apply Fm; exact Hv].
          rewrite HMem3; [apply K2b; exact Hv|left; apply Fl; exact Hv|left; apply Fb; exact Hv].
        * intros b0 ofs kd p Hb Hp.
          assert (Hp3 : Mem.perm m3 b0 ofs kd p) by (apply HPerm3, Q2b; assumption).
          apply HP4; [apply HV3b; eapply Mem.perm_valid_block; exact Hp3|].
          apply HP3b; [eapply Mem.perm_valid_block; exact Hp3|exact Hp3]. }
    destruct HMid as (m4 & HMidEx & HAbs4 & K4 & Q4a).
    set (lA := fst (absorb lbuf regs vs)) in *. set (rA := snd (absorb lbuf regs vs)) in *.
    destruct (absorb_length vs lbuf regs ltac:(lia)) as [HlenA HltA]. fold lA in HlenA, HltA.
    rewrite Hnvs in HlenA.
    destruct HAbs4 as (HOut4 & HCnt4 & HOvf4 & HBlk4 & HReg4 & _ & _ & HrA & _).
    set (bit := annex_bit a) in *.
    clearbody vs nvs bit.
    set (ovf' := uc_overflow false cc vn) in *.
    assert (Hovf' : ovf' = negb (total <? ctx8_limit)).
    { unfold ovf', cc, vn, total. rewrite <- Hr.
      apply (add_counter_overflow r (Z.of_nat (length lbuf)) nvs Hovr Hlbuf HnR). }
    clearbody ovf'.
    (* the context writer *)
    assert (Q4 : forall b0 ofs kd p, Mem.perm m b0 ofs kd p -> Mem.perm m4 b0 ofs kd p).
    { intros b0 ofs kd p Hp. assert (Hv : Mem.valid_block m b0) by (eapply Mem.perm_valid_block; exact Hp).
      apply Q4a; [apply Fq, W1; exact Hv|apply YP, Q1, XP, Hp]. }
    assert (HOut4' : write_frame_at m4 bd dbase bw outedge cursor 830).
    { eapply write_frame_at_preserved; [| |exact Hout].
      - intros ch b0 ofs v0 Hb HL. rewrite K4; [exact HL|destruct Hb; subst; assumption].
      - exact Q4. }
    assert (HArr4 : uint8_array_at m4 bx (0 + 16)
      (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 buf')))).
    { rewrite Hbuf'. apply u8_of_nth. exact HBlk4. }
    assert (HModu : Int64.modu (Int64.add cc vn) (Int64.repr 64) =
      Int64.repr (Z.of_nat (length (byte_chunks_values (buffer_byte_chunks 5 buf'))))).
    { rewrite Hbuf', HlenA.
      apply (add_counter_modu r (Z.of_nat (length lbuf)) nvs Hovr Hlbuf HnR). }
    assert (HSt4 : uint32_array_at m4 bm 0 (map word32_array_value (word32_chunks 3 h'))).
    { change (map word32_array_value (word32_chunks 3 h')) with (state_regs h'). rewrite Hh'.
      apply u32_of_nth. intros i Hi. apply HReg4. rewrite <- HrA. exact Hi. }
    destruct (eval_write_sha256_context_layout m4 bd dbase bw outedge cursor bx 0 bm 0
      (Int64.add cc vn) ovf' buf' h'
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
      (not_eq_sym (Fx bd Vd)) (not_eq_sym (Fx bw Vw)) (not_eq_sym (Fm bd Vd)) (not_eq_sym (Fm bw Vw))
      HCnt4 HOut4 HOvf4 HArr4 HModu HSt4 HOut4')
      as (m5 & HWr & HCells & HPrefix & HFldE & HLoadsE & HPermE & HValE).
    apply (sha_transport_call _ _ sg_in_write_context) in HWr.
    destruct (HFree m5) as (mf & HFL & HLf).
    { intros b0 ofs kd p Hb Hp. apply HPermE. apply Q4a; assumption. }
    set (le4 := PTree.set _t'2 (Vint (bit_int bit)) le2) in *.
    set (le5 := PTree.set _t'3 (Vint (bit_int (negb ovf'))) le4).
    exists mf. split; [|split].
    + eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le5) (m2 := m5)
        (out := Out_return (Some (Vint (bit_int (negb ovf')), tbool))).
      * eapply ah_entry; eassumption.
      * rewrite ah_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
        apply HInitEx. unfold ah_rest.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
        { unfold fz_read. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
          - apply HCallRead. exact HRd.
          - eapply exec_Sifthenelse with (b := false);
              [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
            apply exec_Sskip. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := m4); [exact HMidEx|].
        unfold ah_write. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m5).
        { change le5 with (set_opttemp (Some _t'3) (Vint (bit_int (negb ovf'))) le4).
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_write_sha256_context) Ptrofs.zero)
            (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bx Ptrofs.zero])
            (f := Internal jets.f_simplicity_write_sha256_context).
          - reflexivity.
          - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_write_context_symbol]|].
            apply deref_loc_reference; reflexivity.
          - eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
            eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
          - exact an_write_context_funct.
          - reflexivity.
          - exact HWr. }
        apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
      * cbn. split; [discriminate|]. rewrite HSpec, Hovf'.
        destruct (total <? ctx8_limit); reflexivity.
      * unfold e. rewrite ah_blocks. exact HFL.
    + rewrite HSpec. destruct (Z.ltb_spec total ctx8_limit) as [HT|HT]; [|exact I].
      assert (HCnt' : decode_wide W64 (Int64.zero_ext 64 (Int64.shru (Int64.add cc vn) (Int64.repr 6))) =
        @fromZ (WordToZ 6) total).
      { unfold cc, vn, total. rewrite <- Hr.
        apply (add_counter_count r _ _ Hovr Hlbuf HnR). rewrite Hr. exact HT. }
      rewrite HCnt' in HCells.
      split; [|split].
      * eapply frame_output_cells_preserved; [|exact HCells].
        intros ofs w HL. rewrite HLf by exact Vw. exact HL.
      * eapply write_prefix_at_preserved; [| |exact HPrefix].
        -- intros ofs w HL. rewrite K4 by exact Vw. exact HL.
        -- intros ofs w HL. rewrite HLf by exact Vw. exact HL.
      * destruct HFldE as [HE1 HE2]. split; rewrite HLf by exact Vd; assumption.
    + intros ch b0 ofs Hv Hd Hw. rewrite HLf by exact Hv.
      rewrite HLoadsE by assumption. apply K4; exact Hv.
Qed.
