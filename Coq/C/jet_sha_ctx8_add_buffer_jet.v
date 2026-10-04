(** The jet sha_256_ctx_8_add_buffer_511 of the SHA translation unit against
    the literal ctx8AddBuffer program over Buffer511.  Partial (assertion)
    contract; conditional on the explicit [memcpy_model], with the state
    premise [sha_globals_ok]. *)
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
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition ab_env (bl bm bb bn bx : block) : env :=
  PTree.set _ctx (bx, CTX) (PTree.set _buf_len (bn, tulong) (PTree.set _buf (bb, tarray tuchar 511)
    (PTree.set _midstate (bm, MID) (PTree.set _src (bl, FR) empty_env)))).

Definition ab_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_sha_256_ctx_8_add_buffer_511)))).

Definition ab_readbuf : statement :=
  Scall None (Evar _simplicity_read_buffer8
      (Tfunction (Tcons (tptr tuchar) (Tcons (tptr tulong) (Tcons FRP (Tcons tint Tnil)))) tvoid cc_default))
    [Evar _buf (tarray tuchar 511); Eaddrof (Evar _buf_len tulong) (tptr tulong);
     Eaddrof (Evar _src FR) FRP; Econst_int (Int.repr 8) tint].
Definition ab_uchars : statement :=
  Ssequence (Sset _t'3 (Evar _buf_len tulong))
    (Scall None (Evar _sha256_uchars uchars_ty)
      [Eaddrof (Evar _ctx CTX) CTXP; Evar _buf (tarray tuchar 511); Etempvar _t'3 tulong]).
Definition ab_write : statement :=
  Ssequence
    (Scall (Some _t'2) (Evar _simplicity_write_sha256_context
        (Tfunction (Tcons FRP (Tcons CTXP Tnil)) tbool cc_default))
      [Etempvar _dst FRP; Eaddrof (Evar _ctx CTX) CTXP])
    (Sreturn (Some (Etempvar _t'2 tbool))).
Definition ab_rest : statement :=
  Ssequence fz_read (Ssequence ab_readbuf (Ssequence ab_uchars ab_write)).

Lemma ab_body :
  fn_body f_simplicity_sha_256_ctx_8_add_buffer_511 =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR)) (an_init ab_rest).
Proof. reflexivity. Qed.

Lemma ab_blocks bl bm bb bn bx :
  blocks_of_env sha_ge (ab_env bl bm bb bn bx) =
    [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bn, 0, 8); (bb, 0, 511)].
Proof. vm_compute. reflexivity. Qed.

Lemma ab_read_buffer8_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_read_buffer8 =
    Some (sha_symbol_block _simplicity_read_buffer8).
Proof. vm_compute; reflexivity. Qed.
Lemma ab_read_buffer8_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _simplicity_read_buffer8) Ptrofs.zero) =
    Some (Internal jets.f_simplicity_read_buffer8).
Proof. vm_compute; reflexivity. Qed.

Lemma ab_entry env m m1 m2 m3 m4 m5 bl bm bb bn bx bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) -> Mem.alloc m2 0 511 = (m3, bb) ->
  Mem.alloc m3 0 8 = (m4, bn) -> Mem.alloc m4 0 88 = (m5, bx) ->
  function_entry2 sha_ge f_simplicity_sha_256_ctx_8_add_buffer_511
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (ab_env bl bm bb bn bx) (ab_temps env bd dbase bs sbase) m5.
Proof.
  intros HA HB HC HD HE. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl).
    + change (Mem.alloc m 0 16 = (m1, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := m2) (b1 := bm).
      * change (Mem.alloc m1 0 32 = (m2, bm)); exact HB.
      * eapply alloc_variables_cons with (m1 := m3) (b1 := bb).
        -- change (Mem.alloc m2 0 511 = (m3, bb)); exact HC.
        -- eapply alloc_variables_cons with (m1 := m4) (b1 := bn).
           ++ change (Mem.alloc m3 0 8 = (m4, bn)); exact HD.
           ++ eapply alloc_variables_cons with (m1 := m5) (b1 := bx).
              ** change (Mem.alloc m4 0 88 = (m5, bx)); exact HE.
              ** constructor.
  - reflexivity.
Qed.

Lemma ab_copy m mc bl bm bb bn bx bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (ab_env bl bm bb bn bx) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
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

(** Five nested allocations: freshness, distinctness and permissions. *)
Lemma alloc_chain5 m m1 m2 m3 m4 m5 b1 b2 b3 b4 b5 z1 z2 z3 z4 z5 :
  Mem.alloc m 0 z1 = (m1, b1) -> Mem.alloc m1 0 z2 = (m2, b2) -> Mem.alloc m2 0 z3 = (m3, b3) ->
  Mem.alloc m3 0 z4 = (m4, b4) -> Mem.alloc m4 0 z5 = (m5, b5) ->
  mext m m5 /\
  (forall b, Mem.valid_block m b -> b <> b1 /\ b <> b2 /\ b <> b3 /\ b <> b4 /\ b <> b5) /\
  NoDup [b1; b2; b3; b4; b5] /\
  Mem.range_perm m5 b1 0 z1 Cur Freeable /\ Mem.range_perm m5 b2 0 z2 Cur Freeable /\
  Mem.range_perm m5 b3 0 z3 Cur Freeable /\ Mem.range_perm m5 b4 0 z4 Cur Freeable /\
  Mem.range_perm m5 b5 0 z5 Cur Freeable /\
  Mem.valid_block m5 b1 /\ Mem.valid_block m5 b2 /\ Mem.valid_block m5 b3 /\
  Mem.valid_block m5 b4 /\ Mem.valid_block m5 b5.
Proof.
  intros A1 A2 A3 A4 A5.
  pose proof (mext_alloc _ _ _ _ _ A1) as X1. pose proof (mext_alloc _ _ _ _ _ A2) as X2.
  pose proof (mext_alloc _ _ _ _ _ A3) as X3. pose proof (mext_alloc _ _ _ _ _ A4) as X4.
  pose proof (mext_alloc _ _ _ _ _ A5) as X5.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ A1) as F1. pose proof (Mem.fresh_block_alloc _ _ _ _ _ A2) as F2.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ A3) as F3. pose proof (Mem.fresh_block_alloc _ _ _ _ _ A4) as F4.
  pose proof (Mem.fresh_block_alloc _ _ _ _ _ A5) as F5.
  pose proof (Mem.valid_new_block _ _ _ _ _ A1) as N1. pose proof (Mem.valid_new_block _ _ _ _ _ A2) as N2.
  pose proof (Mem.valid_new_block _ _ _ _ _ A3) as N3. pose proof (Mem.valid_new_block _ _ _ _ _ A4) as N4.
  pose proof (Mem.valid_new_block _ _ _ _ _ A5) as N5.
  assert (X12 : mext m m2) by (eapply mext_trans; eassumption).
  assert (X13 : mext m m3) by (eapply mext_trans; eassumption).
  assert (X14 : mext m m4) by (eapply mext_trans; eassumption).
  assert (X15 : mext m m5) by (eapply mext_trans; eassumption).
  assert (X25 : mext m2 m5) by (eapply mext_trans; [exact X3|eapply mext_trans; eassumption]).
  assert (X15' : mext m1 m5) by (eapply mext_trans; eassumption).
  assert (X35 : mext m3 m5) by (eapply mext_trans; eassumption).
  split; [exact X15|]. split.
  { intros b Hv. repeat split; intro Heq; subst b.
    - exact (F1 Hv).
    - apply F2, (proj1 X1), Hv.
    - apply F3, (proj1 X12), Hv.
    - apply F4, (proj1 X13), Hv.
    - apply F5, (proj1 X14), Hv. }
  split.
  { assert (V12 : Mem.valid_block m2 b1) by (apply (proj1 X2); exact N1).
    assert (V13 : Mem.valid_block m3 b1) by (apply (proj1 X3); exact V12).
    assert (V14 : Mem.valid_block m4 b1) by (apply (proj1 X4); exact V13).
    assert (V23 : Mem.valid_block m3 b2) by (apply (proj1 X3); exact N2).
    assert (V24 : Mem.valid_block m4 b2) by (apply (proj1 X4); exact V23).
    assert (V34 : Mem.valid_block m4 b3) by (apply (proj1 X4); exact N3).
    repeat constructor; cbn; intro Hin;
      repeat (destruct Hin as [Hin|Hin]; [subst; contradiction|]); exact Hin. }
  split; [intros ofs Hr; apply (proj1 (proj2 (proj2 X15'))); eapply Mem.perm_alloc_2; eauto|].
  split; [intros ofs Hr; apply (proj1 (proj2 (proj2 X25))); eapply Mem.perm_alloc_2; eauto|].
  split; [intros ofs Hr; apply (proj1 (proj2 (proj2 X35))); eapply Mem.perm_alloc_2; eauto|].
  split; [intros ofs Hr; apply (proj1 (proj2 (proj2 X5))); eapply Mem.perm_alloc_2; eauto|].
  split; [intros ofs Hr; eapply Mem.perm_alloc_2; eauto|].
  split; [apply (proj1 X15'); exact N1|]. split; [apply (proj1 X25); exact N2|].
  split; [apply (proj1 X35); exact N3|]. split; [apply (proj1 X5); exact N4|exact N5].
Qed.

Lemma nodup5 {A} (a b c d e : A) : NoDup [a; b; c; d; e] ->
  a <> b /\ a <> c /\ a <> d /\ a <> e /\ b <> c /\ b <> d /\ b <> e /\ c <> d /\ c <> e /\ d <> e.
Proof.
  intros H.
  apply NoDup_cons_iff in H. destruct H as [H1 H].
  apply NoDup_cons_iff in H. destruct H as [H2 H].
  apply NoDup_cons_iff in H. destruct H as [H3 H].
  apply NoDup_cons_iff in H. destruct H as [H4 H].
  cbn in *. intuition congruence.
Qed.

Theorem sha_256_ctx_8_add_buffer_511_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_buffer_511
    (Ty.Prod sha256_ctx8_type (buffer_type (Word 3) 8)) sha256_ctx8_type
    (fun a => @ctx8_add_buffer_spec 8 optalg a).
Proof.
  intros Hmodel env m bd dbase bs sbase bi bw edge outedge cursor rc [[buf [count state]] b]
    [Hdisp HMaxC] HSbase HSAlign [HSE HSO] H0 Hmax Hin Hout.
  change (Z.of_nat (bitSize (Ty.Prod sha256_ctx8_type (buffer_type (Word 3) 8)))) with 4927 in Hmax.
  rewrite sha256_ctx8_type_bits in *. change (Z.of_nat 830) with 830 in *.
  change (frame_input_cells_at m bi edge rc
    ((encode buf ++ encode count ++ encode state) ++ encode b)) in Hin.
  cbv beta.
  match goal with |- context[jet_partial_return ?sp] => set (spec := sp) end.
  set (G := sha_symbol_block _simplicity_sha256_compression) in *.
  set (MAXC := sha_symbol_block _sha256_max_counter) in *.
  set (lbuf := byte_chunks_values (buffer_byte_chunks 5 buf)).
  pose proof (sha256_buffer63_length_range buf) as Hlbuf. fold lbuf in Hlbuf.
  set (vs := byte_chunks_values (buffer_byte_chunks 8 b)).
  assert (Hvs511 : (length vs <= 511)%nat).
  { pose proof (byte_chunks_values_bound _ (buffer_byte_chunks_sized 8 b)) as HBd.
    rewrite buffer511_chunks_capacity in HBd. exact HBd. }
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
  destruct (Mem.alloc ma2 0 511) as [ma3 bb] eqn:A3.
  destruct (Mem.alloc ma3 0 8) as [ma4 bn] eqn:A4.
  destruct (Mem.alloc ma4 0 88) as [m0 bx] eqn:A5.
  destruct (alloc_chain5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 A2 A3 A4 A5)
    as ((XV & XL & XP & XA) & FR5 & ND & PL0 & PM0 & PB0 & PN0 & PX0 & VL0 & VM0 & VB0 & VN0 & VX0).
  destruct (nodup5 _ _ _ _ _ ND) as (Hlm & Hlb & Hln & Hlx & Hmb & Hmn & Hmx & Hbn & Hbx & Hnx).
  assert (Fl : forall b0, Mem.valid_block m b0 -> b0 <> bl) by (intros b0 Hv; apply (FR5 b0 Hv)).
  assert (Fm : forall b0, Mem.valid_block m b0 -> b0 <> bm) by (intros b0 Hv; apply (FR5 b0 Hv)).
  assert (Fb : forall b0, Mem.valid_block m b0 -> b0 <> bb) by (intros b0 Hv; apply (FR5 b0 Hv)).
  assert (Fn : forall b0, Mem.valid_block m b0 -> b0 <> bn) by (intros b0 Hv; apply (FR5 b0 Hv)).
  assert (Fx : forall b0, Mem.valid_block m b0 -> b0 <> bx) by (intros b0 Hv; apply (FR5 b0 Hv)).
  set (e := ab_env bl bm bb bn bx).
  set (le0 := ab_temps env bd dbase bs sbase).
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
  assert (Vn1 : Mem.valid_block m1 bn) by (apply V1, Vc; exact VN0).
  assert (Vx1 : Mem.valid_block m1 bx) by (apply V1, Vc; exact VX0).
  (* the context reader *)
  destruct (Mem.alloc m1 0 8) as [ma bq] eqn:AL.
  pose proof (mext_alloc _ _ _ _ _ AL) as (YV & YL & YP & YA).
  assert (Fq : forall b0, Mem.valid_block m1 b0 -> b0 <> bq).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ AL Hv). }
  assert (PXa : Mem.range_perm ma bx 0 88 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PX0, Hr).
  assert (PMa : Mem.range_perm ma bm 0 32 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PM0, Hr).
  assert (PLa : Mem.range_perm ma bl 0 16 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PL0, Hr).
  assert (PBa : Mem.range_perm ma bb 0 511 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PB0, Hr).
  assert (PNa : Mem.range_perm ma bn 0 8 Cur Freeable) by (intros ofs Hr; apply YP, Q1, PN0, Hr).
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
    exists mf, Mem.free_list m5 [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bn, 0, 8); (bb, 0, 511)] = Some mf /\
      (forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mf b0 ofs = Mem.load ch m5 b0 ofs)).
  { intros m5 HP5.
    destruct (free_list_blocks [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bn, 0, 8); (bb, 0, 511)] m5)
      as (mf & HFL & HLf & _ & _).
    - intros b0 lo hi Hin0. cbn in Hin0.
      destruct Hin0 as [Heq|[Heq|[Heq|[Heq|[Heq|[]]]]]]; injection Heq as <- <- <-; intros ofs Hr0; apply HP5.
      + apply Fq; exact Vx1.
      + apply PXa; exact Hr0.
      + apply Fq; exact Vl1.
      + apply PLa; exact Hr0.
      + apply Fq; exact Vm1.
      + apply PMa; exact Hr0.
      + apply Fq; exact Vn1.
      + apply PNa; exact Hr0.
      + apply Fq; exact Vb1.
      + apply PBa; exact Hr0.
    - cbn. repeat constructor; cbn; intuition congruence.
    - exists mf. split; [exact HFL|]. intros ch b0 ofs Hv. apply HLf. cbn.
      intros [E|[E|[E|[E|[E|[]]]]]]; subst b0;
        [exact (Fx _ Hv eq_refl)|exact (Fl _ Hv eq_refl)|exact (Fm _ Hv eq_refl)
        |exact (Fn _ Hv eq_refl)|exact (Fb _ Hv eq_refl)]. }
  (* the specification *)
  assert (Hlist : lbuf = buffer_list (Word 3) 5 buf) by (apply buffer_values_list).
  assert (Hvlist : vs = buffer_list (Word 3) 8 b) by (apply buffer_values_list).
  set (total := @toZ (WordToZ 6) count + (Z.of_nat (length lbuf) + Z.of_nat (length vs)) / 64).
  assert (HSpecV : exists (buf' : Ty.tySem (buffer_type (Word 3) 5)) (h' : Ty.tySem (Word 8)),
    byte_chunks_values (buffer_byte_chunks 5 buf') = fst (absorb lbuf (state_regs state) vs) /\
    state_regs h' = snd (absorb lbuf (state_regs state) vs) /\
    spec = (if total <? ctx8_limit then Some (buf', (@fromZ (WordToZ 6) total, h')) else None)).
  { destruct (ctx8_add_values buf count state vs) as (buf' & h' & HS1 & HS2 & HS3).
    rewrite <- Hlist in HS1, HS2, HS3. fold total in HS3.
    exists buf', h'. rewrite buffer_values_list. split; [exact HS1|]. split; [exact HS2|].
    etransitivity; [|exact HS3]. unfold spec. rewrite ctx8_add_buffer_option.
    destruct (ctx8_add_buffer_model_list 8 (buf, (count, state)) b) as [HM1 HM2].
    rewrite <- Hvlist in HM1, HM2.
    clearbody vs. destruct vs as [|v0 vs'].
    - exact (HM1 eq_refl).
    - exact (HM2 ltac:(discriminate)). }
  destruct HSpecV as (buf' & h' & Hbuf' & Hh' & HSpec).
  clearbody spec.
  assert (HDiv : 0 <= (Z.of_nat (length lbuf) + Z.of_nat (length vs)) / 64) by (apply div64_nonneg; lia).
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
  { eapply ab_copy; [exact HSbase|exact HSAlign| |reflexivity|exact HB0|exact SC].
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
      * eapply ab_entry; eassumption.
      * rewrite ab_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
        apply HInitEx. unfold ab_rest.
        eapply exec_Sseq_2; [|discriminate]. unfold fz_read.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- apply HCallRead. exact HRd.
        -- eapply exec_Sifthenelse with (b := true);
             [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
           apply exec_Sreturn_some. apply eval_Econst_int.
      * cbn. split; [discriminate|reflexivity].
      * unfold e. rewrite ab_blocks. exact HFL.
    + intros ch b0 ofs Hv Hd Hw. rewrite HLf by exact Hv. apply K2; exact Hv.
  - (* the reader succeeds *)
    apply sha256_read_overflow_false in Hovr.
    assert (Q2 : forall b0 ofs kd p, b0 <> bq -> Mem.perm ma b0 ofs kd p -> Mem.perm m2 b0 ofs kd p)
      by exact HPerm2.
    (* the buffer *)
    assert (HinB2 : frame_input_cells_at m2 bi edge (rc + 830) (encode b)).
    { eapply buffer_input_cells_preserved; [|exact HinB]. intros ofs w HL. rewrite K2 by exact Vi. exact HL. }
    assert (PB2 : Mem.range_perm m2 bb 0 (0 + 511) Cur Writable).
    { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
      apply Q2; [apply Fq; exact Vb1|apply PBa; lia]. }
    assert (PN2 : Mem.valid_access m2 Mint64 bn 0 Writable).
    { split; [|exists 0; reflexivity]. intros ofs Hr0. change (size_chunk Mint64) with 8 in Hr0.
      eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
      apply Q2; [apply Fq; exact Vn1|apply PNa; lia]. }
    assert (SW2 : Mem.valid_access m2 Mint64 bl (0 + 8) Writable).
    { destruct R31 as [Pr Al]. split; [|exact Al]. intros ofs Hr0.
      apply Q2; [apply Fq; exact Vl1|apply Pr; exact Hr0]. }
    destruct (eval_read_buffer8_511_layout m2 bl 0 bi edge (rc + 830) bb 0 bn 0 b
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) PB2
      ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) PN2
      Hlb (not_eq_sym (Fl bi Vi)) (not_eq_sym (Fb bi Vi)) (not_eq_sym Hln) (not_eq_sym Hbn)
      (not_eq_sym (Fn bi Vi)) HLocalBase ltac:(lia) ltac:(lia) HFld2 SW2 HinB2)
      as (m3 & HR8 & HArr3 & HLen3 & HFld3 & HMem3 & HPerm3 & HVal3).
    fold vs in HArr3, HLen3.
    apply (sha_transport_call _ _ sg_in_read_buffer8) in HR8.
    assert (K3 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m3 b0 ofs = Mem.load ch m b0 ofs).
    { intros ch b0 ofs Hv.
      rewrite HMem3; [apply K2; exact Hv|left; apply Fl; exact Hv|left; apply Fb; exact Hv|left; apply Fn; exact Hv]. }
    set (l := map word8_array_value lbuf).
    set (regs := state_regs state).
    set (bsi := map word8_array_value vs).
    set (cc := sha256_read_counter r (Int64.repr (Z.of_nat (length lbuf)))) in *.
    set (vn := Int64.repr (Z.of_nat (length vs))).
    assert (Hll : length l = length lbuf) by (unfold l; apply map_length).
    assert (Hlbs : length bsi = length vs) by (unfold bsi; apply map_length).
    assert (Hlr : length regs = 8%nat).
    { unfold regs, state_regs. rewrite map_length. apply (word32_chunks_length 3). }
    assert (HccU : Int64.unsigned cc = 64 * Int64.unsigned r + Z.of_nat (length lbuf)).
    { apply add_counter_c; [exact Hovr|exact Hlbuf]. }
    assert (L3x : forall ch ofs, Mem.load ch m3 bx ofs = Mem.load ch m2 bx ofs).
    { intros ch ofs. apply HMem3; [left; exact (not_eq_sym Hlx)|left; exact (not_eq_sym Hbx)|left; exact (not_eq_sym Hnx)]. }
    assert (L3m : forall ch ofs, Mem.load ch m3 bm ofs = Mem.load ch m2 bm ofs).
    { intros ch ofs. apply HMem3; [left; exact (not_eq_sym Hlm)|left; exact Hmb|left; exact Hmn]. }
    assert (Q3 : forall b0 ofs kd p, b0 <> bq -> Mem.perm ma b0 ofs kd p -> Mem.perm m3 b0 ofs kd p).
    { intros b0 ofs kd p Hb Hp. apply HPerm3, Q2; assumption. }
    pose proof (eval_sha256_uchars Hmodel m3 bx 0 bm 0 bb Ptrofs.zero l regs bsi cc false
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
      ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
      Hmx Hbx (not_eq_sym Hmb) (Fx G VG) (Fm G VG)) as HU.
    cbv zeta in HU.
    destruct HU as (m4 & HUc & HOut4 & HCnt4 & HOvf4 & HBlk4 & HReg4 & HMem4 & HPerm4 & HVal4).
    { change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Hlbs.
      change Ptrofs.max_unsigned with 18446744073709551615. lia. }
    { exact Hlr. }
    { rewrite L3x. exact HOut2. }
    { rewrite L3x. exact HCnt2. }
    { rewrite HccU, Hll. replace (64 * Int64.unsigned r + Z.of_nat (length lbuf)) with
        (Z.of_nat (length lbuf) + Int64.unsigned r * 64) by lia.
      rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    { rewrite L3x. exact HOvf2. }
    { intros i Hi. rewrite L3x. apply (u8_nth _ _ _ _ HArr2). exact Hi. }
    { intros i Hi. split.
      - rewrite L3m. apply (u32_nth m2 bm 0 regs HSt2). rewrite Hlr. exact Hi.
      - split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; lia].
        intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
        eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
        apply Q3; [apply Fq; exact Vm1|apply PMa; lia]. }
    { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. apply (u8_nth _ _ _ _ HArr3). exact Hi. }
    { unfold sha_dispatch_ok. fold G. rewrite K3 by exact VG. exact Hdisp. }
    { fold MAXC. rewrite K3 by exact VM. exact HMaxC. }
    { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
      apply Q3; [apply Fq; exact Vx1|apply PXa; lia]. }
    { exists 0. reflexivity. }
    rewrite Hlbs in HUc, HCnt4, HOvf4. fold vn in HUc, HCnt4, HOvf4.
    unfold l, bsi in HBlk4, HReg4. rewrite absorb_i_map in HBlk4, HReg4. cbn [fst snd] in HBlk4, HReg4.
    fold regs in Hbuf', Hh'.
    set (lA := fst (absorb lbuf regs vs)) in *. set (rA := snd (absorb lbuf regs vs)) in *.
    destruct (absorb_length vs lbuf regs ltac:(lia)) as [HlenA HltA]. fold lA in HlenA, HltA.
    assert (HrA : length rA = 8%nat) by (apply absorb_regs_length; [lia|exact Hlr]).
    set (ovf' := uc_overflow false cc vn) in *.
    assert (HnR : 0 <= Z.of_nat (length vs) <= 4096) by lia.
    assert (Hovf' : ovf' = negb (total <? ctx8_limit)).
    { unfold ovf', cc, vn, total. rewrite <- Hr.
      apply (add_counter_overflow r (Z.of_nat (length lbuf)) (Z.of_nat (length vs)) Hovr Hlbuf HnR). }
    clearbody ovf'.
    (* the context writer *)
    assert (V3 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m3 b0).
    { intros b0 Hv. apply HVal3, W2, Hv. }
    assert (K4 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m4 b0 ofs = Mem.load ch m b0 ofs).
    { intros ch b0 ofs Hv.
      rewrite HMem4; [apply K3; exact Hv|apply V3; exact Hv|left; apply Fx; exact Hv|left; apply Fm; exact Hv]. }
    assert (Q4 : forall b0 ofs kd p, Mem.perm m b0 ofs kd p -> Mem.perm m4 b0 ofs kd p).
    { intros b0 ofs kd p Hp. assert (Hv : Mem.valid_block m b0) by (eapply Mem.perm_valid_block; exact Hp).
      apply HPerm4; [apply V3; exact Hv|]. apply Q3; [apply Fq, W1; exact Hv|]. apply YP, Q1, XP, Hp. }
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
      apply (add_counter_modu r (Z.of_nat (length lbuf)) (Z.of_nat (length vs)) Hovr Hlbuf HnR). }
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
    { intros b0 ofs kd p Hb Hp. apply HPermE.
      apply HPerm4; [|apply Q3; assumption].
      eapply Mem.perm_valid_block. apply Q3; eassumption. }
    set (le2 := PTree.set _t'1 (Vint (bit_int (negb false))) le0).
    set (le3 := PTree.set _t'3 (Vlong vn) le2).
    set (le5 := PTree.set _t'2 (Vint (bit_int (negb ovf'))) le3).
    exists mf. split; [|split].
    + eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le5) (m2 := m5)
        (out := Out_return (Some (Vint (bit_int (negb ovf')), tbool))).
      * eapply ab_entry; eassumption.
      * rewrite ab_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
        apply HInitEx. unfold ab_rest.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
        { unfold fz_read. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
          - apply HCallRead. exact HRd.
          - eapply exec_Sifthenelse with (b := false);
              [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
            apply exec_Sskip. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
        { unfold ab_readbuf. change le2 with (set_opttemp None Vundef le2) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_read_buffer8) Ptrofs.zero)
            (vargs := [Vptr bb Ptrofs.zero; Vptr bn Ptrofs.zero; Vptr bl Ptrofs.zero; Vint (Int.repr 8)])
            (f := Internal jets.f_simplicity_read_buffer8).
          - reflexivity.
          - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact ab_read_buffer8_symbol]|].
            apply deref_loc_reference; reflexivity.
          - eapply eval_Econs.
            + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
            + reflexivity.
            + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
          - exact ab_read_buffer8_funct.
          - reflexivity.
          - exact HR8. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m4).
        { unfold ab_uchars. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m3).
          - apply exec_Sset. eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|].
            eapply deref_loc_value; [reflexivity|]. exact HLen3.
          - change le3 with (set_opttemp None (Vint (bit_int (negb ovf'))) le3) at 2.
            eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
              (vargs := [Vptr bx Ptrofs.zero; Vptr bb Ptrofs.zero; Vlong vn]) (f := Internal f_sha256_uchars).
            + reflexivity.
            + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact an_uchars_symbol]|].
              apply deref_loc_reference; reflexivity.
            + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs.
              * eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
              * reflexivity.
              * eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
            + exact an_uchars_funct.
            + reflexivity.
            + exact HUc. }
        unfold ab_write. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m5).
        { change le5 with (set_opttemp (Some _t'2) (Vint (bit_int (negb ovf'))) le3).
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
      * unfold e. rewrite ab_blocks. exact HFL.
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
