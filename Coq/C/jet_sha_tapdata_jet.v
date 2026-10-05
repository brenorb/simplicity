(** The jet tapdata_init of the SHA translation unit against the literal
    tapdataInit program.  The C code computes the tag midstate at run time
    (SHA256("TapData"), then one compression of the doubled digest); the
    specification scribes it.  Conditional on the explicit [memcpy_model];
    state premises: dispatch pointer, [sha256_max_counter], and the bytes of
    the constant [tagName]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_bitmachine_rep.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks C.jet_uint32_array_init.
Require Import C.jet_wide C.jet_wide_spec C.jet_sha256_iv_init.
Require Import C.jet_write_sha256_context_layout.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_be64_exec C.jet_sha_be32_write C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_tapdata_spec C.jet_sha_tapdata_prep.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition init_ty : type :=
  Tfunction (Tcons CTXP (Tcons (tptr tuint) Tnil)) tvoid
    {| cc_vararg := None; cc_unproto := false; cc_structret := true |}.
Definition tp_env (bl bt bx bi bz br br1 : block) : env :=
  PTree.set __res__1 (br1, CTX) (PTree.set __res (br, CTX) (PTree.set _ctx__1 (bz, CTX)
    (PTree.set _iv (bi, tarray tuint 8) (PTree.set _ctx (bx, CTX)
      (PTree.set _tapleafTag (bt, MID) (PTree.set _src (bl, FR) empty_env)))))).
Definition tp_init1 : statement :=
  Ssequence
    (Scall None (Evar _sha256_init init_ty)
      [Eaddrof (Evar __res__1 CTX) CTXP; Efield (Evar _tapleafTag MID) _s (tarray tuint 8)])
    (Sassign (Evar _ctx CTX) (Evar __res__1 CTX)).
Definition tp_tag_len : expr :=
  Ebinop Osub (Esizeof (tarray tuchar 8) tulong) (Econst_int (Int.repr 1) tint) tulong.
Definition tp_tag : statement :=
  Ssequence
    (Scall None (Evar _sha256_uchars uchars_ty)
      [Eaddrof (Evar _ctx CTX) CTXP; Evar _tagName (tarray tuchar 8); tp_tag_len])
    (Scall None (Evar _sha256_finalize (Tfunction (Tcons CTXP Tnil) tbool cc_default))
      [Eaddrof (Evar _ctx CTX) CTXP]).
Definition tp_init2 : statement :=
  Ssequence
    (Scall None (Evar _sha256_init init_ty) [Eaddrof (Evar __res CTX) CTXP; Evar _iv (tarray tuint 8)])
    (Sassign (Evar _ctx__1 CTX) (Evar __res CTX)).
Definition tp_hash : statement :=
  Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _ctx__1 CTX) CTXP; Eaddrof (Evar _tapleafTag MID) (tptr MID)].
Definition tp_write : statement :=
  Ssequence
    (Scall (Some _t'1) (Evar _simplicity_write_sha256_context
        (Tfunction (Tcons FRP (Tcons CTXP Tnil)) tbool cc_default))
      [Etempvar _dst FRP; Eaddrof (Evar _ctx__1 CTX) CTXP])
    (Sreturn (Some (Etempvar _t'1 tbool))).
Lemma tp_body :
  fn_body f_simplicity_tapdata_init =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR))
      (Ssequence (Ssequence tp_init1 tp_tag)
        (Ssequence tp_init2 (Ssequence tp_hash (Ssequence tp_hash tp_write)))).
Proof. reflexivity. Qed.

Definition tp_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_tapdata_init)))).

Lemma tp_blocks bl bt bx bi bz br br1 :
  blocks_of_env sha_ge (tp_env bl bt bx bi bz br br1) =
    [(bz, 0, 88); (bx, 0, 88); (bl, 0, 16); (bi, 0, 32); (br1, 0, 88); (br, 0, 88); (bt, 0, 32)].
Proof. vm_compute. reflexivity. Qed.

Lemma tp_tag_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _tagName = Some (sha_symbol_block _tagName).
Proof. vm_compute; reflexivity. Qed.

Lemma tp_entry env m m1 m2 m3 m4 m5 m6 m7 bl bt bx bi bz br br1 bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bt) -> Mem.alloc m2 0 88 = (m3, bx) ->
  Mem.alloc m3 0 32 = (m4, bi) -> Mem.alloc m4 0 88 = (m5, bz) -> Mem.alloc m5 0 88 = (m6, br) ->
  Mem.alloc m6 0 88 = (m7, br1) ->
  function_entry2 sha_ge f_simplicity_tapdata_init
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (tp_env bl bt bx bi bz br br1) (tp_temps env bd dbase bs sbase) m7.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact H1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bt); [change (Mem.alloc m1 0 32 = (m2, bt)); exact H2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bx); [change (Mem.alloc m2 0 88 = (m3, bx)); exact H3|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := bi); [change (Mem.alloc m3 0 32 = (m4, bi)); exact H4|].
    eapply alloc_variables_cons with (m1 := m5) (b1 := bz); [change (Mem.alloc m4 0 88 = (m5, bz)); exact H5|].
    eapply alloc_variables_cons with (m1 := m6) (b1 := br); [change (Mem.alloc m5 0 88 = (m6, br)); exact H6|].
    eapply alloc_variables_cons with (m1 := m7) (b1 := br1); [change (Mem.alloc m6 0 88 = (m7, br1)); exact H7|].
    constructor.
  - reflexivity.
Qed.

Lemma tp_copy m mc bl bt bx bi bz br br1 bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (tp_env bl bt bx bi bz br br1) le m
    (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
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

(** ** Concrete digests in register form *)
Lemma map_unsigned_inj (a b : list int) : map Int.unsigned a = map Int.unsigned b -> a = b.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn in H. injection H as H1 H2. f_equal; [|apply IH; exact H2].
  rewrite <- (Int.repr_unsigned x), <- (Int.repr_unsigned y), H1. reflexivity.
Qed.

Lemma tag_regs :
  snd (absorb_i tag_bytes sha256_iv_words (sha_pad (Int64.repr 7))) = state_regs tag_word.
Proof.
  rewrite (absorb_i_fill tag_bytes sha256_iv_words (sha_pad (Int64.repr 7)))
    by (first [reflexivity|discriminate]).
  cbn [snd]. rewrite <- (map_unsigned_inj _ _ tag_block_bytes).
  rewrite <- iv_word_regs, <- hashBlock_regs, tag_hash_eval. reflexivity.
Qed.

Lemma prefix_regs :
  SHA256.hash_block sha256_iv_words (state_regs tag_word ++ state_regs tag_word) = state_regs tapdata_prefix.
Proof.
  rewrite <- tapdata_prefix_eval, hashBlock_regs, iv_word_regs, block_be_words. reflexivity.
Qed.

Lemma be_words_be_bytes2 a b : be_words (be_bytes a ++ be_bytes b) = a ++ b.
Proof. unfold be_bytes. rewrite <- flat_map_app. apply be_words_be_bytes. Qed.

Lemma iv_words_len : length sha256_iv_words = 8%nat.
Proof. reflexivity. Qed.

Definition sha_tag_ok (m : mem) : Prop :=
  forall i, (i < 7)%nat ->
    Mem.load Mint8unsigned m (sha_symbol_block _tagName) (Z.of_nat i) = Some (Vint (nth i tag_bytes Int.zero)).

Definition sha_jet_local_spec_pre (pre : mem -> Prop) (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    pre m ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall sha_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (encode (spec a)) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B)) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs).

Lemma eval_local_tag_s e le m bt :
  e!_tapleafTag = Some (bt, MID) ->
  eval_expr sha_ge e le m (Efield (Evar _tapleafTag MID) _s (tarray tuint 8)) (Vptr bt Ptrofs.zero).
Proof.
  intros He. eapply eval_Elvalue.
  - eapply eval_Efield_struct with (delta := 0).
    + eapply eval_Elvalue; [apply eval_Evar_local; exact He|apply deref_loc_copy; reflexivity].
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_reference; reflexivity.
Qed.

Ltac nlia :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch T with
      | Z.le _ _ => fail
      | Z.lt _ _ => fail
      | (_ <= _ < _) => fail
      | (_ <= _ <= _) => fail
      | (_ < _ <= _) => fail
      | lt _ _ => fail
      | le _ _ => fail
      | (_ <= _ < _)%nat => fail
      | _ => clear H
      end
  end; lia.

Theorem tapdata_init_local_spec : memcpy_model ->
  sha_jet_local_spec_pre (fun m => sha_globals_ok m /\ sha_tag_ok m)
    f_simplicity_tapdata_init Ty.Unit sha256_ctx8_type
    (fun a => @tapdata_init_spec Alg.CoreFunSem a).
Proof.
  intros Hmodel env m bd dbase bs sbase bi0 bw edge outedge cursor rc []
    [[Hdisp HMaxC] HTag] HSbase HSAlign [HSE HSO] _ _ _ Hout.
  rewrite sha256_ctx8_type_bits in *. change (Z.of_nat 830) with 830 in *.
  rewrite tapdata_init_spec_value.
  set (G := sha_symbol_block _simplicity_sha256_compression) in *.
  set (MAXC := sha_symbol_block _sha256_max_counter) in *.
  set (TAG := sha_symbol_block _tagName) in *.
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (VG : Mem.valid_block m G) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m MAXC) by (eapply load_valid_block; exact HMaxC).
  assert (VT : Mem.valid_block m TAG) by (eapply load_valid_block; exact (HTag 0%nat ltac:(lia))).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 830 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  (* locals *)
  destruct (Mem.alloc m 0 16) as [a1 bl] eqn:A1.
  destruct (Mem.alloc a1 0 32) as [a2 bt] eqn:A2.
  destruct (Mem.alloc a2 0 88) as [a3 bx] eqn:A3.
  destruct (Mem.alloc a3 0 32) as [a4 bi] eqn:A4.
  destruct (Mem.alloc a4 0 88) as [a5 bz] eqn:A5.
  destruct (Mem.alloc a5 0 88) as [a6 br] eqn:A6.
  destruct (Mem.alloc a6 0 88) as [m0 br1] eqn:A7.
  assert (HAL : alloc_list m [16; 32; 88; 32; 88; 88; 88] = (m0, [bl; bt; bx; bi; bz; br; br1])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4, A5, A6, A7. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  assert (Fr : forall b0, Mem.valid_block m b0 ->
    b0 <> bl /\ b0 <> bt /\ b0 <> bx /\ b0 <> bi /\ b0 <> bz /\ b0 <> br /\ b0 <> br1).
  { intros b0 Hv. pose proof (FRh b0 Hv) as HN. cbn in HN. repeat split; intro; subst; apply HN; tauto. }
  inversion FA as [|? ? ? ? [PL0 VL0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PT0 VT0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PX0 VX0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PI0 VI0] FA4]; subst.
  inversion FA4 as [|? ? ? ? [PZ0 VZ0] FA5]; subst.
  inversion FA5 as [|? ? ? ? [PR0 VR0] FA6]; subst.
  inversion FA6 as [|? ? ? ? [PR10 VR10] FA7]; subst. clear FA FA1 FA2 FA3 FA4 FA5 FA6 FA7.
  assert (D : forall x y, In x [bl; bt; bx; bi; bz; br; br1] -> In y [bl; bt; bx; bi; bz; br; br1] ->
    x = y \/ x <> y) by (intros x y _ _; destruct (peq x y); auto).
  assert (Hlt : bl <> bt /\ bl <> bx /\ bl <> bi /\ bl <> bz /\ bl <> br /\ bl <> br1 /\
                bt <> bx /\ bt <> bi /\ bt <> bz /\ bt <> br /\ bt <> br1 /\
                bx <> bi /\ bx <> bz /\ bx <> br /\ bx <> br1 /\
                bi <> bz /\ bi <> br /\ bi <> br1 /\ bz <> br /\ bz <> br1 /\ br <> br1).
  { clear - ND.
    repeat (apply NoDup_cons_iff in ND; destruct ND as [? ND]). cbn in *. intuition congruence. }
  destruct Hlt as (Nlt & Nlx & Nli & Nlz & Nlr & Nlr1 & Ntx & Nti & Ntz & Ntr & Ntr1 &
    Nxi & Nxz & Nxr & Nxr1 & Niz & Nir & Nir1 & Nzr & Nzr1 & Nrr1).
  clear HAL D ND FRh.
  set (e := tp_env bl bt bx bi bz br br1).
  set (le0 := tp_temps env bd dbase bs sbase).
  (* the frame copy *)
  assert (HSE0 : Mem.load Mptr m0 bs sbase = Some (Vptr bi0 (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSO0 : Mem.load Mint64 m0 bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_loadbytes_at m0 bs sbase _ _ HSE0 HSO0) as [bytes HB0].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB0) as Hbyteslen.
  assert (PLW : Mem.range_perm m0 bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm m0 bl 0 16 Cur Writable).
    intros ofs Hr. eapply Mem.perm_implies; [apply PL0; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m0 bl 0 bytes PLW) as [mc SC].
  assert (Kc : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mc b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. erewrite Mem.load_storebytes_other; [|exact SC|left; apply (Fr b0 Hv)].
    apply XL. exact Hv. }
  assert (Pc : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm mc b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; eauto. }
  assert (Vc : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block mc b0).
  { intros b0 Hv. eapply Mem.storebytes_valid_block_1; eauto. }
  assert (HCopy : Clight2.exec_stmt sha_ge e le0 m0 (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le0 mc Out_normal).
  { eapply tp_copy; [exact HSbase|exact HSAlign| |reflexivity|exact HB0|exact SC].
    intro Heq. apply (proj1 (Fr bs Vs)). congruence. }
  assert (WR : forall b0 z mm, (forall b1 ofs kd p, Mem.perm m0 b1 ofs kd p -> Mem.perm mm b1 ofs kd p) ->
    Mem.range_perm m0 b0 0 z Cur Freeable -> Mem.range_perm mm b0 0 z Cur Writable).
  { intros b0 z mm HPm HF ofs Ho. apply HPm. eapply Mem.perm_implies; [apply HF; exact Ho|constructor]. }
  (* first context: init, copy *)
  destruct (sha_init_copy mc br1 bx bt 0 (not_eq_sym Ntr1) (not_eq_sym Ntx) (not_eq_sym Nxr1)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(exists 0; reflexivity)
    (WR br1 88 mc Pc PR10) (WR bx 88 mc Pc PX0) (WR bt 32 mc Pc PT0))
    as (mi1 & m1 & bytes1 & HInit1 & HLB1 & HSB1 & HOut1 & HCnt1 & HOvf1 & HArr1 & HMem1 & HPerm1 & HVal1).
  assert (K1 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m1 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. destruct (Fr b0 Hv) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    rewrite HMem1; [apply Kc; exact Hv|apply Vc, XV; exact Hv|exact F7|exact F3|left; exact F2]. }
  assert (P1 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m1 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm1, Pc, Hp. }
  assert (V1 : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block m1 b0).
  { intros b0 Hv. apply HVal1, Vc, Hv. }
  (* the tag *)
  pose proof (eval_sha256_uchars Hmodel m1 bx 0 bt 0 TAG Ptrofs.zero [] sha256_iv_words tag_bytes Int64.zero false
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; nlia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; nlia)
    Ntx (proj1 (proj2 (proj2 (Fr TAG VT)))) (proj1 (proj2 (Fr TAG VT)))
    (proj1 (proj2 (proj2 (Fr G VG)))) (proj1 (proj2 (Fr G VG)))) as HU.
  cbv zeta in HU.
  destruct HU as (m2 & HUc & HOut2 & HCnt2 & HOvf2 & HBlk2 & HReg2 & HMem2 & HPerm2 & HVal2).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. cbn [tag_bytes map length].
    change Ptrofs.max_unsigned with 18446744073709551615. nlia. }
  { exact iv_words_len. }
  { exact HOut1. }
  { exact HCnt1. }
  { reflexivity. }
  { exact HOvf1. }
  { intros i Hi. exfalso. clear - Hi. cbn in Hi. nlia. }
  { intros i Hi. split.
    - apply (u32_nth m1 bt 0 sha256_iv_words HArr1). rewrite iv_words_len. exact Hi.
    - split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; nlia].
      intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
      eapply Mem.perm_implies with (p1 := Freeable); [apply P1, PT0; nlia|constructor]. }
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Z.add_0_l.
    rewrite K1 by exact VT. apply HTag. exact Hi. }
  { unfold sha_dispatch_ok. fold G. rewrite K1 by exact VG. exact Hdisp. }
  { fold MAXC. rewrite K1 by exact VM. exact HMaxC. }
  { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [apply P1, PX0; nlia|constructor]. }
  { exists 0. reflexivity. }
  change (Int64.repr (Z.of_nat (length tag_bytes))) with (Int64.repr 7) in HUc, HCnt2, HOvf2.
  rewrite (absorb_i_small tag_bytes [] sha256_iv_words) in HBlk2, HReg2 by (cbn; nlia).
  cbn [fst snd app] in HBlk2, HReg2.
  set (c1 := Int64.add Int64.zero (Int64.repr 7)) in *.
  set (ovf1 := uc_overflow false Int64.zero (Int64.repr 7)) in *.
  assert (V2 : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HVal2, V1, Hv. }
  assert (P2 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m2 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm2; [apply V1; eapply Mem.perm_valid_block; exact Hp|apply P1, Hp]. }
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. destruct (Fr b0 Hv) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    rewrite HMem2; [apply K1; exact Hv|apply V1, XV; exact Hv|left; exact F3|left; exact F2]. }
  destruct (eval_sha256_finalize Hmodel m2 bx 0 bt 0 tag_bytes sha256_iv_words c1 ovf1
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; nlia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; nlia)
    Ntx (proj1 (proj2 (proj2 (Fr G VG)))) (proj1 (proj2 (Fr G VG)))
    (proj1 (proj2 (proj2 (Fr MAXC VM)))) (proj1 (proj2 (Fr MAXC VM)))
    iv_words_len HOut2 HCnt2 ltac:(reflexivity) HOvf2 HBlk2)
    as (m3 & HFin & HReg3 & HMem3 & HPerm3 & HVal3).
  { intros i Hi. split; [apply HReg2; exact Hi|].
    split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; nlia].
    intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
    eapply Mem.perm_implies with (p1 := Freeable); [apply P2, PT0; nlia|constructor]. }
  { unfold sha_dispatch_ok. fold G. rewrite K2 by exact VG. exact Hdisp. }
  { fold MAXC. rewrite K2 by exact VM. exact HMaxC. }
  { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [apply P2, PX0; nlia|constructor]. }
  { exists 0. reflexivity. }
  change (sha_pad c1) with (sha_pad (Int64.repr 7)) in HReg3. rewrite tag_regs in HReg3.
  set (T := state_regs tag_word) in *.
  assert (HTLen : length T = 8%nat) by reflexivity.
  assert (V3 : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block m3 b0).
  { intros b0 Hv. apply HVal3, V2, Hv. }
  assert (P3 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m3 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm3; [apply V2; eapply Mem.perm_valid_block; exact Hp|apply P2, Hp]. }
  assert (K3 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m3 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. destruct (Fr b0 Hv) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    rewrite HMem3; [apply K2; exact Hv|apply V2, XV; exact Hv|left; exact F3|left; exact F2]. }
  (* second context: init, copy *)
  destruct (sha_init_copy m3 br bz bi 0 (not_eq_sym Nir) (not_eq_sym Niz) (not_eq_sym Nzr)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; nlia) ltac:(exists 0; reflexivity)
    (WR br 88 m3 P3 PR0) (WR bz 88 m3 P3 PZ0) (WR bi 32 m3 P3 PI0))
    as (mi2 & m4 & bytes2 & HInit2 & HLB2 & HSB2 & HOut4 & HCnt4 & HOvf4 & HArr4 & HMem4 & HPerm4 & HVal4).
  assert (V4 : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block m4 b0).
  { intros b0 Hv. apply HVal4, V3, Hv. }
  assert (P4 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m4 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm4, P3, Hp. }
  assert (K4 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m4 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. destruct (Fr b0 Hv) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    rewrite HMem4; [apply K3; exact Hv|apply V3, XV; exact Hv|exact F6|exact F5|left; exact F4]. }
  assert (HT4 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m4 bt (Ptrofs.unsigned Ptrofs.zero + 4 * Z.of_nat j) = Some (Vint (nth j T Int.zero))).
  { intros j Hj. change (Ptrofs.unsigned Ptrofs.zero) with 0.
    rewrite HMem4; [apply HReg3; exact Hj|apply V3; exact VT0|exact Ntr|exact Ntz|left; exact Nti]. }
  assert (HbT : length (be_bytes T) = 32%nat) by (rewrite be_bytes_length, HTLen; reflexivity).
  pose proof (eval_sha256_hash Hmodel m4 bz 0 bi 0 bt Ptrofs.zero [] sha256_iv_words T Int64.zero false
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Niz (proj1 (proj2 (proj2 (proj2 (proj2 (Fr G VG)))))) (proj1 (proj2 (proj2 (proj2 (Fr G VG)))))
    iv_words_len HTLen
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    HT4 HOut4 HCnt4 ltac:(reflexivity) HOvf4) as HH1.
  cbv zeta in HH1.
  destruct HH1 as (m5 & HHc5 & HOut5 & HCnt5 & HOvf5 & HBlk5 & HReg5 & HMem5 & HPerm5 & HVal5).
  { intros i Hi. exfalso. clear - Hi. cbn in Hi. lia. }
  { intros i Hi. split.
    - apply (u32_nth m4 bi 0 sha256_iv_words HArr4). rewrite iv_words_len. exact Hi.
    - split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; nlia].
      intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
      eapply Mem.perm_implies with (p1 := Freeable); [apply P4, PI0; nlia|constructor]. }
  { unfold sha_dispatch_ok. fold G. rewrite K4 by exact VG. exact Hdisp. }
  { fold MAXC. rewrite K4 by exact VM. exact HMaxC. }
  { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [apply P4, PZ0; nlia|constructor]. }
  { exists 0. reflexivity. }
  rewrite (absorb_i_small (be_bytes T) [] sha256_iv_words) in HBlk5, HReg5 by (rewrite HbT; cbn; lia).
  cbn [fst snd app] in HBlk5, HReg5.
  set (c5 := Int64.add Int64.zero (Int64.repr 32)) in *.
  set (ovf5 := uc_overflow false Int64.zero (Int64.repr 32)) in *.
  assert (V5 : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block m5 b0).
  { intros b0 Hv. apply HVal5, V4, Hv. }
  assert (P5 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m5 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm5; [apply V4; eapply Mem.perm_valid_block; exact Hp|apply P4, Hp]. }
  assert (K5 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m5 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. destruct (Fr b0 Hv) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    rewrite HMem5; [apply K4; exact Hv|apply V4, XV; exact Hv|left; exact F5|left; exact F4]. }
  assert (HT5 : forall j, (j < 8)%nat ->
    Mem.load Mint32 m5 bt (Ptrofs.unsigned Ptrofs.zero + 4 * Z.of_nat j) = Some (Vint (nth j T Int.zero))).
  { intros j Hj. rewrite HMem5; [apply HT4; exact Hj|apply V4; exact VT0|left; exact Ntz|left; exact Nti]. }
  pose proof (eval_sha256_hash Hmodel m5 bz 0 bi 0 bt Ptrofs.zero (be_bytes T) sha256_iv_words T c5 ovf5
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Niz (proj1 (proj2 (proj2 (proj2 (proj2 (Fr G VG)))))) (proj1 (proj2 (proj2 (proj2 (Fr G VG)))))
    iv_words_len HTLen
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    HT5 HOut5 HCnt5 ltac:(rewrite HbT; reflexivity) HOvf5 HBlk5) as HH2.
  cbv zeta in HH2.
  destruct HH2 as (m6 & HHc6 & HOut6 & HCnt6 & HOvf6 & HBlk6 & HReg6 & HMem6 & HPerm6 & HVal6).
  { intros i Hi. split; [apply HReg5; exact Hi|].
    split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; nlia].
    intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
    eapply Mem.perm_implies with (p1 := Freeable); [apply P5, PI0; nlia|constructor]. }
  { unfold sha_dispatch_ok. fold G. rewrite K5 by exact VG. exact Hdisp. }
  { fold MAXC. rewrite K5 by exact VM. exact HMaxC. }
  { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [apply P5, PZ0; nlia|constructor]. }
  { exists 0. reflexivity. }
  assert (HAbs : absorb_i (be_bytes T) sha256_iv_words (be_bytes T) = ([], state_regs tapdata_prefix)).
  { rewrite (absorb_i_fill (be_bytes T) sha256_iv_words (be_bytes T)).
    - rewrite be_words_be_bytes2. unfold T. rewrite prefix_regs. reflexivity.
    - rewrite HbT. reflexivity.
    - intro HN. rewrite HN in HbT. discriminate HbT. }
  rewrite HAbs in HBlk6, HReg6. cbn [fst snd] in HBlk6, HReg6.
  set (c6 := Int64.add c5 (Int64.repr 32)) in *.
  assert (Hovf6 : uc_overflow ovf5 c5 (Int64.repr 32) = false) by (vm_compute; reflexivity).
  rewrite Hovf6 in HOvf6.
  assert (V6 : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block m6 b0).
  { intros b0 Hv. apply HVal6, V5, Hv. }
  assert (P6 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m6 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm6; [apply V5; eapply Mem.perm_valid_block; exact Hp|apply P5, Hp]. }
  assert (K6 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m6 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. destruct (Fr b0 Hv) as (F1 & F2 & F3 & F4 & F5 & F6 & F7).
    rewrite HMem6; [apply K5; exact Hv|apply V5, XV; exact Hv|left; exact F5|left; exact F4]. }
  (* the context writer *)
  assert (HOutW : write_frame_at m6 bd dbase bw outedge cursor 830).
  { eapply write_frame_at_preserved; [| |exact Hout].
    - intros ch b0 ofs v0 Hb HL. rewrite K6; [exact HL|destruct Hb; subst; assumption].
    - intros b0 ofs kd p Hp. apply P6, XP, Hp. }
  assert (HArrW : uint8_array_at m6 bz (0 + 16)
    (map word8_array_value (byte_chunks_values (buffer_byte_chunks 5 (buffer_empty_value (Word 3) 5))))).
  { intros i x Hi. destruct i; discriminate Hi. }
  assert (HStW : uint32_array_at m6 bi 0 (map word32_array_value (word32_chunks 3 tapdata_prefix))).
  { change (map word32_array_value (word32_chunks 3 tapdata_prefix)) with (state_regs tapdata_prefix).
    apply u32_of_nth. intros i Hi. apply HReg6. exact Hi. }
  destruct (eval_write_sha256_context_layout m6 bd dbase bw outedge cursor bz 0 bi 0 c6 false
    (buffer_empty_value (Word 3) 5) tapdata_prefix
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    (not_eq_sym (proj1 (proj2 (proj2 (proj2 (proj2 (Fr bd Vd)))))))
    (not_eq_sym (proj1 (proj2 (proj2 (proj2 (proj2 (Fr bw Vw)))))))
    (not_eq_sym (proj1 (proj2 (proj2 (proj2 (Fr bd Vd))))))
    (not_eq_sym (proj1 (proj2 (proj2 (proj2 (Fr bw Vw))))))
    HCnt6 HOut6 HOvf6 HArrW ltac:(reflexivity) HStW HOutW)
    as (m7 & HWr & HCells & HPrefix & HFldE & HLoadsE & HPermE & HValE).
  apply (sha_transport_call _ _ sg_in_write_context) in HWr.
  destruct (free_list_blocks
    [(bz, 0, 88); (bx, 0, 88); (bl, 0, 16); (bi, 0, 32); (br1, 0, 88); (br, 0, 88); (bt, 0, 32)] m7)
    as (mf & HFL & HLf & _ & _).
  { intros b0 lo hi Hin0. cbn in Hin0.
    destruct Hin0 as [Heq|[Heq|[Heq|[Heq|[Heq|[Heq|[Heq|[]]]]]]]]; injection Heq as <- <- <-;
      intros ofs Hr0; apply HPermE, P6; [apply PZ0|apply PX0|apply PL0|apply PI0|apply PR10|apply PR0|apply PT0];
      exact Hr0. }
  { cbn. repeat constructor; cbn; intuition congruence. }
  assert (HNl : forall b0, Mem.valid_block m b0 ->
    ~ In b0 (map (fun x => fst (fst x))
      [(bz, 0, 88); (bx, 0, 88); (bl, 0, 16); (bi, 0, 32); (br1, 0, 88); (br, 0, 88); (bt, 0, 32)])).
  { intros b0 Hv. destruct (Fr b0 Hv) as (F1 & F2 & F3 & F4 & F5 & F6 & F7). cbn. intuition congruence. }
  set (le7 := PTree.set _t'1 (Vint (bit_int (negb false))) le0).
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le7) (m2 := m7)
      (out := Out_return (Some (Vint (bit_int (negb false)), tbool))).
    + eapply tp_entry; eassumption.
    + rewrite tp_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m3).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m1).
        - unfold tp_init1. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mi1).
          + change le0 with (set_opttemp None Vundef le0) at 2.
            eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_init) Ptrofs.zero)
              (vargs := [Vptr br1 Ptrofs.zero; Vptr bt Ptrofs.zero]) (f := Internal jets.f_sha256_init).
            * reflexivity.
            * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tap_init_symbol]|].
              apply deref_loc_reference; reflexivity.
            * eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs; [apply eval_local_tag_s; reflexivity|reflexivity|apply eval_Enil].
            * exact tap_init_funct.
            * reflexivity.
            * exact HInit1.
          + eapply (exec_ctx_struct_copy e le0 mi1 m1 _ctx __res__1 bx br1 bytes1);
              [reflexivity|reflexivity|exact Nxr1|exact HLB1|exact HSB1].
        - unfold tp_tag. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m2).
          + change le0 with (set_opttemp None (Vint (bit_int (negb ovf1))) le0) at 2.
            eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
              (vargs := [Vptr bx Ptrofs.zero; Vptr TAG Ptrofs.zero; Vlong (Int64.repr 7)])
              (f := Internal f_sha256_uchars).
            * reflexivity.
            * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_uchars_symbol]|].
              apply deref_loc_reference; reflexivity.
            * eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs.
              -- eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tp_tag_symbol]|].
                 apply deref_loc_reference; reflexivity.
              -- reflexivity.
              -- eapply eval_Econs with (v1 := Vlong (Int64.repr 7)); [|reflexivity|apply eval_Enil].
                 unfold tp_tag_len.
                 eapply eval_Ebinop; [apply eval_Esizeof|apply eval_Econst_int|reflexivity].
            * exact sha_uchars_funct.
            * reflexivity.
            * exact HUc.
          + change le0 with (set_opttemp None (Vint (bit_int (negb ovf1))) le0) at 2.
            eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_finalize) Ptrofs.zero)
              (vargs := [Vptr bx Ptrofs.zero]) (f := Internal f_sha256_finalize).
            * reflexivity.
            * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_finalize_symbol]|].
              apply deref_loc_reference; reflexivity.
            * eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
            * exact sha_finalize_funct.
            * reflexivity.
            * exact HFin. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m4).
      { unfold tp_init2. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mi2).
        - change le0 with (set_opttemp None Vundef le0) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_init) Ptrofs.zero)
            (vargs := [Vptr br Ptrofs.zero; Vptr bi Ptrofs.zero]) (f := Internal jets.f_sha256_init).
          + reflexivity.
          + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tap_init_symbol]|].
            apply deref_loc_reference; reflexivity.
          + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
            eapply eval_Econs with (v1 := Vptr bi Ptrofs.zero); [|reflexivity|apply eval_Enil].
            eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
          + exact tap_init_funct.
          + reflexivity.
          + exact HInit2.
        - eapply (exec_ctx_struct_copy e le0 mi2 m4 _ctx__1 __res bz br bytes2);
            [reflexivity|reflexivity|exact Nzr|exact HLB2|exact HSB2]. }
      assert (HHashCall : forall ma mb,
        Clight2.eval_funcall sha_ge ma (Internal f_sha256_hash) [Vptr bz (Ptrofs.repr 0); Vptr bt Ptrofs.zero] E0 mb Vundef ->
        Clight2.exec_stmt sha_ge e le0 ma tp_hash E0 le0 mb Out_normal).
      { intros ma mb HC. unfold tp_hash. change le0 with (set_opttemp None Vundef le0) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_hash) Ptrofs.zero)
          (vargs := [Vptr bz Ptrofs.zero; Vptr bt Ptrofs.zero]) (f := Internal f_sha256_hash).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_hash_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
          eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        - exact sha_hash_funct.
        - reflexivity.
        - exact HC. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m5); [apply HHashCall; exact HHc5|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m6); [apply HHashCall; exact HHc6|].
      unfold tp_write. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le7) (m1 := m7).
      { change le7 with (set_opttemp (Some _t'1) (Vint (bit_int (negb false))) le0).
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_write_sha256_context) Ptrofs.zero)
          (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bz Ptrofs.zero])
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
    + cbn. split; [discriminate|reflexivity].
    + unfold e. rewrite tp_blocks. exact HFL.
  - assert (HOne : decode_wide W64 (Int64.zero_ext 64 (Int64.shru c6 (Int64.repr 6))) = one64)
      by (vm_compute; reflexivity).
    rewrite HOne in HCells.
    eapply frame_output_cells_preserved; [|exact HCells].
    intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - eapply write_prefix_at_preserved; [| |exact HPrefix].
    + intros ofs w HL. rewrite K6 by exact Vw. exact HL.
    + intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - destruct HFldE as [HE1 HE2]. split; rewrite HLf by (apply HNl; exact Vd); assumption.
  - intros ch b0 ofs Hv Hd Hw. rewrite HLf by (apply HNl; exact Hv).
    rewrite HLoadsE by assumption. apply K6; exact Hv.
Qed.
