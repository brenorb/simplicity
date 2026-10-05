(** The Bitcoin jet build_tapleaf_simplicity against the literal
    buildTapleafSimplicity program.  Conditional on [memcpy_model]; state
    premises: the dispatch pointer, the counter bound and the "TapLeaf" tag
    name global. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding.
Require Import C.jet_buffer_input C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_struct_copy_loads C.jet_write32s_layout.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_exec C.jet_sha_be32_write.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_finalize_exec.
Require Import C.jet_constant_layout C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_tapdata_prep C.jet_sha_tapdata_spec C.jet_sha_tapdata_jet.
Require Import C.jet_sha_ctx8_finalize_jet C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_tagged_ctx C.jet_sha_hash_io.
Require Import C.jet_bitcoin_tapleaf_hash_spec C.jet_bitcoin_build_tapleaf_spec C.jet_bitcoin_make_tapleaf_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Definition btl_env (bl bcm brs brr : block) : env :=
  PTree.set __res (brr, MID) (PTree.set _result (brs, MID)
    (PTree.set _cmr (bcm, MID) (PTree.set _src (bl, FR) empty_env))).

Definition btl_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_bitcoin_build_tapleaf_simplicity)))).

Lemma btl_blocks bl bcm brs brr :
  blocks_of_env sha_ge (btl_env bl bcm brs brr) = [(bcm, 0, 32); (bl, 0, 16); (brr, 0, 32); (brs, 0, 32)].
Proof. vm_compute. reflexivity. Qed.

Lemma btl_entry env m m1 m2 m3 m4 bl bcm brs brr bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bcm) -> Mem.alloc m2 0 32 = (m3, brs) ->
  Mem.alloc m3 0 32 = (m4, brr) ->
  function_entry2 sha_ge f_simplicity_bitcoin_build_tapleaf_simplicity
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (btl_env bl bcm brs brr) (btl_temps env bd dbase bs sbase) m4.
Proof.
  intros HA HB HC HD. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HY. contradiction.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact HA|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bcm); [change (Mem.alloc m1 0 32 = (m2, bcm)); exact HB|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := brs); [change (Mem.alloc m2 0 32 = (m3, brs)); exact HC|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := brr); [change (Mem.alloc m3 0 32 = (m4, brr)); exact HD|].
    constructor.
  - reflexivity.
Qed.

Lemma btl_copy m mc bl bcm brs brr bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (btl_env bl bcm brs brr) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
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

Lemma btl_make_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_bitcoin_make_tapleaf =
    Some (sha_symbol_block _simplicity_bitcoin_make_tapleaf).
Proof. vm_compute; reflexivity. Qed.
Lemma btl_make_funct :
  Genv.find_funct (Clight.genv_genv sha_ge)
    (Vptr (sha_symbol_block _simplicity_bitcoin_make_tapleaf) Ptrofs.zero) =
    Some (Internal f_simplicity_bitcoin_make_tapleaf).
Proof. vm_compute; reflexivity. Qed.

Lemma btl_cast190 m : sem_cast (Vint (Int.repr 190)) tint tuchar m = Some (Vint (Int.repr 190)).
Proof. vm_compute. reflexivity. Qed.
Lemma btl_ext190 : Int.zero_ext 8 (Int.repr 190) = Int.repr 190.
Proof. vm_compute. reflexivity. Qed.

Local Opaque sha_ge ge0.

(** ** The value: the C tagged hash is the specification's block hash *)
Lemma map_unsigned_inj' (a b : list int) : map Int.unsigned a = map Int.unsigned b -> a = b.
Proof.
  revert b. induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [|apply IH; exact H2].
  rewrite <- (Int.repr_unsigned x), <- (Int.repr_unsigned y), H1. reflexivity.
Qed.

Lemma btl_tag_regs : tag_regs_of tapleaf_tag_ints = state_regs tapleaf_tag_word.
Proof.
  unfold tag_regs_of. change (Int64.repr (Z.of_nat (length tapleaf_tag_ints))) with (Int64.repr 7).
  rewrite (absorb_i_fill tapleaf_tag_ints sha256_iv_words (sha_pad (Int64.repr 7)))
    by (first [reflexivity|discriminate]).
  cbn [snd]. change tapleaf_tag_ints with tapleaf_tag_bytes.
  rewrite <- (map_unsigned_inj' _ _ tapleaf_tag_block_bytes).
  rewrite <- iv_word_regs, <- hashBlock_regs, tapleaf_tag_hash_eval. reflexivity.
Qed.

Lemma btl_prefix_regs : tagged_prefix tapleaf_tag_ints = state_regs tapleaf_prefix.
Proof.
  unfold tagged_prefix. rewrite btl_tag_regs.
  rewrite <- tapleaf_prefix_eval, hashBlock_regs, iv_word_regs, block_be_words. reflexivity.
Qed.

Lemma btl_const_bytes :
  map Int.unsigned (map word8_array_value ([tl_version; byte32])) =
    map Int.unsigned [Int.repr 190; Int.repr 32].
Proof. vm_compute. reflexivity. Qed.

Lemma btl_pad_bytes :
  map Int.unsigned (map word8_array_value tl_pad) = map Int.unsigned (sha_pad (Int64.repr 98)).
Proof. vm_compute. reflexivity. Qed.

Theorem build_tapleaf_regs (a : Ty.tySem (Word 8)) :
  make_tapleaf_regs (Int.repr 190) (state_regs a) =
    state_regs (@build_tapleaf_spec Alg.CoreFunSem a).
Proof.
  assert (HS : length (state_regs a) = 8%nat).
  { unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
  unfold make_tapleaf_regs.
  rewrite absorb_i_fill.
  2:{ rewrite app_length, be_bytes_length, HS. reflexivity. }
  2:{ discriminate. }
  cbn [snd]. rewrite btl_prefix_regs, build_tapleaf_spec_value, hashBlock_regs.
  do 2 f_equal. rewrite build_tapleaf_block_bytes, !map_app, be_bytes_state_regs.
  rewrite (map_unsigned_inj' _ _ btl_const_bytes), (map_unsigned_inj' _ _ btl_pad_bytes).
  rewrite <- app_assoc. reflexivity.
Qed.

Lemma state_regs_cells (w : Ty.tySem (Word 8)) : uint32_word_cells (state_regs w) = encode w.
Proof.
  rewrite <- (from_to_hash256 w) at 2. rewrite <- uint32_cells_from_hash256, hash256_reg_chunks.
  reflexivity.
Qed.

Definition sha_tapleaf_pre (m : mem) : Prop := sha_globals_ok m /\ sha_tapleaf_tag_ok m.

Theorem bitcoin_build_tapleaf_simplicity_local_spec : memcpy_model ->
  sha_jet_local_spec_pre sha_tapleaf_pre f_simplicity_bitcoin_build_tapleaf_simplicity
    (Word 8) (Word 8) (fun a => @build_tapleaf_spec Alg.CoreFunSem a).
Proof.
  intros Hmodel env m bd dbase bs sbase bi bw edge outedge cursor rc a
    [[Hdisp HMaxC] HTag] HSbase HSAlign [HSE HSO] H0 Hmax Hin Hout.
  change (rc + 256 <= Int64.max_unsigned) in Hmax.
  change (write_frame_at m bd dbase bw outedge cursor 256) in Hout.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  set (hs := word32_chunks 3 a).
  assert (Hlh : length hs = 8%nat) by (apply (word32_chunks_length 3)).
  assert (Hwh : forall j v, nth_error hs j = Some v -> frame_input_word_at m bi edge (rc + 32 * Z.of_nat j) v)
    by (apply (frame_input_word32_chunks m bi edge rc 3 a); exact Hin).
  assert (Vi : Mem.valid_block m bi).
  { eapply frame_input_cells_valid; [|exact Hin]. intro HN.
    apply (f_equal (@length Cell)) in HN. rewrite encode_length in HN. discriminate HN. }
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 256 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  (* locals *)
  destruct (Mem.alloc m 0 16) as [ma1 bl] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 bcm] eqn:A2.
  destruct (Mem.alloc ma2 0 32) as [ma3 brs] eqn:A3.
  destruct (Mem.alloc ma3 0 32) as [m0 brr] eqn:A4.
  assert (HAL : alloc_list m [16; 32; 32; 32] = (m0, [bl; bcm; brs; brr])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PL0 VL0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PC0 VC0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PS0 VS0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PR0 VR0] FA4]; subst. clear FA FA1 FA2 FA3 FA4 HAL.
  pose proof ND as ND0.
  apply NoDup_cons_iff in ND. destruct ND as [N1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N2 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N3 _].
  pose proof (FRh bi Vi) as Nbi. pose proof (FRh bs Vs) as Nbs.
  pose proof (FRh bd Vd) as Nbd. pose proof (FRh bw Vw) as Nbw.
  set (e := btl_env bl bcm brs brr).
  set (le := btl_temps env bd dbase bs sbase).
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
  destruct (Mem.range_perm_storebytes m0 bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at m0 mc bs sbase bl bytes _ _ HB0 SC HSE0 HSO0) as [HLE HLO].
  assert (Kc : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mc b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    erewrite Mem.load_storebytes_other; [|exact SC|left; ne]. apply XL. exact Hv. }
  assert (Pc : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm mc b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; eauto. }
  assert (Vc : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block mc b0).
  { intros b0 Hv. eapply Mem.storebytes_valid_block_1; eauto. }
  assert (HCopy : Clight2.exec_stmt sha_ge e le m0 (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal).
  { apply (btl_copy m0 mc bl bcm brs brr bs sbase bytes le); [exact HSbase|exact HSAlign|ne|reflexivity|exact HB0|exact SC]. }
  (* readHash *)
  destruct (eval_sha_readHash mc bcm 0 bl 0 bi edge rc hs Hlh ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(exists 0; reflexivity))
    as (m1 & HRd & HArr1 & HFld1 & HMem1 & HPerm1 & HVal1).
  { intros ofs Hr. eapply Mem.perm_implies; [apply Pc, PC0; lia|constructor]. }
  { ne. }
  { ne. }
  { ne. }
  { exact HLocalBase. }
  { exact H0. }
  { exact Hmax. }
  { split; [exact HLE|exact HLO]. }
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies; [apply Pc, PL0; lia|constructor]. }
  { intros i x Hi. eapply frame_input_bits_at_preserved; [|exact (Hwh i x Hi)].
    intros ofs w HL. rewrite Kc by exact Vi. exact HL. }
  fold (state_regs a) in HArr1.
  assert (K1 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m1 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite HMem1; [apply Kc; exact Hv|left; ne|left; ne]. }
  assert (P1 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m1 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm1, Pc, Hp. }
  assert (V1 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m1 b0).
  { intros b0 Hv. apply HVal1, Vc, XV, Hv. }
  (* make_tapleaf *)
  assert (HSR : length (state_regs a) = 8%nat).
  { unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
  destruct (eval_make_tapleaf Hmodel m1 brr 0 (Int.repr 190) bcm Ptrofs.zero (state_regs a)
    btl_ext190 ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(exists 0; reflexivity))
    as (m2 & HMk & HReg2 & HMem2 & HPerm2 & HVal2).
  { intros ofs Hr. eapply Mem.perm_implies; [apply P1, PR0; lia|constructor]. }
  { exact HSR. }
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { intros j Hj. change (Ptrofs.unsigned Ptrofs.zero) with 0.
    apply (u32_nth m1 bcm 0 (state_regs a) HArr1). rewrite HSR. exact Hj. }
  { unfold sha_dispatch_ok. rewrite K1; [exact Hdisp|eapply load_valid_block; exact Hdisp]. }
  { rewrite K1; [exact HMaxC|eapply load_valid_block; exact HMaxC]. }
  { intros i Hi. rewrite K1; [apply HTag; exact Hi|eapply load_valid_block; exact (HTag 0%nat ltac:(lia))]. }
  rewrite build_tapleaf_regs in HReg2.
  set (res := @build_tapleaf_spec Alg.CoreFunSem a) in *.
  assert (HRL : length (state_regs res) = 8%nat).
  { unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite HMem2; [apply K1; exact Hv|apply V1; exact Hv|left; ne]. }
  assert (P2 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m2 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm2, P1, Hp. }
  (* result = __res *)
  assert (PRd : Mem.range_perm m2 brr 0 32 Cur Readable).
  { intros ofs Hr. eapply Mem.perm_implies; [apply P2, PR0, Hr|constructor]. }
  destruct (Mem.range_perm_loadbytes m2 brr 0 32 PRd) as (rbytes & HRB).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HRB) as HRBL.
  assert (PWr : Mem.range_perm m2 brs 0 (0 + Z.of_nat (length rbytes)) Cur Writable).
  { rewrite HRBL. change (0 + Z.of_nat (Z.to_nat 32)) with 32. intros ofs Hr.
    eapply Mem.perm_implies; [apply P2, PS0, Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m2 brs 0 rbytes PWr) as (m3 & HRS).
  assert (HRB3 : Mem.loadbytes m3 brs 0 32 = Some rbytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HRS) as H. rewrite HRBL in H. exact H. }
  assert (HArr3 : uint32_array_at m3 brs 0 (state_regs res)).
  { apply u32_of_nth. intros j Hj. rewrite HRL in Hj.
    apply (equal_loadbytes_field Mint32 m2 m3 brr brs 0 0 32 (4 * Z.of_nat j) rbytes).
    - lia.
    - change (size_chunk Mint32) with 4. lia.
    - exact HRB.
    - exact HRB3.
    - change (align_chunk Mint32) with 4. exists (Z.of_nat j). lia.
    - apply HReg2. exact Hj. }
  assert (K3 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m3 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite (Mem.load_storebytes_other _ _ _ _ _ HRS) by (left; ne). apply K2. exact Hv. }
  assert (P3 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m3 b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; [exact HRS|apply P2, Hp]. }
  (* writeHash *)
  assert (HOut3 : write_frame_at m3 bd dbase bw outedge cursor 256).
  { eapply write_frame_at_preserved; [| |exact Hout].
    - intros ch b0 ofs v0 Hb HL. rewrite K3; [exact HL|destruct Hb; subst; assumption].
    - intros b0 ofs kd p Hp. apply P3, XP, Hp. }
  destruct (eval_sha_writeHash m3 brs 0 bd dbase bw outedge cursor (state_regs res) HRL ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(ne) ltac:(ne) HArr3 HOut3)
    as (m4 & HWr & HCells & HPrefix & HFldE & HLoadsE & HPermE & HValE).
  rewrite state_regs_cells in HCells.
  (* freeing the locals *)
  destruct (free_list_blocks [(bcm, 0, 32); (bl, 0, 16); (brr, 0, 32); (brs, 0, 32)] m4)
    as (mf & HFL & HLf & _ & _).
  { intros b lo hi HIn ofs Hr. apply HPermE, P3. cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[]]]]]; injection E as <- <- <-;
      [apply PC0|apply PL0|apply PR0|apply PS0]; exact Hr. }
  { cbn [map fst]. nd6. }
  cbn [map fst] in HLf.
  assert (HNl : forall b, Mem.valid_block m b -> ~ In b [bcm; bl; brr; brs]).
  { intros b Hb HIn. apply (FRh b Hb). cbn [In] in HIn |- *. tauto. }
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le) (m2 := m4)
      (out := Out_return (Some (Vint (Int.repr 1), tint))).
    + eapply btl_entry; eassumption.
    + unfold f_simplicity_bitcoin_build_tapleaf_simplicity. cbn [fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
      { change le with (set_opttemp None Vundef le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _readHash) Ptrofs.zero)
          (vargs := [Vptr bcm Ptrofs.zero; Vptr bl Ptrofs.zero]) (f := Internal f_readHash).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact hio_readHash_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
          eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        - exact hio_readHash_funct.
        - reflexivity.
        - exact HRd. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m3).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2).
        - change le with (set_opttemp None Vundef le) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_bitcoin_make_tapleaf) Ptrofs.zero)
            (vargs := [Vptr brr Ptrofs.zero; Vint (Int.repr 190); Vptr bcm Ptrofs.zero])
            (f := Internal f_simplicity_bitcoin_make_tapleaf).
          + reflexivity.
          + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact btl_make_symbol]|].
            apply deref_loc_reference; reflexivity.
          + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
            eapply eval_Econs; [apply eval_Econst_int|apply btl_cast190|].
            eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
          + exact btl_make_funct.
          + reflexivity.
          + exact HMk.
        - eapply exec_Sassign with (v2 := Vptr brr Ptrofs.zero) (v := Vptr brr Ptrofs.zero).
          + apply eval_Evar_local; reflexivity.
          + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_copy; reflexivity].
          + reflexivity.
          + eapply assign_loc_copy with (bytes := rbytes).
            * reflexivity.
            * intros _. exists 0. reflexivity.
            * intros _. exists 0. reflexivity.
            * left. ne.
            * exact HRB.
            * exact HRS. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m4).
      { change le with (set_opttemp None Vundef le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _writeHash) Ptrofs.zero)
          (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr brs Ptrofs.zero]) (f := Internal f_writeHash).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact hio_writeHash_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
          eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        - exact hio_writeHash_funct.
        - reflexivity.
        - exact HWr. }
      apply exec_Sreturn_some. apply eval_Econst_int.
    + cbn. split; [discriminate|reflexivity].
    + unfold e. rewrite btl_blocks. exact HFL.
  - eapply frame_output_cells_preserved; [|exact HCells].
    intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - eapply write_prefix_at_preserved; [| |exact HPrefix].
    + intros ofs w HL. rewrite K3 by exact Vw. exact HL.
    + intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - destruct HFldE as [HE1 HE2]. split; rewrite HLf by (apply HNl; exact Vd); assumption.
  - intros ch b0 ofs Hv Hd Hw. rewrite HLf by (apply HNl; exact Hv).
    rewrite HLoadsE by assumption. apply K3; exact Hv.
Qed.
