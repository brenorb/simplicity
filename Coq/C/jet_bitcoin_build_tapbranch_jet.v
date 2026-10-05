(** The Bitcoin jet build_tapbranch against the literal buildTapbranch
    program.  Conditional on [memcpy_model]; state
    premises: the dispatch pointer, the counter bound and the "TapBranch" tag
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
Require Import C.jet_bitcoin_make_tapleaf_exec C.jet_bitcoin_build_tapleaf_jet.
Require Import C.jet_sha_cmp_be_exec C.jet_sha_cmp_be_model C.jet_bitcoin_build_tapbranch_spec C.jet_bitcoin_make_tapbranch_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.


Definition btb_env (bl ba bb brs brr : block) : env :=
  PTree.set __res (brr, MID) (PTree.set _result (brs, MID)
    (PTree.set _b (bb, MID) (PTree.set _a (ba, MID) (PTree.set _src (bl, FR) empty_env)))).

Definition btb_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_bitcoin_build_tapbranch)))).

Lemma btb_blocks bl ba bb brs brr :
  blocks_of_env sha_ge (btb_env bl ba bb brs brr) =
    [(bl, 0, 16); (ba, 0, 32); (brr, 0, 32); (bb, 0, 32); (brs, 0, 32)].
Proof. vm_compute. reflexivity. Qed.

Lemma btb_entry env m m1 m2 m3 m4 m5 bl ba bb brs brr bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, ba) -> Mem.alloc m2 0 32 = (m3, bb) ->
  Mem.alloc m3 0 32 = (m4, brs) -> Mem.alloc m4 0 32 = (m5, brr) ->
  function_entry2 sha_ge f_simplicity_bitcoin_build_tapbranch
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (btb_env bl ba bb brs brr) (btb_temps env bd dbase bs sbase) m5.
Proof.
  intros HA HB HC HD HE. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HY. contradiction.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact HA|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := ba); [change (Mem.alloc m1 0 32 = (m2, ba)); exact HB|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bb); [change (Mem.alloc m2 0 32 = (m3, bb)); exact HC|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := brs); [change (Mem.alloc m3 0 32 = (m4, brs)); exact HD|].
    eapply alloc_variables_cons with (m1 := m5) (b1 := brr); [change (Mem.alloc m4 0 32 = (m5, brr)); exact HE|].
    constructor.
  - reflexivity.
Qed.

Lemma btb_copy m mc bl ba bb brs brr bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (btb_env bl ba bb brs brr) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
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

Lemma btb_make_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _simplicity_bitcoin_make_tapbranch =
    Some (sha_symbol_block _simplicity_bitcoin_make_tapbranch).
Proof. vm_compute; reflexivity. Qed.
Lemma btb_make_funct :
  Genv.find_funct (Clight.genv_genv sha_ge)
    (Vptr (sha_symbol_block _simplicity_bitcoin_make_tapbranch) Ptrofs.zero) =
    Some (Internal f_simplicity_bitcoin_make_tapbranch).
Proof. vm_compute; reflexivity. Qed.

Local Opaque sha_ge ge0.

(** ** The value *)
Lemma btb_tag_regs : tag_regs_of tapbranch_tag_ints = state_regs tapbranch_tag_word.
Proof.
  unfold tag_regs_of. change (Int64.repr (Z.of_nat (length tapbranch_tag_ints))) with (Int64.repr 9).
  rewrite (absorb_i_fill tapbranch_tag_ints sha256_iv_words (sha_pad (Int64.repr 9)))
    by (first [reflexivity|discriminate]).
  cbn [snd]. change tapbranch_tag_ints with tapbranch_tag_bytes.
  rewrite <- (map_unsigned_inj' _ _ tapbranch_tag_block_bytes).
  rewrite <- iv_word_regs, <- hashBlock_regs, tapbranch_tag_hash_eval. reflexivity.
Qed.

Lemma btb_prefix_regs : tagged_prefix tapbranch_tag_ints = state_regs tapbranch_prefix.
Proof.
  unfold tagged_prefix. rewrite btb_tag_regs.
  rewrite <- tapbranch_prefix_eval, hashBlock_regs, iv_word_regs, block_be_words. reflexivity.
Qed.

Theorem build_tapbranch_regs (a b : Ty.tySem (Word 8)) :
  make_tapbranch_regs (state_regs a) (state_regs b) =
    state_regs (@build_tapbranch_spec Alg.CoreFunSem (a, b)).
Proof.
  unfold make_tapbranch_regs, tapbranch_lt. rewrite cmp_model_lt.
  rewrite build_tapbranch_spec_value, !hashBlock_regs, !block_be_words.
  rewrite absorb_i_fill by (first [reflexivity|discriminate]).
  cbn [snd app]. rewrite btb_prefix_regs, (map_unsigned_inj' _ _ tb_padblock_words).
  unfold tapbranch_order. destruct (@toZ (WordToZ 8) a <? @toZ (WordToZ 8) b).
  - change (word32_chunks 4 (a, b)) with (word32_chunks 3 a ++ word32_chunks 3 b).
    rewrite map_app. reflexivity.
  - change (word32_chunks 4 (b, a)) with (word32_chunks 3 b ++ word32_chunks 3 a).
    rewrite map_app. reflexivity.
Qed.

Definition sha_tapbranch_pre (m : mem) : Prop := sha_globals_ok m /\ sha_tapbranch_tag_ok m.

Theorem bitcoin_build_tapbranch_local_spec : memcpy_model ->
  sha_jet_local_spec_pre sha_tapbranch_pre f_simplicity_bitcoin_build_tapbranch
    (Word 9) (Word 8) (fun ab => @build_tapbranch_spec Alg.CoreFunSem ab).
Proof.
  intros Hmodel env m bd dbase bs sbase bi bw edge outedge cursor rc [a b]
    [[Hdisp HMaxC] HTag] HSbase HSAlign [HSE HSO] H0 Hmax Hin Hout.
  change (rc + 512 <= Int64.max_unsigned) in Hmax.
  change (write_frame_at m bd dbase bw outedge cursor 256) in Hout.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  assert (Vi : Mem.valid_block m bi).
  { eapply frame_input_cells_valid; [|exact Hin]. intro HN.
    apply (f_equal (@length Cell)) in HN. rewrite encode_length in HN. discriminate HN. }
  change (frame_input_cells_at m bi edge rc (@encode (Word 8) a ++ @encode (Word 8) b)) in Hin.
  apply frame_input_cells_at_app in Hin. destruct Hin as [Hina Hinb].
  rewrite encode_length in Hinb. change (Z.of_nat (bitSize (Word 8))) with 256 in Hinb.
  set (hsA := word32_chunks 3 a). set (hsB := word32_chunks 3 b).
  assert (HlA : length hsA = 8%nat) by (apply (word32_chunks_length 3)).
  assert (HlB : length hsB = 8%nat) by (apply (word32_chunks_length 3)).
  assert (HwA : forall j v, nth_error hsA j = Some v -> frame_input_word_at m bi edge (rc + 32 * Z.of_nat j) v)
    by (apply (frame_input_word32_chunks m bi edge rc 3 a); exact Hina).
  assert (HwB : forall j v, nth_error hsB j = Some v ->
    frame_input_word_at m bi edge (rc + 256 + 32 * Z.of_nat j) v)
    by (apply (frame_input_word32_chunks m bi edge (rc + 256) 3 b); exact Hinb).
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 256 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  (* locals *)
  destruct (Mem.alloc m 0 16) as [ma1 bl] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 ba] eqn:A2.
  destruct (Mem.alloc ma2 0 32) as [ma3 bb] eqn:A3.
  destruct (Mem.alloc ma3 0 32) as [ma4 brs] eqn:A4.
  destruct (Mem.alloc ma4 0 32) as [m0 brr] eqn:A5.
  assert (HAL : alloc_list m [16; 32; 32; 32; 32] = (m0, [bl; ba; bb; brs; brr])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4, A5. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PL0 VL0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PA0 VA0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PB0 VB0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PS0 VS0] FA4]; subst.
  inversion FA4 as [|? ? ? ? [PR0 VR0] FA5]; subst. clear FA FA1 FA2 FA3 FA4 FA5 HAL.
  apply NoDup_cons_iff in ND. destruct ND as [N1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N2 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N3 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N4 _].
  pose proof (FRh bi Vi) as Nbi. pose proof (FRh bs Vs) as Nbs.
  pose proof (FRh bd Vd) as Nbd. pose proof (FRh bw Vw) as Nbw.
  set (e := btb_env bl ba bb brs brr).
  set (le := btb_temps env bd dbase bs sbase).
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
  { apply (btb_copy m0 mc bl ba bb brs brr bs sbase bytes le);
      [exact HSbase|exact HSAlign|ne|reflexivity|exact HB0|exact SC]. }
  (* readHash a *)
  destruct (eval_sha_readHash mc ba 0 bl 0 bi edge rc hsA HlA ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(exists 0; reflexivity))
    as (m1 & HRd1 & HArr1 & HFld1 & HMem1 & HPerm1 & HVal1).
  { intros ofs Hr. eapply Mem.perm_implies; [apply Pc, PA0; lia|constructor]. }
  { ne. }
  { ne. }
  { ne. }
  { exact HLocalBase. }
  { exact H0. }
  { lia. }
  { split; [exact HLE|exact HLO]. }
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies; [apply Pc, PL0; lia|constructor]. }
  { intros i x Hi. eapply frame_input_bits_at_preserved; [|exact (HwA i x Hi)].
    intros ofs w HL. rewrite Kc by exact Vi. exact HL. }
  fold (state_regs a) in HArr1.
  assert (K1 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m1 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite HMem1; [apply Kc; exact Hv|left; ne|left; ne]. }
  assert (P1 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m1 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm1, Pc, Hp. }
  (* readHash b *)
  destruct (eval_sha_readHash m1 bb 0 bl 0 bi edge (rc + 256) hsB HlB ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(exists 0; reflexivity))
    as (m2 & HRd2 & HArr2 & HFld2 & HMem2 & HPerm2 & HVal2).
  { intros ofs Hr. eapply Mem.perm_implies; [apply P1, PB0; lia|constructor]. }
  { ne. }
  { ne. }
  { ne. }
  { exact HLocalBase. }
  { lia. }
  { lia. }
  { exact HFld1. }
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies; [apply P1, PL0; lia|constructor]. }
  { intros i x Hi. eapply frame_input_bits_at_preserved; [|exact (HwB i x Hi)].
    intros ofs w HL. rewrite K1 by exact Vi. exact HL. }
  fold (state_regs b) in HArr2.
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite HMem2; [apply K1; exact Hv|left; ne|left; ne]. }
  assert (P2 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m2 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm2, P1, Hp. }
  assert (V2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HVal2, HVal1, Vc, XV, Hv. }
  assert (HArr1' : uint32_array_at m2 ba 0 (state_regs a)).
  { intros i x Hi. rewrite HMem2; [apply HArr1; exact Hi|left; ne|left; ne]. }
  assert (HSA : length (state_regs a) = 8%nat).
  { unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
  assert (HSB : length (state_regs b) = 8%nat).
  { unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
  (* make_tapbranch *)
  assert (HZ32 : Ptrofs.unsigned Ptrofs.zero + 32 <= Ptrofs.max_unsigned).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  destruct (eval_make_tapbranch Hmodel m2 brr 0 ba Ptrofs.zero bb Ptrofs.zero (state_regs a) (state_regs b)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(exists 0; reflexivity))
    as (m3 & HMk & HReg3 & HMem3 & HPerm3 & HVal3).
  { intros ofs Hr. eapply Mem.perm_implies; [apply P2, PR0; lia|constructor]. }
  { exact HSA. }
  { exact HZ32. }
  { intros j Hj. change (Ptrofs.unsigned Ptrofs.zero) with 0.
    apply (u32_nth m2 ba 0 (state_regs a) HArr1'). rewrite HSA. exact Hj. }
  { exact HSB. }
  { exact HZ32. }
  { intros j Hj. change (Ptrofs.unsigned Ptrofs.zero) with 0.
    apply (u32_nth m2 bb 0 (state_regs b) HArr2). rewrite HSB. exact Hj. }
  { unfold sha_dispatch_ok. rewrite K2; [exact Hdisp|eapply load_valid_block; exact Hdisp]. }
  { rewrite K2; [exact HMaxC|eapply load_valid_block; exact HMaxC]. }
  { intros i Hi. rewrite K2; [apply HTag; exact Hi|eapply load_valid_block; exact (HTag 0%nat ltac:(lia))]. }
  rewrite build_tapbranch_regs in HReg3.
  set (res := @build_tapbranch_spec Alg.CoreFunSem (a, b)) in *.
  assert (HRL : length (state_regs res) = 8%nat).
  { unfold state_regs. rewrite map_length. apply (word32_chunks_length 3). }
  assert (K3 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m3 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite HMem3; [apply K2; exact Hv|apply V2; exact Hv|left; ne]. }
  assert (P3 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m3 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HPerm3, P2, Hp. }
  (* result = __res *)
  assert (PRd : Mem.range_perm m3 brr 0 32 Cur Readable).
  { intros ofs Hr. eapply Mem.perm_implies; [apply P3, PR0, Hr|constructor]. }
  destruct (Mem.range_perm_loadbytes m3 brr 0 32 PRd) as (rbytes & HRB).
  pose proof (Mem.loadbytes_length _ _ _ _ _ HRB) as HRBL.
  assert (PWr : Mem.range_perm m3 brs 0 (0 + Z.of_nat (length rbytes)) Cur Writable).
  { rewrite HRBL. change (0 + Z.of_nat (Z.to_nat 32)) with 32. intros ofs Hr.
    eapply Mem.perm_implies; [apply P3, PS0, Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m3 brs 0 rbytes PWr) as (m4 & HRS).
  assert (HRB4 : Mem.loadbytes m4 brs 0 32 = Some rbytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HRS) as H. rewrite HRBL in H. exact H. }
  assert (HArr4 : uint32_array_at m4 brs 0 (state_regs res)).
  { apply u32_of_nth. intros j Hj. rewrite HRL in Hj.
    apply (equal_loadbytes_field Mint32 m3 m4 brr brs 0 0 32 (4 * Z.of_nat j) rbytes).
    - lia.
    - change (size_chunk Mint32) with 4. lia.
    - exact HRB.
    - exact HRB4.
    - change (align_chunk Mint32) with 4. exists (Z.of_nat j). lia.
    - apply HReg3. exact Hj. }
  assert (K4 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m4 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite (Mem.load_storebytes_other _ _ _ _ _ HRS) by (left; ne). apply K3. exact Hv. }
  assert (P4 : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm m4 b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; [exact HRS|apply P3, Hp]. }
  (* writeHash *)
  assert (HOut4 : write_frame_at m4 bd dbase bw outedge cursor 256).
  { eapply write_frame_at_preserved; [| |exact Hout].
    - intros ch b0 ofs v0 Hb HL. rewrite K4; [exact HL|destruct Hb; subst; assumption].
    - intros b0 ofs kd p Hp. apply P4, XP, Hp. }
  destruct (eval_sha_writeHash m4 brs 0 bd dbase bw outedge cursor (state_regs res) HRL ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(ne) ltac:(ne) HArr4 HOut4)
    as (m5 & HWr & HCells & HPrefix & HFldE & HLoadsE & HPermE & HValE).
  rewrite state_regs_cells in HCells.
  (* freeing the locals *)
  destruct (free_list_blocks [(bl, 0, 16); (ba, 0, 32); (brr, 0, 32); (bb, 0, 32); (brs, 0, 32)] m5)
    as (mf & HFL & HLf & _ & _).
  { intros b0 lo hi HIn ofs Hr. apply HPermE, P4. cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[E|[]]]]]]; injection E as <- <- <-;
      [apply PL0|apply PA0|apply PR0|apply PB0|apply PS0]; exact Hr. }
  { cbn [map fst]. nd6. }
  cbn [map fst] in HLf.
  assert (HNl : forall b0, Mem.valid_block m b0 -> ~ In b0 [bl; ba; brr; bb; brs]).
  { intros b0 Hb HIn. apply (FRh b0 Hb). cbn [In] in HIn |- *. tauto. }
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le) (m2 := m5)
      (out := Out_return (Some (Vint (Int.repr 1), tint))).
    + eapply btb_entry; eassumption.
    + unfold f_simplicity_bitcoin_build_tapbranch. cbn [fn_body].
      assert (HReadCall : forall ma mb id bh,
        e!id = Some (bh, MID) ->
        Clight2.eval_funcall sha_ge ma (Internal f_readHash)
          [Vptr bh (Ptrofs.repr 0); Vptr bl (Ptrofs.repr 0)] E0 mb Vundef ->
        Clight2.exec_stmt sha_ge e le ma
          (Scall None (Evar _readHash (Tfunction (Tcons (tptr MID) (Tcons FRP Tnil)) tvoid cc_default))
            [Eaddrof (Evar id MID) (tptr MID); Eaddrof (Evar _src FR) FRP]) E0 le mb Out_normal).
      { intros ma mb id bh HI HC. change le with (set_opttemp None Vundef le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _readHash) Ptrofs.zero)
          (vargs := [Vptr bh Ptrofs.zero; Vptr bl Ptrofs.zero]) (f := Internal f_readHash).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact hio_readHash_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HI|reflexivity|].
          eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        - exact hio_readHash_funct.
        - reflexivity.
        - exact HC. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
      { exact (HReadCall mc m1 _a ba eq_refl HRd1). }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m2).
      { exact (HReadCall m1 m2 _b bb eq_refl HRd2). }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m4).
      { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m3).
        - change le with (set_opttemp None Vundef le) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _simplicity_bitcoin_make_tapbranch) Ptrofs.zero)
            (vargs := [Vptr brr Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero])
            (f := Internal f_simplicity_bitcoin_make_tapbranch).
          + reflexivity.
          + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact btb_make_symbol]|].
            apply deref_loc_reference; reflexivity.
          + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
            eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
            eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
          + exact btb_make_funct.
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
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m5).
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
    + unfold e. rewrite btb_blocks. exact HFL.
  - eapply frame_output_cells_preserved; [|exact HCells].
    intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - eapply write_prefix_at_preserved; [| |exact HPrefix].
    + intros ofs w HL. rewrite K4 by exact Vw. exact HL.
    + intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - destruct HFldE as [HE1 HE2]. split; rewrite HLf by (apply HNl; exact Vd); assumption.
  - intros ch b0 ofs Hv Hd Hw. rewrite HLf by (apply HNl; exact Hv).
    rewrite HLoadsE by assumption. apply K4; exact Hv.
Qed.
