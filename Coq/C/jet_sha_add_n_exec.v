(** Complete execution of the static helper [sha_256_ctx_8_add_n] against the
    byte-list form of ctx8Addn.  The call returns true exactly when the
    option semantics is defined, and then leaves its encoding in the output
    frame.  Conditional on the explicit [memcpy_model]; the dispatch pointer
    and the constant [sha256_max_counter] are explicit state premises. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256 sha.common_lemmas.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_partial.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_bitmachine_rep.
Require Import C.jet_buffer_empty_spec C.jet_buffer_input C.jet_buffer_chunks C.jet_sha256_ctx8_init_spec.
Require Import C.jet_read8s_layout C.jet_read32s_layout C.jet_word32_chunks C.jet_uint32_array_init.
Require Import C.jet_wide C.jet_wide_spec.
Require Import C.jet_read_sha256_counter C.jet_read_sha256_overflow C.jet_sha256_counter_representation.
Require Import C.jet_write_sha256_context_layout.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_spec C.jet_sha_ctx8_model C.jet_sha_be32_exec.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_read_context_layout C.jet_sha_ctx8_bridge.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge ge0.
Set Default Timeout 600.

Definition sha_globals_ok (m : mem) : Prop :=
  sha_dispatch_ok m /\
  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong sha_max_counter).

Lemma absorb_regs_length bs : forall (l : list (Ty.tySem (Word 3))) regs,
  (length l < 64)%nat -> length regs = 8%nat -> length (snd (absorb l regs bs)) = 8%nat.
Proof.
  induction bs as [|x bs IH]; intros l regs HL HR; [exact HR|].
  destruct (Nat.eq_dec (length l) 63) as [E|E].
  - rewrite absorb_cons_full by exact E. apply IH; [cbn; lia|].
    apply sha.common_lemmas.length_hash_block; [exact HR|].
    apply be_words_length. rewrite map_length, app_length. cbn [length]. lia.
  - rewrite absorb_cons_small by lia. apply IH; [rewrite app_length; cbn [length]; lia|exact HR].
Qed.

Lemma sg_in_read8s : In (jets._read8s, jets.f_read8s) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.
Lemma sg_in_write_context :
  In (jets._simplicity_write_sha256_context, jets.f_simplicity_write_sha256_context) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.

Lemma vector_values_pos X k (v : Ty.tySem (Vector X k)) : vector_values X k v <> [].
Proof.
  intro H. pose proof (vector_values_length X k v) as HL. rewrite H in HL. cbn in HL.
  pose proof (Nat.pow_nonzero 2 k ltac:(lia)). lia.
Qed.

Lemma pow2_le_512 k : (k <= 9)%nat -> (1 <= Nat.pow 2 k <= 512)%nat.
Proof.
  intros H. do 10 (destruct k as [|k]; [cbn; lia|]). lia.
Qed.

Theorem eval_sha_add_n (Hmodel : memcpy_model) (k : nat) m bd dbase bsf sbase bi bw edge outedge cursor rc
    (c : Ty.tySem sha256_ctx8_type) (v : Ty.tySem (Vector (Word 3) k)) :
  (k <= 9)%nat ->
  sha_globals_ok m ->
  frame_base_valid sbase ->
  frame_fields_at m bsf sbase bi edge rc ->
  Mem.valid_access m Mint64 bsf (sbase + 8) Writable ->
  0 <= rc -> rc + 830 + 8 * Z.of_nat (Nat.pow 2 k) <= Int64.max_unsigned ->
  frame_input_cells_at m bi edge rc (encode c ++ encode v) ->
  write_frame_at m bd dbase bw outedge cursor 830 ->
  bsf <> bi -> bsf <> bd -> bsf <> bw ->
  bsf <> sha_symbol_block _sha256_max_counter ->
  bsf <> sha_symbol_block _simplicity_sha256_compression ->
  let vs := vector_values (Word 3) k v in
  let spec := ctx8_add_list c vs in
  exists mf,
    Clight2.eval_funcall sha_ge m (Internal f_sha_256_ctx_8_add_n)
      [Vptr bd (Ptrofs.repr dbase); Vptr bsf (Ptrofs.repr sbase);
       Vlong (Int64.repr (Z.of_nat (length vs)))] E0 mf (jet_partial_return spec) /\
    (match spec with
     | Some b => frame_output_cells_at mf bw outedge cursor (encode b) /\
                 write_prefix_at m mf bw outedge cursor /\
                 frame_fields_at mf bd dbase bw outedge (cursor - 830)
     | None => True
     end) /\
    (forall chunk b ofs, Mem.valid_block m b ->
      (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b <> bw \/ ofs + size_chunk chunk <= outedge + 8 * ((cursor - 830) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      (b <> bsf \/ ofs + size_chunk chunk <= sbase + 8 \/ sbase + 16 <= ofs) ->
      Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kd p, Mem.valid_block m b -> Mem.perm m b ofs kd p -> Mem.perm mf b ofs kd p).
Proof.
  intros Hk [Hdisp HMaxC] HSbase [HSE HSO] HSW H0 Hmax Hin Hout Hsi Hsd Hsw HsM HsG vs spec.
  destruct c as [buf [count state]].
  set (G := sha_symbol_block _simplicity_sha256_compression) in *.
  set (MAXC := sha_symbol_block _sha256_max_counter) in *.
  pose proof (pow2_le_512 k Hk) as Hpow.
  assert (Hvs : length vs = Nat.pow 2 k) by (apply vector_values_length).
  set (vn := Int64.repr (Z.of_nat (length vs))).
  (* input split *)
  apply frame_input_cells_at_app in Hin. destruct Hin as [HinC HinV].
  rewrite encode_length in HinV. rewrite sha256_ctx8_type_bits in HinV. change (Z.of_nat 830) with 830 in HinV.
  rewrite encode_vector_values in HinV. fold vs in HinV.
  rewrite frame_input_byte_list in HinV.
  set (lbuf := byte_chunks_values (buffer_byte_chunks 5 buf)).
  pose proof (sha256_buffer63_length_range buf) as Hlbuf. fold lbuf in Hlbuf.
  (* validity of the given blocks *)
  assert (Vsf : Mem.valid_block m bsf) by (eapply load_valid_block; exact HSE).
  assert (VG : Mem.valid_block m G) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m MAXC) by (eapply load_valid_block; exact HMaxC).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 830 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (Vi : Mem.valid_block m bi).
  { destruct vs as [|x0 vs'] eqn:Evs; [exfalso; cbn in Hvs; lia|].
    pose proof (HinV 0%nat x0 eq_refl) as Hw0.
    pose proof (Hw0 O _ (@jet_read16_input_word.frame_input_word_bits_nth 3 x0 O ltac:(vm_compute; lia))) as Hhead.
    destruct Hhead as [_ [_ [w [HL _]]]]. eapply load_valid_block; exact HL. }
  (* locals *)
  destruct (Mem.alloc m 0 32) as [ma1 bm] eqn:A1.
  destruct (Mem.alloc ma1 0 512) as [ma2 bb] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [m0 bx] eqn:A3.
  pose proof (mext_alloc _ _ _ _ _ A1) as X1. pose proof (mext_alloc _ _ _ _ _ A2) as X2.
  pose proof (mext_alloc _ _ _ _ _ A3) as X3.
  assert (X : mext m m0) by (eapply mext_trans; [exact X1|eapply mext_trans; eassumption]).
  destruct X as (XV & XL & XP & XA).
  assert (Fm : forall b0, Mem.valid_block m b0 -> b0 <> bm).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Fb : forall b0, Mem.valid_block m b0 -> b0 <> bb).
  { intros b0 Hv Heq. subst b0. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). apply (proj1 X1). exact Hv. }
  assert (Fx : forall b0, Mem.valid_block m b0 -> b0 <> bx).
  { intros b0 Hv Heq. subst b0. apply (Mem.fresh_block_alloc _ _ _ _ _ A3).
    apply (proj1 X2). apply (proj1 X1). exact Hv. }
  assert (Hmb : bm <> bb).
  { intro Heq. subst bb. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). eapply Mem.valid_new_block; exact A1. }
  assert (Hmx : bm <> bx).
  { intro Heq. subst bx. apply (Mem.fresh_block_alloc _ _ _ _ _ A3). apply (proj1 X2).
    eapply Mem.valid_new_block; exact A1. }
  assert (Hbx : bb <> bx).
  { intro Heq. subst bx. apply (Mem.fresh_block_alloc _ _ _ _ _ A3). eapply Mem.valid_new_block; exact A2. }
  assert (PM0 : Mem.range_perm m0 bm 0 32 Cur Freeable).
  { intros ofs Hr. apply (proj1 (proj2 (proj2 X3))). apply (proj1 (proj2 (proj2 X2))).
    eapply Mem.perm_alloc_2; eauto. }
  assert (PB0 : Mem.range_perm m0 bb 0 512 Cur Freeable).
  { intros ofs Hr. apply (proj1 (proj2 (proj2 X3))). eapply Mem.perm_alloc_2; eauto. }
  assert (PX0 : Mem.range_perm m0 bx 0 88 Cur Freeable).
  { intros ofs Hr. eapply Mem.perm_alloc_2; eauto. }
  set (e := an_env bm bb bx).
  set (le0 := an_temps bd dbase bsf sbase vn).
  (* initialisation *)
  destruct (an_init_exec e bx bm eq_refl eq_refl le0 m0
    ltac:(intros ofs Hr; eapply Mem.perm_implies; [apply PX0; exact Hr|constructor]))
    as (m1 & HInitEx & HOut1 & (L1 & P1 & V1)).
  assert (K1 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m1 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. rewrite L1 by (left; apply Fx; exact Hv). apply XL. exact Hv. }
  assert (Q1 : forall b0 ofs kd p, Mem.perm m b0 ofs kd p -> Mem.perm m1 b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply P1, XP, Hp. }
  assert (W1 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m1 b0).
  { intros b0 Hv. apply V1, XV, Hv. }
  (* the context reader *)
  destruct (Mem.alloc m1 0 8) as [ma bl] eqn:AL.
  pose proof (mext_alloc _ _ _ _ _ AL) as (YV & YL & YP & YA).
  assert (Fl : forall b0, Mem.valid_block m1 b0 -> b0 <> bl).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ AL Hv). }
  assert (Vm1 : Mem.valid_block m1 bm).
  { apply V1. apply (proj1 X3). apply (proj1 X2). eapply Mem.valid_new_block; exact A1. }
  assert (Vb1 : Mem.valid_block m1 bb).
  { apply V1. apply (proj1 X3). eapply Mem.valid_new_block; exact A2. }
  assert (Vx1 : Mem.valid_block m1 bx) by (apply V1; eapply Mem.valid_new_block; exact A3).
  assert (PXa : Mem.range_perm ma bx 0 88 Cur Freeable).
  { intros ofs Hr. apply YP, P1, PX0, Hr. }
  assert (PMa : Mem.range_perm ma bm 0 32 Cur Freeable).
  { intros ofs Hr. apply YP, P1, PM0, Hr. }
  assert (PBa : Mem.range_perm ma bb 0 512 Cur Freeable).
  { intros ofs Hr. apply YP, P1, PB0, Hr. }
  assert (Ka : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch ma b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. rewrite YL by (apply W1; exact Hv). apply K1. exact Hv. }
  assert (R4 : Mem.range_perm ma bx (0 + 16) (0 + 79) Cur Writable).
  { intros ofs Hr. eapply Mem.perm_implies; [apply PXa; lia|constructor]. }
  assert (R5 : Mem.valid_access ma Mint64 bx (0 + 8) Writable).
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies; [apply PXa; lia|constructor]. }
  assert (R6 : Mem.valid_access ma Mint8unsigned bx (0 + 80) Writable).
  { split; [|exists 80; reflexivity]. intros ofs Hr. change (size_chunk Mint8unsigned) with 1 in Hr.
    eapply Mem.perm_implies; [apply PXa; lia|constructor]. }
  assert (R7 : Mem.load Mptr ma bx 0 = Some (Vptr bm (Ptrofs.repr 0))).
  { rewrite YL by exact Vx1. exact HOut1. }
  assert (R11 : Mem.range_perm ma bm 0 (0 + 32) Cur Writable).
  { intros ofs Hr. eapply Mem.perm_implies; [apply PMa; lia|constructor]. }
  assert (R26 : Mem.load Mint64 ma MAXC 0 = Some (Vlong (Int64.repr 2305843009213693952))).
  { rewrite Ka by exact VM. exact HMaxC. }
  assert (R30 : frame_fields_at ma bsf sbase bi edge rc).
  { split; rewrite Ka by exact Vsf; assumption. }
  assert (R31 : Mem.valid_access ma Mint64 bsf (sbase + 8) Writable).
  { destruct HSW as [Pr Al]. split; [|exact Al]. intros ofs Hr. apply YP, Q1, Pr, Hr. }
  assert (R32 : frame_input_cells_at ma bi edge rc (encode buf ++ encode count ++ encode state)).
  { eapply buffer_input_cells_preserved; [|exact HinC]. intros ofs w HL. rewrite Ka by exact Vi. exact HL. }
  destruct (sg_eval_read_sha256_context_allocated_layout m1 ma bsf sbase bi edge rc bx 0 bl bm 0 buf count state
    AL ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) R4 R5 R6 R7
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(exists 0; reflexivity) R11
    (Fx bsf Vsf) Hsi (not_eq_sym (Fx bi Vi))
    (not_eq_sym (Fl bsf (W1 bsf Vsf))) (not_eq_sym (Fl bx Vx1)) (not_eq_sym (Fl bi (W1 bi Vi)))
    (not_eq_sym (Fm bsf Vsf)) (not_eq_sym (Fm bi Vi)) Hmx (not_eq_sym (Fl bm Vm1))
    HsM (not_eq_sym (Fx MAXC VM)) (not_eq_sym (Fl MAXC (W1 MAXC VM))) (not_eq_sym (Fm MAXC VM))
    R26 HSbase H0 ltac:(lia) R30 R31 R32)
    as (m2 & r & HRd & Hr & HOut2 & HArr2 & HSt2 & HCnt2 & HOvf2 & HFld2 & HMax2 & HPerm2 & HMem2 & HVal2).
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 ->
    (b0 <> bsf \/ ofs + size_chunk ch <= sbase + 8 \/ sbase + 16 <= ofs) ->
    Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv Hc.
    rewrite HMem2; [apply Ka; exact Hv|apply Fl, W1, Hv|exact Hc|left; apply Fx; exact Hv|left; apply Fm; exact Hv]. }
  assert (W2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HVal2, YV, W1, Hv. }
  assert (HFree : forall m5,
    (forall b0 ofs kd p, b0 <> bl -> Mem.perm ma b0 ofs kd p -> Mem.perm m5 b0 ofs kd p) ->
    exists mf, Mem.free_list m5 [(bx, 0, 88); (bm, 0, 32); (bb, 0, 512)] = Some mf /\
      (forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mf b0 ofs = Mem.load ch m5 b0 ofs) /\
      (forall b0 ofs kd p, Mem.valid_block m b0 -> Mem.perm m5 b0 ofs kd p -> Mem.perm mf b0 ofs kd p)).
  { intros m5 HP5.
    destruct (free_list_blocks [(bx, 0, 88); (bm, 0, 32); (bb, 0, 512)] m5) as (mf & HFL & HLf & HPf & _).
    - intros b0 lo hi Hin0. cbn in Hin0.
      destruct Hin0 as [Heq|[Heq|[Heq|[]]]]; injection Heq as <- <- <-; intros ofs Hr0; apply HP5.
      + apply Fl; exact Vx1.
      + apply PXa; exact Hr0.
      + apply Fl; exact Vm1.
      + apply PMa; exact Hr0.
      + apply Fl; exact Vb1.
      + apply PBa; exact Hr0.
    - cbn. repeat constructor; cbn; intuition congruence.
    - assert (HNot : forall b0, Mem.valid_block m b0 ->
        ~ In b0 (map (fun x => fst (fst x)) [(bx, 0, 88); (bm, 0, 32); (bb, 0, 512)])).
      { intros b0 Hv. cbn. intros [E|[E|[E|[]]]]; subst b0;
          [exact (Fx _ Hv eq_refl)|exact (Fm _ Hv eq_refl)|exact (Fb _ Hv eq_refl)]. }
      exists mf. split; [exact HFL|]. split.
      + intros ch b0 ofs Hv. apply HLf. apply HNot. exact Hv.
      + intros b0 ofs kd p Hv Hp. apply HPf; [apply HNot; exact Hv|exact Hp]. }
  (* the specification *)
  assert (Hlist : lbuf = buffer_list (Word 3) 5 buf) by (apply buffer_values_list).
  set (total := @toZ (WordToZ 6) count + (Z.of_nat (length lbuf) + Z.of_nat (length vs)) / 64).
  pose proof (ctx8_add_list_closed vs buf count state (vector_values_pos _ _ v)) as HClosed.
  cbv zeta in HClosed. rewrite <- Hlist in HClosed. fold total in HClosed. fold spec in HClosed.
  destruct HClosed as [HCa HCb].
  assert (HDiv : 0 <= (Z.of_nat (length lbuf) + Z.of_nat (length vs)) / 64) by (apply div64_nonneg; lia).
  destruct (sha256_read_overflow r) eqn:Hovr.
  - (* the stored compression count is out of range *)
    apply sha256_read_overflow_true in Hovr.
    assert (HNone : spec = None) by (apply HCb; unfold total, ctx8_limit; rewrite <- Hr; lia).
    destruct (HFree m2 HPerm2) as (mf & HFL & HLf & HPf0).
    exists mf. rewrite HNone. split; [|split; [exact I|split]].
    + eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0)
        (le2 := PTree.set _t'3 (Vint (bit_int (negb true))) le0) (m2 := m2)
        (out := Out_return (Some (Vint (Int.repr 0), tint))).
      * eapply an_entry; eassumption.
      * rewrite an_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply an_assert_exec|].
        apply HInitEx. unfold an_rest.
        eapply exec_Sseq_2; [|discriminate]. unfold an_read.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
        -- eapply an_call_read; [reflexivity|exact HRd].
        -- eapply exec_Sifthenelse with (b := true);
             [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
           apply exec_Sreturn_some. apply eval_Econst_int.
      * cbn. split; [discriminate|reflexivity].
      * unfold e. rewrite an_blocks. exact HFL.
    + intros ch b0 ofs Hv Hd Hw Hs. rewrite HLf by exact Hv. apply K2; assumption.
    + intros b0 ofs kd p Hv Hp. apply HPf0; [exact Hv|].
      apply HPerm2; [apply Fl, W1; exact Hv|]. apply YP, Q1, Hp.
  - (* the reader succeeds *)
    apply sha256_read_overflow_false in Hovr.
    assert (HWords : forall i x, nth_error vs i = Some x ->
      frame_input_word_at m2 bi edge (rc + 830 + 8 * Z.of_nat i) x).
    { intros i x Hi. eapply frame_input_bits_at_preserved; [|exact (HinV i x Hi)].
      intros ofs w HL. rewrite K2; [exact HL|exact Vi|left; intro Heq; apply Hsi; congruence]. }
    assert (PB2 : Mem.range_perm m2 bb 0 (0 + Z.of_nat (length vs)) Cur Writable).
    { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
      apply HPerm2; [apply Fl; exact Vb1|apply PBa; lia]. }
    assert (SW2 : Mem.valid_access m2 Mint64 bsf (sbase + 8) Writable).
    { destruct R31 as [Pr Al]. split; [|exact Al]. intros ofs Hr0.
      apply HPerm2; [apply Fl, W1; exact Vsf|apply Pr; exact Hr0]. }
    destruct (eval_read8s_layout m2 bb 0 bsf sbase bi edge (rc + 830) vs ltac:(lia)
      ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) PB2
      (Fb bsf Vsf) Hsi (not_eq_sym (Fb bi Vi)) HSbase ltac:(lia) ltac:(rewrite Hvs; lia)
      HFld2 SW2 HWords)
      as (m3 & HR8 & HArr3 & HFld3 & HMem3 & HPerm3 & HVal3).
    apply (sha_transport_call _ _ sg_in_read8s) in HR8.
    assert (K3 : forall ch b0 ofs, Mem.valid_block m b0 ->
      (b0 <> bsf \/ ofs + size_chunk ch <= sbase + 8 \/ sbase + 16 <= ofs) ->
      Mem.load ch m3 b0 ofs = Mem.load ch m b0 ofs).
    { intros ch b0 ofs Hv Hc. rewrite HMem3; [apply K2; assumption|exact Hc|left; apply Fb; exact Hv]. }
    set (l := map word8_array_value lbuf).
    set (regs := state_regs state).
    set (bs := map word8_array_value vs).
    set (cc := sha256_read_counter r (Int64.repr (Z.of_nat (length lbuf)))) in *.
    assert (Hll : length l = length lbuf) by (unfold l; apply map_length).
    assert (Hlbs : length bs = length vs) by (unfold bs; apply map_length).
    assert (Hlr : length regs = 8%nat).
    { unfold regs, state_regs. rewrite map_length. apply (word32_chunks_length 3). }
    assert (HccU : Int64.unsigned cc = 64 * Int64.unsigned r + Z.of_nat (length lbuf)).
    { apply add_counter_c; [exact Hovr|exact Hlbuf]. }
    assert (L3x : forall ch ofs, Mem.load ch m3 bx ofs = Mem.load ch m2 bx ofs).
    { intros ch ofs. apply HMem3; [left; apply not_eq_sym, Fx; exact Vsf|left; apply not_eq_sym; exact Hbx]. }
    assert (L3m : forall ch ofs, Mem.load ch m3 bm ofs = Mem.load ch m2 bm ofs).
    { intros ch ofs. apply HMem3; [left; apply not_eq_sym, Fm; exact Vsf|left; exact Hmb]. }
    assert (Q3 : forall b0 ofs kd p, b0 <> bl -> Mem.perm ma b0 ofs kd p -> Mem.perm m3 b0 ofs kd p).
    { intros b0 ofs kd p Hb Hp. apply HPerm3, HPerm2; assumption. }
    pose proof (eval_sha256_uchars Hmodel m3 bx 0 bm 0 bb Ptrofs.zero l regs bs cc false
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
        apply Q3; [apply Fl; exact Vm1|apply PMa; lia]. }
    { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. apply (u8_nth _ _ _ _ HArr3). exact Hi. }
    { unfold sha_dispatch_ok. fold G. rewrite K3; [exact Hdisp|exact VG|left; apply not_eq_sym; exact HsG]. }
    { fold MAXC. rewrite K3; [exact HMaxC|exact VM|left; apply not_eq_sym; exact HsM]. }
    { intros ofs Hr0. eapply Mem.perm_implies with (p1 := Freeable); [|constructor].
      apply Q3; [apply Fl; exact Vx1|apply PXa; lia]. }
    { exists 0. reflexivity. }
    rewrite Hlbs in HUc, HCnt4, HOvf4. fold vn in HUc, HCnt4, HOvf4.
    unfold l, bs in HBlk4, HReg4. rewrite absorb_i_map in HBlk4, HReg4. cbn [fst snd] in HBlk4, HReg4.
    set (lA := fst (absorb lbuf regs vs)) in *. set (rA := snd (absorb lbuf regs vs)) in *.
    destruct (absorb_length vs lbuf regs ltac:(lia)) as [HlenA HltA]. fold lA in HlenA, HltA.
    assert (HrA : length rA = 8%nat) by (apply absorb_regs_length; [lia|exact Hlr]).
    assert (HSpecV : exists (buf' : Ty.tySem (buffer_type (Word 3) 5)) (h' : Ty.tySem (Word 8)),
      byte_chunks_values (buffer_byte_chunks 5 buf') = lA /\ state_regs h' = rA /\
      spec = (if total <? ctx8_limit then Some (buf', (@fromZ (WordToZ 6) total, h')) else None)).
    { destruct (Z.ltb_spec total ctx8_limit) as [HT|HT].
      - destruct (HCa HT) as (buf' & h' & HS1 & HS2 & HS3). exists buf', h'.
        rewrite buffer_values_list. split; [exact HS2|split; [exact HS3|exact HS1]].
      - destruct (buffer_exists (Word 3) 5 lA ltac:(change (Nat.pow 2 6) with 64%nat; exact HltA)) as [buf' Hb'].
        destruct (state_exists rA HrA) as [h' Hh'].
        exists buf', h'. rewrite buffer_values_list. split; [exact Hb'|split; [exact Hh'|apply HCb; exact HT]]. }
    destruct HSpecV as (buf' & h' & Hbuf' & Hh' & HSpec).
    set (ovf' := uc_overflow false cc vn) in *.
    assert (HnR : 0 <= Z.of_nat (length vs) <= 4096) by lia.
    assert (Hovf' : ovf' = negb (total <? ctx8_limit)).
    { unfold ovf', cc, vn, total. rewrite <- Hr.
      apply (add_counter_overflow r (Z.of_nat (length lbuf)) (Z.of_nat (length vs)) Hovr Hlbuf HnR). }
    clearbody ovf'.
    (* the context writer *)
    assert (V3 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m3 b0).
    { intros b0 Hv. apply HVal3, W2, Hv. }
    assert (K4 : forall ch b0 ofs, Mem.valid_block m b0 ->
      (b0 <> bsf \/ ofs + size_chunk ch <= sbase + 8 \/ sbase + 16 <= ofs) ->
      Mem.load ch m4 b0 ofs = Mem.load ch m b0 ofs).
    { intros ch b0 ofs Hv Hc.
      rewrite HMem4; [apply K3; assumption|apply V3; exact Hv|left; apply Fx; exact Hv|left; apply Fm; exact Hv]. }
    assert (Q4 : forall b0 ofs kd p, Mem.perm m b0 ofs kd p -> Mem.perm m4 b0 ofs kd p).
    { intros b0 ofs kd p Hp. assert (Hv : Mem.valid_block m b0) by (eapply Mem.perm_valid_block; exact Hp).
      apply HPerm4; [apply V3; exact Hv|]. apply Q3; [apply Fl, W1; exact Hv|]. apply YP, Q1, Hp. }
    assert (HOut4' : write_frame_at m4 bd dbase bw outedge cursor 830).
    { eapply write_frame_at_preserved; [| |exact Hout].
      - intros ch b0 ofs v0 Hb HL. rewrite K4; [exact HL| |].
        + destruct Hb; subst; assumption.
        + left. destruct Hb; subst; intro Heq; [apply Hsd|apply Hsw]; congruence.
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
    destruct (HFree m5) as (mf & HFL & HLf & HPf0).
    { intros b0 ofs kd p Hb Hp. apply HPermE.
      apply HPerm4; [|apply Q3; assumption].
      eapply Mem.perm_valid_block. apply Q3; eassumption. }
    set (le2 := PTree.set _t'3 (Vint (bit_int (negb false))) le0).
    set (le5 := PTree.set _t'4 (Vint (bit_int (negb ovf'))) le2).
    exists mf. split; [|split; [|split]].
    + eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m0) (le2 := le5) (m2 := m5)
        (out := Out_return (Some (Vint (bit_int (negb ovf')), tbool))).
      * eapply an_entry; eassumption.
      * rewrite an_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [apply an_assert_exec|].
        apply HInitEx. unfold an_rest.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2).
        { unfold an_read. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
          - eapply an_call_read; [reflexivity|exact HRd].
          - eapply exec_Sifthenelse with (b := false);
              [eapply eval_Eunop; [apply eval_Etempvar; apply PTree.gss|reflexivity]|reflexivity|].
            apply exec_Sskip. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m3).
        { eapply an_call_read8s; [reflexivity|reflexivity|exact HR8]. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m4).
        { eapply an_call_uchars; [reflexivity|exact HUc]. }
        unfold an_write. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m5).
        { eapply an_call_write; [reflexivity|exact HWr]. }
        apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
      * cbn. split; [discriminate|]. rewrite HSpec, Hovf'.
        destruct (total <? ctx8_limit); reflexivity.
      * unfold e. rewrite an_blocks. exact HFL.
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
        -- intros ofs w HL. rewrite K4; [exact HL|exact Vw|left; intro Heq; apply Hsw; congruence].
        -- intros ofs w HL. rewrite HLf by exact Vw. exact HL.
      * destruct HFldE as [HE1 HE2]. split; rewrite HLf by exact Vd; assumption.
    + intros ch b0 ofs Hv Hd Hw Hs. rewrite HLf by exact Hv.
      rewrite HLoadsE by assumption. apply K4; assumption.
    + intros b0 ofs kd p Hv Hp. apply HPf0; [exact Hv|]. apply HPermE, Q4, Hp.
Qed.
