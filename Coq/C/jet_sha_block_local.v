(** Actual sha_256_block jet (in the SHA translation unit) against the
    canonical [hashBlock] program.
    C: [read32s(h, 8, &src); read32s(block, 16, &src);
        simplicity_sha256_compression(h, block); write32s(dst, h, 8); return true;]
    The call goes through the mutable dispatch pointer
    [simplicity_sha256_compression]; the contract carries the explicit state
    premise [sha_dispatch_ok] that it still holds its initializer, the
    portable compression function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events Globalenvs.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg Simplicity.SHA256.
Require Import C.jet_exec C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_spec C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout.
Require Import C.jet_encoding C.jet_bitmachine_rep C.jet_constant_layout C.jet_read16_input_word.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_word32_chunks C.jet_uint32_array_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_exec.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque sha_ge ge0.
Set Default Timeout 300.

Definition sha_dispatch_ok (m : mem) : Prop :=
  Mem.load Mptr m (sha_symbol_block _simplicity_sha256_compression) 0 =
    Some (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero).

(** [jet_local_spec] in the SHA translation unit, under the dispatch premise. *)
Definition sha_jet_local_spec (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    sha_dispatch_ok m ->
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

Lemma hash256_reg_chunks (h : Ty.tySem Word256) :
  hash256_reg (to_hash256 h) = map word32_array_value (word32_chunks 3 h).
Proof. destruct h as [[[h0 h1] [h2 h3]] [[h4 h5] [h6 h7]]]. reflexivity. Qed.

Lemma repr_Block_chunks (b : Ty.tySem Word512) :
  SHA256.repr_Block b = map word32_array_value (word32_chunks 4 b).
Proof.
  destruct b as [b0 b1]. unfold SHA256.repr_Block. rewrite !hash256_reg_chunks.
  change (word32_chunks 4 (b0, b1)) with (word32_chunks 3 b0 ++ word32_chunks 3 b1).
  rewrite map_app. reflexivity.
Qed.

Lemma encode_word_pair' n (hi lo : Ty.tySem (Word n)) :
  @encode (Word (S n)) (hi, lo) = @encode (Word n) hi ++ @encode (Word n) lo.
Proof. reflexivity. Qed.

Lemma uint32_cells_from_hash256 (h : hash256) :
  uint32_word_cells (hash256_reg h) = encode (from_hash256 h).
Proof.
  destruct h as [regs Hlen].
  destruct regs as [|a0 [|a1 [|a2 [|a3 [|a4 [|a5 [|a6 [|a7 [|a8 regs]]]]]]]]];
    cbn in Hlen; try discriminate.
  unfold uint32_word_cells, from_hash256; cbn [hash256_reg map concat].
  rewrite !encode_word_pair'. rewrite ?app_nil_r, ?app_assoc. reflexivity.
Qed.

Definition sha_256_block_spec (hb : Ty.tySem (Ty.Prod Word256 Word512)) : Ty.tySem Word256 :=
  @SHA256.hashBlock Alg.CoreFunSem hb.

Lemma sha_256_block_spec_cells (h : Ty.tySem Word256) (b : Ty.tySem Word512) :
  uint32_word_cells (SHA256.hash_block (map word32_array_value (word32_chunks 3 h))
    (map word32_array_value (word32_chunks 4 b))) = encode (sha_256_block_spec (h, b)).
Proof.
  rewrite <- hash256_reg_chunks, <- repr_Block_chunks.
  pose proof (SHA256.hashBlock_correct h b) as Hc.
  change (hash256_reg (to_hash256 (sha_256_block_spec (h, b))) =
    SHA256.hash_block (hash256_reg (to_hash256 h)) (SHA256.repr_Block b)) in Hc.
  rewrite <- Hc. rewrite uint32_cells_from_hash256. rewrite from_to_hash256. reflexivity.
Qed.

Lemma uint32_array_nth m b xs i :
  uint32_array_at m b 0 xs -> (i < length xs)%nat ->
  Mem.load Mint32 m b (0 + 4 * Z.of_nat i) = Some (Vint (nth i xs Int.zero)).
Proof. intros HA Hi. apply HA. apply nth_error_nth'. exact Hi. Qed.

Theorem sha_256_block_local_spec :
  sha_jet_local_spec f_simplicity_sha_256_block (Ty.Prod Word256 Word512) Word256 sha_256_block_spec.
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [h b]
    Hdisp HSbase HSAlign HSource H0 Hmax Hin Hout.
  change (rc + 768 <= Int64.max_unsigned) in Hmax.
  change (write_frame_at m bd dbase bw outedge cursor 256) in Hout.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  change (frame_input_cells_at m bi edge rc (@encode Word256 h ++ @encode Word512 b)) in Hin.
  apply frame_input_cells_at_app in Hin. destruct Hin as [Hinh Hinb].
  rewrite encode_length in Hinb. change (Z.of_nat (bitSize Word256)) with 256 in Hinb.
  set (hs := word32_chunks 3 h) in *. set (bs16 := word32_chunks 4 b) in *.
  assert (Hlh : length hs = 8%nat) by (apply (word32_chunks_length 3)).
  assert (Hlb : length bs16 = 16%nat) by (apply (word32_chunks_length 4)).
  assert (Hwh : forall j v, nth_error hs j = Some v -> frame_input_word_at m bi edge (rc + 32 * Z.of_nat j) v)
    by (apply (frame_input_word32_chunks m bi edge rc 3 h); exact Hinh).
  assert (Hwb : forall j v, nth_error bs16 j = Some v ->
    frame_input_word_at m bi edge (rc + 256 + 32 * Z.of_nat j) v)
    by (apply (frame_input_word32_chunks m bi edge (rc + 256) 4 b); exact Hinb).
  assert (HSourceLoad : exists w, Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong w)).
  { destruct hs as [|v0 hs'] eqn:Ehs; [discriminate Hlh|].
    pose proof (Hwh 0%nat v0 eq_refl) as Hw0.
    pose proof (Hw0 O _ (@frame_input_word_bits_nth 5 v0 O ltac:(vm_compute; lia))) as Hhead.
    replace (rc + 32 * Z.of_nat 0 + Z.of_nat 0) with rc in Hhead by lia.
    destruct Hhead as [_ [_ [w [HL _]]]]. exists w. exact HL. }
  destruct HSourceLoad as [sourceword HSourceLoad].
  destruct HSource as [HSE HSO].
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hbyteslen.
  pose proof Hout as [HDbase [[HDE HDO] [HE [HC [HM [PD HW]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor 256 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:A1.
  destruct (Mem.alloc ma 0 32) as [mb bh] eqn:A2.
  destruct (Mem.alloc mb 0 64) as [mc bb] eqn:A3.
  pose proof (mext_alloc _ _ _ _ _ A1) as X1. pose proof (mext_alloc _ _ _ _ _ A2) as X2.
  pose proof (mext_alloc _ _ _ _ _ A3) as X3.
  assert (X : mext m mc) by (eapply mext_trans; [exact X1|eapply mext_trans; eassumption]).
  destruct X as (XV & XL & XP & XA).
  assert (Fl : forall b0, Mem.valid_block m b0 -> b0 <> bl).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Fh : forall b0, Mem.valid_block m b0 -> b0 <> bh).
  { intros b0 Hv Heq. subst b0. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). apply (proj1 X1). exact Hv. }
  assert (Fb : forall b0, Mem.valid_block m b0 -> b0 <> bb).
  { intros b0 Hv Heq. subst b0. apply (Mem.fresh_block_alloc _ _ _ _ _ A3).
    apply (proj1 X2). apply (proj1 X1). exact Hv. }
  assert (Hlh' : bl <> bh).
  { intro Heq. subst bh. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). eapply Mem.valid_new_block; exact A1. }
  assert (Hlb' : bl <> bb).
  { intro Heq. subst bb. apply (Mem.fresh_block_alloc _ _ _ _ _ A3). apply (proj1 X2).
    eapply Mem.valid_new_block; exact A1. }
  assert (Hhb : bh <> bb).
  { intro Heq. subst bb. apply (Mem.fresh_block_alloc _ _ _ _ _ A3). eapply Mem.valid_new_block; exact A2. }
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (Vi : Mem.valid_block m bi) by (eapply load_valid_block; exact HSourceLoad).
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (Vg : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression))
    by (eapply load_valid_block; exact Hdisp).
  assert (HBc : Mem.loadbytes mc bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [|exact A3|apply (proj1 X2); apply (proj1 X1); exact Vs].
    erewrite Mem.loadbytes_alloc_unchanged; [|exact A2|apply (proj1 X1); exact Vs].
    erewrite Mem.loadbytes_alloc_unchanged; [exact HB|exact A1|exact Vs]. }
  assert (PL : Mem.range_perm mc bl 0 16 Cur Freeable).
  { intros ofs Hr. apply (proj1 (proj2 (proj2 X3))). apply (proj1 (proj2 (proj2 X2))).
    eapply Mem.perm_alloc_2; eauto. }
  assert (PH : Mem.range_perm mc bh 0 32 Cur Freeable).
  { intros ofs Hr. apply (proj1 (proj2 (proj2 X3))). eapply Mem.perm_alloc_2; eauto. }
  assert (PB : Mem.range_perm mc bb 0 64 Cur Freeable).
  { intros ofs Hr. eapply Mem.perm_alloc_2; eauto. }
  assert (PLW : Mem.range_perm mc bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm mc bl 0 16 Cur Writable).
    intros ofs Hr. eapply Mem.perm_implies; [apply PL; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes mc bl 0 bytes PLW) as [mcp SC].
  assert (HSEc : Mem.load Mptr mc bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSOc : Mem.load Mint64 mc bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_copy_fields_at mc mcp bs sbase bl bytes _ _ HBc SC HSEc HSOc) as [HLE HLO].
  (* loads of original blocks up to the copy *)
  assert (K0 : forall chunk b0 ofs, Mem.valid_block m b0 -> Mem.load chunk mcp b0 ofs = Mem.load chunk m b0 ofs).
  { intros chunk b0 ofs Hv. erewrite Mem.load_storebytes_other; [|exact SC|left; apply Fl; exact Hv].
    apply XL. exact Hv. }
  assert (P0 : forall b0 ofs k p, Mem.perm mc b0 ofs k p -> Mem.perm mcp b0 ofs k p).
  { intros b0 ofs k p Hp. eapply Mem.perm_storebytes_1; eauto. }
  assert (PLC : Mem.valid_access mcp Mint64 bl 8 Writable).
  { split; [|exists 1; reflexivity]. intros ofs Hr. apply P0.
    eapply Mem.perm_implies with (p1 := Freeable); [apply PL; cbn in Hr; lia|constructor]. }
  (* first read: the state words *)
  assert (Hwh0 : forall j v, nth_error hs j = Some v -> frame_input_word_at mcp bi edge (rc + 32 * Z.of_nat j) v).
  { intros j v Hj. eapply frame_input_bits_at_preserved; [|exact (Hwh j v Hj)].
    intros ofs w HL. rewrite K0 by exact Vi. exact HL. }
  destruct (eval_read32s_layout mcp bh 0 bl 0 bi edge rc hs
    ltac:(lia) ltac:(rewrite Hlh; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(exists 0; reflexivity)
    ltac:(rewrite Hlh; intros ofs Hr; apply P0; eapply Mem.perm_implies; [apply PH; lia|constructor])
    Hlh' ltac:(intro Heq; apply (Fl bi Vi); congruence) ltac:(intro Heq; apply (Fh bi Vi); congruence)
    HLocalBase H0 ltac:(rewrite Hlh; lia) (conj HLE HLO) PLC Hwh0)
    as (mr1 & Hread1 & HArr1 & HFields1 & HMem1 & HPerm1 & HValid1).
  rewrite Hlh in Hread1, HFields1, HMem1. change (0 + 4 * Z.of_nat 8) with 32 in HMem1.
  change (rc + 32 * Z.of_nat 8) with (rc + 256) in HFields1.
  assert (K1 : forall chunk b0 ofs, Mem.valid_block m b0 -> Mem.load chunk mr1 b0 ofs = Mem.load chunk m b0 ofs).
  { intros chunk b0 ofs Hv. rewrite HMem1 by (left; first [apply Fl|apply Fh]; exact Hv). apply K0. exact Hv. }
  (* second read: the block words *)
  assert (Hwb1 : forall j v, nth_error bs16 j = Some v ->
    frame_input_word_at mr1 bi edge (rc + 256 + 32 * Z.of_nat j) v).
  { intros j v Hj. eapply frame_input_bits_at_preserved; [|exact (Hwb j v Hj)].
    intros ofs w HL. rewrite K1 by exact Vi. exact HL. }
  assert (PLC1 : Mem.valid_access mr1 Mint64 bl 8 Writable).
  { destruct PLC as [Pr Pa]. split; [intros ofs Hr; apply HPerm1; apply Pr; exact Hr|exact Pa]. }
  destruct (eval_read32s_layout mr1 bb 0 bl 0 bi edge (rc + 256) bs16
    ltac:(lia) ltac:(rewrite Hlb; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(exists 0; reflexivity)
    ltac:(rewrite Hlb; intros ofs Hr; apply HPerm1; apply P0; eapply Mem.perm_implies; [apply PB; lia|constructor])
    Hlb' ltac:(intro Heq; apply (Fl bi Vi); congruence) ltac:(intro Heq; apply (Fb bi Vi); congruence)
    HLocalBase ltac:(lia) ltac:(rewrite Hlb; lia) HFields1 PLC1 Hwb1)
    as (mr2 & Hread2 & HArr2 & HFields2 & HMem2 & HPerm2 & HValid2).
  rewrite Hlb in Hread2, HMem2. change (0 + 4 * Z.of_nat 16) with 64 in HMem2.
  assert (K2 : forall chunk b0 ofs, Mem.valid_block m b0 -> Mem.load chunk mr2 b0 ofs = Mem.load chunk m b0 ofs).
  { intros chunk b0 ofs Hv. rewrite HMem2 by (left; first [apply Fl|apply Fb]; exact Hv). apply K1. exact Hv. }
  assert (HArr1' : uint32_array_at mr2 bh 0 (map word32_array_value hs)).
  { intros i x Hi. rewrite HMem2 by (left; congruence). exact (HArr1 i x Hi). }
  set (regs := map word32_array_value hs) in *. set (blk := map word32_array_value bs16) in *.
  assert (Hlr : length regs = 8%nat) by (unfold regs; rewrite map_length; exact Hlh).
  assert (Hlk : length blk = 16%nat) by (unfold blk; rewrite map_length; exact Hlb).
  assert (PH2 : forall ofs, 0 <= ofs < 32 -> Mem.perm mr2 bh ofs Cur Freeable).
  { intros ofs Hr. apply HPerm2, HPerm1, P0. apply PH. exact Hr. }
  (* the compression call *)
  destruct (eval_sha_compression mr2 bh Ptrofs.zero bb Ptrofs.zero regs blk Hlr Hlk
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(left; exact Hhb))
    as (m4 & Hcomp & HS4 & HL4 & HP4 & HV4).
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. split.
    - apply uint32_array_nth; [exact HArr1'|lia].
    - split; [|change (align_chunk Mint32) with 4; exists (Z.of_nat i); lia].
      intros ofs Hr. change (size_chunk Mint32) with 4 in Hr.
      eapply Mem.perm_implies; [apply PH2; lia|constructor]. }
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0.
    apply uint32_array_nth; [exact HArr2|lia]. }
  change (Ptrofs.unsigned Ptrofs.zero) with 0 in HS4, HL4.
  set (out := SHA256.hash_block regs blk) in *.
  assert (Hlo : length out = 8%nat).
  { unfold out, regs, blk, hs, bs16. rewrite <- hash256_reg_chunks, <- repr_Block_chunks.
    pose proof (SHA256.hashBlock_correct h b) as Hc.
    change (hash256_reg (to_hash256 (@SHA256.hashBlock Alg.CoreFunSem (h, b))) =
      SHA256.hash_block (hash256_reg (to_hash256 h)) (SHA256.repr_Block b)) in Hc.
    rewrite <- Hc. apply hash256_len. }
  assert (Vr2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block mr2 b0).
  { intros b0 Hv. apply HValid2, HValid1. eapply Mem.storebytes_valid_block_1; [exact SC|]. apply XV. exact Hv. }
  assert (K4 : forall chunk b0 ofs, Mem.valid_block m b0 -> Mem.load chunk m4 b0 ofs = Mem.load chunk m b0 ofs).
  { intros chunk b0 ofs Hv. rewrite HL4; [apply K2; exact Hv|apply Vr2; exact Hv|left; apply Fh; exact Hv]. }
  assert (P4 : forall b0 ofs k p, Mem.perm m b0 ofs k p -> Mem.perm m4 b0 ofs k p).
  { intros b0 ofs k p Hp. apply HP4.
    - apply Vr2. eapply Mem.perm_valid_block; exact Hp.
    - apply HPerm2, HPerm1, P0, XP. exact Hp. }
  assert (HArr4 : uint32_array_at m4 bh 0 out).
  { intros i x Hi. assert (Hi8 : (i < 8)%nat) by (rewrite <- Hlo; apply nth_error_Some; rewrite Hi; discriminate).
    rewrite (HS4 i Hi8). f_equal. f_equal. apply nth_error_nth. exact Hi. }
  assert (HOut4 : write_frame_at m4 bd dbase bw outedge cursor (32 * Z.of_nat (length out))).
  { rewrite Hlo. change (32 * Z.of_nat 8) with 256.
    eapply write_frame_at_preserved; [| |exact Hout].
    - intros chunk b0 ofs v Hb HL. rewrite K4; [exact HL|destruct Hb; subst; assumption].
    - exact P4. }
  destruct (eval_write32s_layout m4 bh 0 bd dbase bw outedge cursor out
    ltac:(lia) ltac:(rewrite Hlo; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(intro Heq; apply (Fh bd Vd); congruence) ltac:(intro Heq; apply (Fh bw Vw); congruence)
    HArr4 HOut4)
    as (me & Hwrite & HCells & HPrefix & HFieldsE & HLoadsE & HPermE & HValidE).
  rewrite Hlo in Hwrite, HFieldsE, HLoadsE. change (32 * Z.of_nat 8) with 256 in HFieldsE, HLoadsE.
  (* deallocation *)
  assert (PF : forall b0 lo hi, In (b0, lo, hi) [(bl, 0, 16); (bh, 0, 32); (bb, 0, 64)] ->
    Mem.range_perm me b0 lo hi Cur Freeable).
  { assert (Pchain : forall b0 ofs, Mem.perm mc b0 ofs Cur Freeable -> Mem.perm me b0 ofs Cur Freeable).
    { intros b0 ofs Hp. apply HPermE. apply HP4.
      - apply HValid2, HValid1. eapply Mem.storebytes_valid_block_1; [exact SC|].
        eapply Mem.perm_valid_block; exact Hp.
      - apply HPerm2, HPerm1, P0. exact Hp. }
    intros b0 lo hi Hin ofs Hr. cbn in Hin.
    destruct Hin as [Heq|[Heq|[Heq|[]]]]; injection Heq as <- <- <-; apply Pchain;
      [apply PL|apply PH|apply PB]; exact Hr. }
  destruct (free_list_blocks [(bl, 0, 16); (bh, 0, 32); (bb, 0, 64)] me PF) as (mf & HFL & HLf & HPf & HVf).
  { cbn. repeat constructor; cbn; intuition congruence. }
  cbn [map fst] in HLf.
  assert (Kf : forall chunk b0 ofs, Mem.valid_block m b0 -> Mem.load chunk mf b0 ofs = Mem.load chunk me b0 ofs).
  { intros chunk b0 ofs Hv. apply HLf. cbn. intros [E|[E|[E|[]]]]; subst b0;
      [exact (Fl _ Hv eq_refl)|exact (Fh _ Hv eq_refl)|exact (Fb _ Hv eq_refl)]. }
  assert (Hdisp2 : Mem.load Mptr mr2 (sha_symbol_block _simplicity_sha256_compression) 0 =
    Some (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero))
    by (rewrite K2 by exact Vg; exact Hdisp).
  exists mf. split.
  - eapply eval_sha_block_composes with (mcp := mcp) (mr1 := mr1) (mr2 := mr2) (m4 := m4) (me := me);
      try eassumption.
    + intro Heq. apply (Fl bs Vs). congruence.
    + eapply sha_transport_call; [|exact Hread1]. unfold sha_core_helpers. simpl. tauto.
    + eapply sha_transport_call; [|exact Hread2]. unfold sha_core_helpers. simpl. tauto.
    + eapply sha_transport_call; [|exact Hwrite]. unfold sha_core_helpers. simpl. tauto.
  - split.
    + rewrite <- sha_256_block_spec_cells. fold hs bs16 regs blk out.
      eapply frame_output_cells_preserved; [|exact HCells].
      intros ofs w HL. rewrite Kf by exact Vw. exact HL.
    + split.
      * eapply write_prefix_at_preserved; [| |exact HPrefix].
        -- intros ofs w HL. rewrite K4 by exact Vw. exact HL.
        -- intros ofs w HL. rewrite Kf by exact Vw. exact HL.
      * split.
        -- destruct HFieldsE as [Hedge Hcursor]. change (Z.of_nat (bitSize Word256)) with 256.
           split; rewrite Kf by exact Vd; assumption.
        -- intros chunk b0 ofs HV Hbd Hbw. change (Z.of_nat (bitSize Word256)) with 256 in Hbw.
           rewrite Kf by exact HV. rewrite HLoadsE by assumption. apply K4. exact HV.
Qed.
