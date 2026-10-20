(** Derive the real allocation/copy/read prefix from initial input frames.
    No helper execution or desired output is an initial premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_encoding C.jet_read16_input_word.
Require Import C.jet_bitmachine_rep.
Require Import C.jet_read32s_layout C.jet_word32_chunks C.jet_uint32_array_init.
Require Import C.jet_exec C.jet_elements_support_sha_linkage C.jet_elements_support_sha_transport C.jet_elements_support_sha_compress_call C.jet_elements_support_sha_block_local.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_calculation_lifecycle_allocation.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Local Opaque elements_ge sha_ge ge0.
Set Default Timeout 10.

Lemma calc_owned_preserved m mf bs zs :
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mf b ofs k p) ->
  (forall b, Mem.valid_block m b -> Mem.valid_block mf b) ->
  Forall2 (fun b z => Mem.range_perm m b 0 z Cur Freeable /\ Mem.valid_block m b) bs zs ->
  Forall2 (fun b z => Mem.range_perm mf b 0 z Cur Freeable /\ Mem.valid_block mf b) bs zs.
Proof.
  intros HP HV HA. induction HA as [|b z bs zs [HB VB] HA IH].
  - constructor.
  - constructor; [split; [intros ofs Ho; apply HP, HB; exact Ho|apply HV; exact VB]|exact IH].
Qed.

Theorem calc_read_prefix m bs sbase bi edge rc (h : Ty.tySem Word256) :
  frame_base_valid sbase -> (8 | sbase) ->
  frame_fields_at m bs sbase bi edge rc ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  frame_input_cells_at m bi edge rc (@encode Word256 h) ->
  exists m1 m2 m3 m4 bl bh br bt bytes mcp mr,
    Mem.alloc m 0 16 = (m1, bl) /\
    Mem.alloc m1 0 32 = (m2, bh) /\
    Mem.alloc m2 0 32 = (m3, br) /\
    Mem.alloc m3 0 32 = (m4, bt) /\
    Mem.loadbytes m4 bs sbase 16 = Some bytes /\
    Mem.storebytes m4 bl 0 bytes = Some mcp /\
    Clight2.eval_funcall elements_ge mcp (Internal f_read32s)
      [Vptr bh Ptrofs.zero; Vlong (Int64.repr 8); Vptr bl Ptrofs.zero] E0 mr Vundef /\
    uint32_array_at mr bh 0 (hash256_reg (to_hash256 h)) /\
    frame_fields_at mr bl 0 bi edge (rc + 256) /\
    mext m mr /\
    (forall b, Mem.valid_block m b -> ~ In b [bl; bh; br; bt]) /\
    NoDup [bl; bh; br; bt] /\
    Forall2 (fun b z => Mem.range_perm mr b 0 z Cur Freeable /\ Mem.valid_block mr b)
      [bl; bh; br; bt] [16; 32; 32; 32].
Proof.
  intros HB HA HF HC HM HI.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  set (hs := word32_chunks 3 h).
  assert (Hlh : length hs = 8%nat) by (apply (word32_chunks_length 3)).
  assert (Hwh : forall j v, nth_error hs j = Some v ->
    frame_input_word_at m bi edge (rc + 32 * Z.of_nat j) v)
    by (apply (frame_input_word32_chunks m bi edge rc 3 h); exact HI).
  assert (HSourceLoad : exists w,
    Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong w)).
  { destruct hs as [|v0 hs'] eqn:Ehs; [discriminate Hlh|].
    pose proof (Hwh 0%nat v0 eq_refl) as Hw0.
    pose proof (Hw0 O _ (@frame_input_word_bits_nth 5 v0 O ltac:(vm_compute; lia))) as Hhead.
    replace (rc + 32 * Z.of_nat 0 + Z.of_nat 0) with rc in Hhead by lia.
    destruct Hhead as [_ [_ [w [HL _]]]]. exists w. exact HL. }
  destruct HSourceLoad as [sourceword HSourceLoad].
  destruct HF as [HSE HSO].
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HBytes].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HBytes) as HLen.
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (Vi : Mem.valid_block m bi) by (eapply load_valid_block; exact HSourceLoad).
  destruct (Mem.alloc m 0 16) as [m1 bl] eqn:A1.
  destruct (Mem.alloc m1 0 32) as [m2 bh] eqn:A2.
  destruct (Mem.alloc m2 0 32) as [m3 br] eqn:A3.
  destruct (Mem.alloc m3 0 32) as [m4 bt] eqn:A4.
  assert (AL : calc_alloc_list m [16; 32; 32; 32] = (m4, [bl; bh; br; bt])).
  { cbn [calc_alloc_list]. rewrite A1. cbn [calc_alloc_list]. rewrite A2.
    cbn [calc_alloc_list]. rewrite A3. cbn [calc_alloc_list]. rewrite A4. reflexivity. }
  destruct (calc_alloc_list_props _ _ _ _ AL) as (X & Fresh & ND & Owned).
  destruct X as (XV & XL & XP & XA).
  pose proof (mext_alloc _ _ _ _ _ A1) as X1.
  pose proof (mext_alloc _ _ _ _ _ A2) as X2.
  pose proof (mext_alloc _ _ _ _ _ A3) as X3.
  assert (HB4 : Mem.loadbytes m4 bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [|exact A4|apply (proj1 X3), (proj1 X2), (proj1 X1); exact Vs].
    erewrite Mem.loadbytes_alloc_unchanged; [|exact A3|apply (proj1 X2), (proj1 X1); exact Vs].
    erewrite Mem.loadbytes_alloc_unchanged; [|exact A2|apply (proj1 X1); exact Vs].
    erewrite Mem.loadbytes_alloc_unchanged; [exact HBytes|exact A1|exact Vs]. }
  assert (Fl : forall b, Mem.valid_block m b -> b <> bl).
  { intros b V E; subst b. apply (Fresh bl V). left; reflexivity. }
  assert (Fh : forall b, Mem.valid_block m b -> b <> bh).
  { intros b V E; subst b. apply (Fresh bh V). right; left; reflexivity. }
  assert (Hlh' : bl <> bh).
  { intro E; subst bh. inversion ND as [|x xs Hnot Hnd]. apply Hnot. left; reflexivity. }
  assert (PL : Mem.range_perm m4 bl 0 16 Cur Freeable).
  { inversion Owned as [|b z bs' zs' Hpair Htail]. exact (proj1 Hpair). }
  assert (PH : Mem.range_perm m4 bh 0 32 Cur Freeable).
  { inversion Owned as [|b z bs' zs' Hpair Htail].
    inversion Htail as [|b' z' bs'' zs'' Hpair' Htail']. exact (proj1 Hpair'). }
  assert (PLW : Mem.range_perm m4 bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLen. change (Mem.range_perm m4 bl 0 16 Cur Writable).
    intros ofs Ho. eapply Mem.perm_implies; [apply PL; exact Ho|constructor]. }
  destruct (Mem.range_perm_storebytes m4 bl 0 bytes PLW) as [mcp SC].
  assert (HSE4 : Mem.load Mptr m4 bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSO4 : Mem.load Mint64 m4 bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_copy_fields_at m4 mcp bs sbase bl bytes _ _ HB4 SC HSE4 HSO4) as [HLE HLO].
  assert (K0 : forall ch b ofs, Mem.valid_block m b ->
    Mem.load ch mcp b ofs = Mem.load ch m b ofs).
  { intros ch b ofs V. erewrite Mem.load_storebytes_other; [|exact SC|left; apply Fl; exact V].
    apply XL; exact V. }
  assert (P0 : forall b ofs k p, Mem.perm m4 b ofs k p -> Mem.perm mcp b ofs k p).
  { intros b ofs k p H. eapply Mem.perm_storebytes_1; eauto. }
  assert (V0 : forall b, Mem.valid_block m4 b -> Mem.valid_block mcp b).
  { intros b V. eapply Mem.storebytes_valid_block_1; eauto. }
  assert (PLC : Mem.valid_access mcp Mint64 bl 8 Writable).
  { split; [|exists 1; reflexivity]. intros ofs Ho. apply P0.
    eapply Mem.perm_implies with (p1 := Freeable); [apply PL; cbn in Ho; lia|constructor]. }
  assert (Hwh0 : forall j v, nth_error hs j = Some v ->
    frame_input_word_at mcp bi edge (rc + 32 * Z.of_nat j) v).
  { intros j v H. eapply frame_input_bits_at_preserved; [|exact (Hwh j v H)].
    intros ofs w HL. rewrite K0 by exact Vi. exact HL. }
  destruct (eval_read32s_layout mcp bh 0 bl 0 bi edge rc hs
    ltac:(lia) ltac:(rewrite Hlh; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(exists 0; reflexivity)
    ltac:(rewrite Hlh; intros ofs Ho; apply P0; eapply Mem.perm_implies; [apply PH; lia|constructor])
    Hlh' ltac:(intro E; apply (Fl bi Vi); congruence) ltac:(intro E; apply (Fh bi Vi); congruence)
    HLocalBase HC ltac:(rewrite Hlh; lia) (conj HLE HLO) PLC Hwh0)
    as (mr & Hread & HArr & HFields & HMem & HPerm & HValid).
  rewrite Hlh in Hread, HFields.
  change (rc + 32 * Z.of_nat 8) with (rc + 256) in HFields.
  assert (K1 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch mr b ofs = Mem.load ch m b ofs).
  { intros ch b ofs V. rewrite HMem by (left; first [apply Fl|apply Fh]; exact V). apply K0; exact V. }
  assert (V1 : forall b, Mem.valid_block m b -> Mem.valid_block mr b).
  { intros b V. apply HValid, V0, XV; exact V. }
  assert (P1 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mr b ofs k p).
  { intros b ofs k p H. apply HPerm, P0, XP; exact H. }
  assert (Xr : mext m mr).
  { split; [exact V1|]. split; [exact K1|]. split; [exact P1|].
    intros ch b ofs p [HP HA']. split; [intros ofs' Ho; apply P1, HP; exact Ho|exact HA']. }
  exists m1, m2, m3, m4, bl, bh, br, bt, bytes, mcp, mr.
  split; [reflexivity|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|].
  split; [exact HB4|]. split; [exact SC|]. split.
  - rewrite <- elements_sha_genv. eapply sha_transport_call; [|exact Hread].
    unfold sha_core_helpers. simpl. tauto.
  - split; [rewrite hash256_reg_chunks; exact HArr|].
    split; [exact HFields|]. split; [exact Xr|]. split; [exact Fresh|]. split; [exact ND|].
    eapply calc_owned_preserved; [| |exact Owned].
    + intros b ofs k p H. apply HPerm, P0; exact H.
    + intros b V. apply HValid, V0; exact V.
Qed.
