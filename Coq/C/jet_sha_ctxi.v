(** A local SHA-256 context as an absorbing state over raw byte values, with
    every context operation of sha256.h as a transition: [sha256_init]
    (with the struct copy of its result), [sha256_uchars], [sha256_uchar],
    [sha256_u64be], [sha256_hash] and [sha256_finalize].  Conditional on
    [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256 sha.common_lemmas.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_exec C.jet_sha_be32_write C.jet_sha_be64_exec.
Require Import C.jet_sha_compress_uchar C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_calls C.jet_sha_uchar_exec C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_tapdata_prep C.jet_sha_ctx_abs.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Lemma absorb_i_cons l regs x bs :
  absorb_i l regs (x :: bs) =
    absorb_i (fst (absorb_step_i (l, regs) x)) (snd (absorb_step_i (l, regs) x)) bs.
Proof. unfold absorb_i. cbn [fold_left]. destruct (absorb_step_i (l, regs) x); reflexivity. Qed.

Lemma absorb_i_len bs : forall l regs, (length l < 64)%nat -> length regs = 8%nat ->
  Z.of_nat (length (fst (absorb_i l regs bs))) = (Z.of_nat (length l) + Z.of_nat (length bs)) mod 64 /\
  (length (fst (absorb_i l regs bs)) < 64)%nat /\ length (snd (absorb_i l regs bs)) = 8%nat.
Proof.
  induction bs as [|x bs IH]; intros l regs HL HR.
  - unfold absorb_i. cbn [fold_left fst snd length]. rewrite Z.add_0_r, Z.mod_small by lia. auto.
  - rewrite absorb_i_cons. unfold absorb_step_i. cbv zeta. cbn [fst snd].
    destruct (Nat.eqb (length (l ++ [x])) 64) eqn:E; cbn [fst snd].
    + apply Nat.eqb_eq in E. rewrite app_length in E. cbn [length] in E.
      destruct (IH [] (SHA256.hash_block regs (be_words (l ++ [x])))) as (H1 & H2 & H3).
      * cbn. lia.
      * apply sha.common_lemmas.length_hash_block; [exact HR|].
        apply be_words_length. rewrite app_length. cbn [length]. lia.
      * split; [|split; assumption]. rewrite H1. cbn [length].
        replace (Z.of_nat (length l) + Z.of_nat (S (length bs))) with
          (Z.of_nat 0 + Z.of_nat (length bs) + 1 * 64) by lia.
        rewrite Z.mod_add by lia. reflexivity.
    + apply Nat.eqb_neq in E. rewrite app_length in E. cbn [length] in E.
      destruct (IH (l ++ [x]) regs) as (H1 & H2 & H3).
      * rewrite app_length. cbn [length]. lia.
      * exact HR.
      * split; [|split; assumption]. rewrite H1, app_length. cbn [length]. f_equal. lia.
Qed.

Definition ctxi (m : mem) (bx bm : block) (l regs : list int) (c : int64) (ovf : bool) : Prop :=
  Mem.load Mptr m bx 0 = Some (Vptr bm (Ptrofs.repr 0)) /\
  Mem.load Mint64 m bx (0 + 8) = Some (Vlong c) /\
  Mem.load Mint8unsigned m bx (0 + 80) = Some (Vint (bit_int ovf)) /\
  (forall i, (i < length l)%nat ->
     Mem.load Mint8unsigned m bx (0 + 16 + Z.of_nat i) = Some (Vint (nth i l Int.zero))) /\
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bm (0 + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero))) /\
  Int64.unsigned c mod 64 = Z.of_nat (length l) /\ (length l < 64)%nat /\ length regs = 8%nat /\
  Mem.range_perm m bx 0 88 Cur Freeable /\ Mem.range_perm m bm 0 32 Cur Freeable /\
  sha_dispatch_ok m /\ Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter).

Lemma ctxi_other m m' bx bm l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  (forall ch b ofs, b = bx \/ b = bm \/ b = GC \/ b = GM -> Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
  (forall b ofs k p, b = bx \/ b = bm -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) ->
  ctxi m' bx bm l regs c ovf.
Proof.
  intros (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax) HL HP.
  split; [rewrite HL by tauto; exact HOut|]. split; [rewrite HL by tauto; exact HCnt|].
  split; [rewrite HL by tauto; exact HOvf|].
  split; [intros i Hi; rewrite HL by tauto; apply HBlk; exact Hi|].
  split; [intros i Hi; rewrite HL by tauto; apply HRegs; exact Hi|].
  split; [exact HMod|]. split; [exact HLen|]. split; [exact Hr|].
  split; [intros ofs Hr0; apply HP; [tauto|apply PX, Hr0]|].
  split; [intros ofs Hr0; apply HP; [tauto|apply PM, Hr0]|].
  split; [unfold sha_dispatch_ok; rewrite HL by tauto; exact Hdisp|rewrite HL by tauto; exact HMax].
Qed.

Section Step.
Variables (bx bm : block).
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Lemma ctxi_valid m l regs c ovf : ctxi m bx bm l regs c ovf ->
  Mem.valid_block m bx /\ Mem.valid_block m bm /\ Mem.valid_block m GC /\ Mem.valid_block m GM.
Proof.
  intros (HOut & _ & _ & _ & HRegs & _ & _ & _ & _ & _ & Hdisp & HMax).
  split; [eapply load_valid_block; exact HOut|].
  split; [eapply load_valid_block; exact (HRegs 0%nat ltac:(lia))|].
  split; eapply load_valid_block; eassumption.
Qed.

Lemma ctxi_regs_access m l regs c ovf : ctxi m bx bm l regs c ovf ->
  forall i, (i < 8)%nat ->
    Mem.load Mint32 m bm (0 + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero)) /\
    Mem.valid_access m Mint32 bm (0 + 4 * Z.of_nat i) Writable.
Proof.
  intros (_ & _ & _ & _ & HRegs & _ & _ & _ & _ & PM & _) i Hi.
  split; [apply HRegs; exact Hi|].
  split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; lia].
  intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
  eapply Mem.perm_implies; [apply PM; lia|constructor].
Qed.

Lemma ctxi_block_perm m l regs c ovf : ctxi m bx bm l regs c ovf ->
  Mem.range_perm m bx (0 + 8) (0 + 81) Cur Writable.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & PX & _) ofs Hr0.
  eapply Mem.perm_implies; [apply PX; lia|constructor].
Qed.

(** The state after an absorbing call, from the facts every such call
    establishes. *)
Lemma ctxi_step m m' l regs c ovf (bs : list int) (n : Z) ovf' :
  ctxi m bx bm l regs c ovf ->
  0 <= n <= Int64.max_unsigned -> Z.of_nat (length bs) = n ->
  Mem.load Mptr m' bx 0 = Some (Vptr bm (Ptrofs.repr 0)) ->
  Mem.load Mint64 m' bx (0 + 8) = Some (Vlong (Int64.add c (Int64.repr n))) ->
  Mem.load Mint8unsigned m' bx (0 + 80) = Some (Vint (bit_int ovf')) ->
  (forall i, (i < length (fst (absorb_i l regs bs)))%nat ->
     Mem.load Mint8unsigned m' bx (0 + 16 + Z.of_nat i) =
       Some (Vint (nth i (fst (absorb_i l regs bs)) Int.zero))) ->
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m' bm (0 + 4 * Z.of_nat i) =
       Some (Vint (nth i (snd (absorb_i l regs bs)) Int.zero))) ->
  (forall ch b ofs, Mem.valid_block m b ->
     (b <> bx \/ ofs + size_chunk ch <= 0 + 8 \/ 0 + 81 <= ofs) ->
     (b <> bm \/ ofs + size_chunk ch <= 0 \/ 0 + 32 <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
  (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) ->
  ctxi m' bx bm (fst (absorb_i l regs bs)) (snd (absorb_i l regs bs)) (Int64.add c (Int64.repr n)) ovf' /\
  (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs).
Proof.
  intros HA Hn Hlen HOut' HCnt' HOvf' HBlk' HReg' HMem' HPerm'.
  destruct (ctxi_valid _ _ _ _ _ HA) as (Vx & Vm & VG & VM).
  destruct HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  assert (HL' : forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
    Mem.load ch m' b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hv H1 H2. apply HMem'; [exact Hv|left; exact H1|left; exact H2]. }
  destruct (absorb_i_len bs l regs HLen Hr) as (HlenA & HltA & HrA).
  split; [|exact HL'].
  split; [exact HOut'|]. split; [exact HCnt'|]. split; [exact HOvf'|]. split; [exact HBlk'|].
  split; [exact HReg'|]. split.
  { rewrite HlenA, Hlen. apply counter_mod_add; [exact Hn|exact HMod]. }
  split; [exact HltA|]. split; [exact HrA|].
  split; [intros ofs Hr0; apply HPerm'; [exact Vx|apply PX, Hr0]|].
  split; [intros ofs Hr0; apply HPerm'; [exact Vm|apply PM, Hr0]|].
  split; [unfold sha_dispatch_ok; rewrite HL' by assumption; exact Hdisp|].
  rewrite HL' by assumption. exact HMax.
Qed.

Theorem ctxi_uchars (Hmodel : memcpy_model) m ba oa l regs (bs : list int) c ovf :
  ctxi m bx bm l regs c ovf ->
  ba <> bx -> ba <> bm ->
  Ptrofs.unsigned oa + Z.of_nat (length bs) <= Ptrofs.max_unsigned ->
  (forall i, (i < length bs)%nat ->
     Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa + Z.of_nat i) = Some (Vint (nth i bs Int.zero))) ->
  let vn := Int64.repr (Z.of_nat (length bs)) in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchars)
      [Vptr bx (Ptrofs.repr 0); Vptr ba oa; Vlong vn] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctxi m' bx bm (fst (absorb_i l regs bs)) (snd (absorb_i l regs bs)) (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA Hax Ham HaM HBs vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (Ptrofs.unsigned_range oa) as HOA.
  pose proof (eval_sha256_uchars Hmodel m bx 0 bm 0 ba oa l regs bs c ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hax Ham Hgx Hgm HaM Hr HOut HCnt HMod HOvf HBlk (ctxi_regs_access _ _ _ _ _ HA) HBs Hdisp HMax
    (ctxi_block_perm _ _ _ _ _ HA) ltac:(exists 0; reflexivity)) as HU.
  cbv zeta in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  destruct (ctxi_step m m' l regs c ovf bs (Z.of_nat (length bs)) ovf' HA
    ltac:(change Int64.max_unsigned with 18446744073709551615;
          change Ptrofs.max_unsigned with 18446744073709551615 in HaM; lia)
    eq_refl HOut' HCnt' HOvf' HBlk' HReg' HMem' HPerm') as [HA' HL'].
  exists m'. split; [exact HUc|]. split; [exact HA'|]. split; [exact HL'|].
  split; [exact HPerm'|exact HVal'].
Qed.

Theorem ctxi_uchar (Hmodel : memcpy_model) m l regs (x : int) c ovf :
  ctxi m bx bm l regs c ovf -> Int.zero_ext 8 x = x ->
  let vn := Int64.repr 1 in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar)
      [Vptr bx (Ptrofs.repr 0); Vint x] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctxi m' bx bm (fst (absorb_i l regs [x])) (snd (absorb_i l regs [x])) (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA Hx vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (eval_sha256_uchar Hmodel m bx 0 bm 0 l regs x c ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hgx Hgm Hx Hr HOut HCnt HMod HOvf HBlk (ctxi_regs_access _ _ _ _ _ HA) Hdisp HMax
    (ctxi_block_perm _ _ _ _ _ HA) ltac:(exists 0; reflexivity)) as HU.
  cbv zeta in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  destruct (ctxi_step m m' l regs c ovf [x] 1 ovf' HA
    ltac:(change Int64.max_unsigned with 18446744073709551615; lia)
    eq_refl HOut' HCnt' HOvf' HBlk' HReg' HMem' HPerm') as [HA' HL'].
  exists m'. split; [exact HUc|]. split; [exact HA'|]. split; [exact HL'|].
  split; [exact HPerm'|exact HVal'].
Qed.

Theorem ctxi_u64be (Hmodel : memcpy_model) m l regs (x : int64) c ovf :
  ctxi m bx bm l regs c ovf ->
  let vn := Int64.repr 8 in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_u64be)
      [Vptr bx (Ptrofs.repr 0); Vlong x] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctxi m' bx bm (fst (absorb_i l regs (c_be64_bytes x))) (snd (absorb_i l regs (c_be64_bytes x)))
      (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (eval_sha256_u64be Hmodel m bx 0 bm 0 l regs c x ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hgx Hgm Hr HOut HCnt HMod HOvf HBlk (ctxi_regs_access _ _ _ _ _ HA) Hdisp HMax
    (ctxi_block_perm _ _ _ _ _ HA) ltac:(exists 0; reflexivity)) as HU.
  cbv zeta in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  destruct (ctxi_step m m' l regs c ovf (c_be64_bytes x) 8 ovf' HA
    ltac:(change Int64.max_unsigned with 18446744073709551615; lia)
    eq_refl HOut' HCnt' HOvf' HBlk' HReg' HMem' HPerm') as [HA' HL'].
  exists m'. split; [exact HUc|]. split; [exact HA'|]. split; [exact HL'|].
  split; [exact HPerm'|exact HVal'].
Qed.

Theorem ctxi_hash (Hmodel : memcpy_model) m bt ot l regs (regsH : list int) c ovf :
  ctxi m bx bm l regs c ovf ->
  length regsH = 8%nat -> Ptrofs.unsigned ot + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bt (Ptrofs.unsigned ot + 4 * Z.of_nat j) = Some (Vint (nth j regsH Int.zero))) ->
  let vn := Int64.repr 32 in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_hash)
      [Vptr bx (Ptrofs.repr 0); Vptr bt ot] E0 m' Vundef /\
    ctxi m' bx bm (fst (absorb_i l regs (be_bytes regsH))) (snd (absorb_i l regs (be_bytes regsH)))
      (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA HrH HotM HH vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (eval_sha256_hash Hmodel m bx 0 bm 0 bt ot l regs regsH c ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hgx Hgm Hr HrH HotM HH HOut HCnt HMod HOvf HBlk (ctxi_regs_access _ _ _ _ _ HA) Hdisp HMax
    (ctxi_block_perm _ _ _ _ _ HA) ltac:(exists 0; reflexivity)) as HU.
  cbv zeta in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  destruct (ctxi_step m m' l regs c ovf (be_bytes regsH) 32 ovf' HA
    ltac:(change Int64.max_unsigned with 18446744073709551615; lia)
    ltac:(rewrite be_bytes_length, HrH; reflexivity)
    HOut' HCnt' HOvf' HBlk' HReg' HMem' HPerm') as [HA' HL'].
  exists m'. split; [exact HUc|]. split; [exact HA'|]. split; [exact HL'|].
  split; [exact HPerm'|exact HVal'].
Qed.

Theorem ctxi_finalize (Hmodel : memcpy_model) m l regs c ovf :
  ctxi m bx bm l regs c ovf ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_finalize)
      [Vptr bx (Ptrofs.repr 0)] E0 m' (Vint (bit_int (negb ovf))) /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bm (0 + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs (sha_pad c))) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  destruct (eval_sha256_finalize Hmodel m bx 0 bm 0 l regs c ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hgx Hgm Hcx Hcm Hr HOut HCnt HMod HOvf HBlk (ctxi_regs_access _ _ _ _ _ HA) Hdisp HMax
    (ctxi_block_perm _ _ _ _ _ HA) ltac:(exists 0; reflexivity))
    as (m' & HUc & HReg' & HMem' & HPerm' & HVal').
  exists m'. split; [exact HUc|]. split; [exact HReg'|].
  split; [|split; [exact HPerm'|exact HVal']].
  intros ch b ofs Hv H1 H2. apply HMem'; [exact Hv|left; exact H1|left; exact H2].
Qed.

(** [ctx = sha256_init(arr)]: the call into the result temporary [br] and
    the struct copy into the context [bx]. *)
Theorem ctxi_init m br :
  br <> bm -> br <> bx ->
  Mem.valid_block m GC -> Mem.valid_block m GM -> GC <> br -> GM <> br ->
  Mem.range_perm m br 0 88 Cur Freeable -> Mem.range_perm m bx 0 88 Cur Freeable ->
  Mem.range_perm m bm 0 32 Cur Freeable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists mi mx bytes,
    Clight2.eval_funcall sha_ge m (Internal jets.f_sha256_init)
      [Vptr br Ptrofs.zero; Vptr bm (Ptrofs.repr 0)] E0 mi Vundef /\
    Mem.loadbytes mi br 0 88 = Some bytes /\ Mem.storebytes mi bx 0 bytes = Some mx /\
    ctxi mx bx bm [] sha256_iv_words Int64.zero false /\
    (forall ch b ofs, Mem.valid_block m b -> b <> br -> b <> bx -> b <> bm ->
       Mem.load ch mx b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mx b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mx b).
Proof.
  intros Hrm Hrx VG VM Hgr Hcr PR PX PM Hdisp HMax.
  destruct (sha_init_copy m br bx bm 0 Hrm (not_eq_sym Hmx) Hrx ltac:(lia)
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) ltac:(exists 0; reflexivity))
    as (mi & mx & bytes & HInit & HB & HS & HOut & HCnt & HOvf & HArr & HL & HP & HV).
  { intros ofs Hr0. eapply Mem.perm_implies; [apply PR, Hr0|constructor]. }
  { intros ofs Hr0. eapply Mem.perm_implies; [apply PX, Hr0|constructor]. }
  { intros ofs Hr0. eapply Mem.perm_implies; [apply PM; lia|constructor]. }
  exists mi, mx, bytes. split; [exact HInit|]. split; [exact HB|]. split; [exact HS|].
  split; [|split; [|split; [exact HP|exact HV]]].
  - split; [exact HOut|]. split; [exact HCnt|]. split; [exact HOvf|].
    split; [intros i Hi; cbn in Hi; lia|].
    split; [intros i Hi; apply (jet_sha_add_n_calls.u32_nth mx bm 0 sha256_iv_words HArr); exact Hi|].
    split; [reflexivity|]. split; [cbn; lia|]. split; [reflexivity|].
    split; [intros ofs Hr0; apply HP, PX, Hr0|]. split; [intros ofs Hr0; apply HP, PM, Hr0|].
    split.
    + unfold sha_dispatch_ok. rewrite HL; [exact Hdisp|exact VG|exact Hgr|exact Hgx|left; exact Hgm].
    + rewrite HL; [exact HMax|exact VM|exact Hcr|exact Hcx|left; exact Hcm].
  - intros ch b ofs Hv H1 H2 H3. apply HL; [exact Hv|exact H1|exact H2|left; exact H3].
Qed.

End Step.
