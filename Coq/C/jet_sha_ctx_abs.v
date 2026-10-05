(** A local SHA-256 context as an abstract absorbing state, with the two
    absorbing calls [sha256_uchars] and [sha256_uchar] as transitions over
    the byte-list model [absorb].  Conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep C.jet_read8s_layout.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_compress_uchar C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_ctx8_bridge C.jet_sha_add_n_exec C.jet_sha_uchar_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Notation GC := (sha_symbol_block _simplicity_sha256_compression).
Notation GM := (sha_symbol_block _sha256_max_counter).

Definition ctx_abs (m : mem) (bx bm : block) (l : list (Ty.tySem (Word 3))) (regs : list int)
    (c : int64) (ovf : bool) : Prop :=
  Mem.load Mptr m bx 0 = Some (Vptr bm (Ptrofs.repr 0)) /\
  Mem.load Mint64 m bx (0 + 8) = Some (Vlong c) /\
  Mem.load Mint8unsigned m bx (0 + 80) = Some (Vint (bit_int ovf)) /\
  (forall i, (i < length (map word8_array_value l))%nat ->
     Mem.load Mint8unsigned m bx (0 + 16 + Z.of_nat i) =
       Some (Vint (nth i (map word8_array_value l) Int.zero))) /\
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bm (0 + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero))) /\
  Int64.unsigned c mod 64 = Z.of_nat (length l) /\ (length l < 64)%nat /\ length regs = 8%nat /\
  Mem.range_perm m bx 0 88 Cur Freeable /\ Mem.range_perm m bm 0 32 Cur Freeable /\
  sha_dispatch_ok m /\ Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter).

Lemma ctx_abs_fst (A B : Type) (a : A) (b : B) : fst (a, b) = a.
Proof. reflexivity. Qed.
Lemma ctx_abs_snd (A B : Type) (a : A) (b : B) : snd (a, b) = b.
Proof. reflexivity. Qed.

Lemma absorb_i_fst l regs bs :
  fst (absorb_i (map word8_array_value l) regs (map word8_array_value bs)) =
    map word8_array_value (fst (absorb l regs bs)).
Proof. rewrite absorb_i_map. apply ctx_abs_fst. Qed.

Lemma absorb_i_snd l regs bs :
  snd (absorb_i (map word8_array_value l) regs (map word8_array_value bs)) = snd (absorb l regs bs).
Proof. rewrite absorb_i_map. apply ctx_abs_snd. Qed.

Lemma absorb_app l regs bs1 bs2 :
  absorb (fst (absorb l regs bs1)) (snd (absorb l regs bs1)) bs2 = absorb l regs (bs1 ++ bs2).
Proof.
  unfold absorb. rewrite fold_left_app.
  destruct (fold_left absorb_step bs1 (l, regs)) as [l1 r1]. reflexivity.
Qed.

Lemma counter_mod_add (c : int64) (n len : Z) :
  0 <= n <= Int64.max_unsigned -> Int64.unsigned c mod 64 = len ->
  Int64.unsigned (Int64.add c (Int64.repr n)) mod 64 = (len + n) mod 64.
Proof.
  intros Hn Hc. unfold Int64.add. rewrite (Int64.unsigned_repr n) by exact Hn.
  rewrite Int64.unsigned_repr_eq.
  rewrite <- (Zmod_div_mod 64 Int64.modulus) by
    (try (exists 288230376151711744; reflexivity); reflexivity).
  rewrite <- Z.add_mod_idemp_l by lia. rewrite Hc. reflexivity.
Qed.

Section Step.
Variables (bx bm : block).
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Lemma ctx_abs_frame m m' l regs c ovf :
  ctx_abs m bx bm l regs c ovf ->
  (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm -> Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
  (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) ->
  Mem.range_perm m' bx 0 88 Cur Freeable /\ Mem.range_perm m' bm 0 32 Cur Freeable /\
  sha_dispatch_ok m' /\ Mem.load Mint64 m' GM 0 = Some (Vlong sha_max_counter).
Proof.
  intros (HOut & _ & _ & _ & HRegs & _ & _ & _ & PX & PM & Hdisp & HMax) HL HP.
  assert (Vx : Mem.valid_block m bx) by (eapply load_valid_block; exact HOut).
  assert (Vm : Mem.valid_block m bm) by (eapply load_valid_block; exact (HRegs 0%nat ltac:(lia))).
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  split; [intros ofs Hr; apply HP; [exact Vx|apply PX; exact Hr]|].
  split; [intros ofs Hr; apply HP; [exact Vm|apply PM; exact Hr]|].
  split.
  - unfold sha_dispatch_ok. rewrite HL by assumption. exact Hdisp.
  - rewrite HL by assumption. exact HMax.
Qed.

Theorem ctx_abs_uchars (Hmodel : memcpy_model) m ba oa l regs (bs : list (Ty.tySem (Word 3))) c ovf :
  ctx_abs m bx bm l regs c ovf ->
  ba <> bx -> ba <> bm ->
  Ptrofs.unsigned oa + Z.of_nat (length bs) <= Ptrofs.max_unsigned ->
  (forall i, (i < length (map word8_array_value bs))%nat ->
     Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa + Z.of_nat i) =
       Some (Vint (nth i (map word8_array_value bs) Int.zero))) ->
  let vn := Int64.repr (Z.of_nat (length bs)) in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchars)
      [Vptr bx (Ptrofs.repr 0); Vptr ba oa; Vlong vn] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctx_abs m' bx bm (fst (absorb l regs bs)) (snd (absorb l regs bs)) (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA Hax Ham HaM HBs vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (Ptrofs.unsigned_range oa) as HOA.
  pose proof (eval_sha256_uchars Hmodel m bx 0 bm 0 ba oa (map word8_array_value l) regs
    (map word8_array_value bs) c ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hax Ham Hgx Hgm) as HU.
  cbv zeta in HU. rewrite !map_length in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  { exact HaM. }
  { exact Hr. }
  { exact HOut. }
  { exact HCnt. }
  { exact HMod. }
  { exact HOvf. }
  { intros i Hi. apply HBlk. rewrite map_length. exact Hi. }
  { intros i Hi. split; [apply HRegs; exact Hi|].
    split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; lia].
    intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
    eapply Mem.perm_implies; [apply PM; lia|constructor]. }
  { intros i Hi. apply HBs. rewrite map_length. exact Hi. }
  { exact Hdisp. }
  { exact HMax. }
  { intros ofs Hr0. eapply Mem.perm_implies; [apply PX; lia|constructor]. }
  { exists 0. reflexivity. }
  assert (HL' : forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
    Mem.load ch m' b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hv H1 H2. apply HMem'; [exact Hv|left; exact H1|left; exact H2]. }
  destruct (ctx_abs_frame m m' l regs c ovf HA HL' HPerm') as (PX' & PM' & Hdisp' & HMax').
  destruct (absorb_length bs l regs HLen) as [HlenA HltA].
  rewrite absorb_i_fst in HBlk'. rewrite absorb_i_snd in HReg'.
  exists m'. split; [exact HUc|]. split; [|split; [exact HL'|split; [exact HPerm'|exact HVal']]].
  split; [exact HOut'|]. split; [exact HCnt'|]. split; [exact HOvf'|]. split; [exact HBlk'|].
  split; [exact HReg'|]. split.
  { rewrite HlenA. apply counter_mod_add; [|exact HMod].
    change Int64.max_unsigned with 18446744073709551615.
    change Ptrofs.max_unsigned with 18446744073709551615 in HaM. lia. }
  split; [exact HltA|]. split; [apply absorb_regs_length; [exact HLen|exact Hr]|].
  split; [exact PX'|]. split; [exact PM'|]. split; [exact Hdisp'|exact HMax'].
Qed.

Theorem ctx_abs_uchar (Hmodel : memcpy_model) m l regs (x : Ty.tySem (Word 3)) c ovf :
  ctx_abs m bx bm l regs c ovf ->
  let vn := Int64.repr 1 in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar)
      [Vptr bx (Ptrofs.repr 0); Vint (word8_array_value x)] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctx_abs m' bx bm (fst (absorb l regs [x])) (snd (absorb l regs [x])) (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (eval_sha256_uchar Hmodel m bx 0 bm 0 (map word8_array_value l) regs
    (word8_array_value x) c ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hgx Hgm (word8_array_value_zero_ext x)) as HU.
  cbv zeta in HU. rewrite !map_length in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  { exact Hr. }
  { exact HOut. }
  { exact HCnt. }
  { exact HMod. }
  { exact HOvf. }
  { intros i Hi. apply HBlk. rewrite map_length. exact Hi. }
  { intros i Hi. split; [apply HRegs; exact Hi|].
    split; [|exists (Z.of_nat i); change (align_chunk Mint32) with 4; lia].
    intros ofs Hr0. change (size_chunk Mint32) with 4 in Hr0.
    eapply Mem.perm_implies; [apply PM; lia|constructor]. }
  { exact Hdisp. }
  { exact HMax. }
  { intros ofs Hr0. eapply Mem.perm_implies; [apply PX; lia|constructor]. }
  { exists 0. reflexivity. }
  assert (HL' : forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
    Mem.load ch m' b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hv H1 H2. apply HMem'; [exact Hv|left; exact H1|left; exact H2]. }
  destruct (ctx_abs_frame m m' l regs c ovf HA HL' HPerm') as (PX' & PM' & Hdisp' & HMax').
  destruct (absorb_length [x] l regs HLen) as [HlenA HltA].
  change [word8_array_value x] with (map word8_array_value [x]) in HBlk', HReg'.
  rewrite absorb_i_fst in HBlk'. rewrite absorb_i_snd in HReg'.
  exists m'. split; [exact HUc|]. split; [|split; [exact HL'|split; [exact HPerm'|exact HVal']]].
  split; [exact HOut'|]. split; [exact HCnt'|]. split; [exact HOvf'|]. split; [exact HBlk'|].
  split; [exact HReg'|]. split.
  { rewrite HlenA. apply counter_mod_add; [|exact HMod].
    change Int64.max_unsigned with 18446744073709551615. cbn. lia. }
  split; [exact HltA|]. split; [apply absorb_regs_length; [exact HLen|exact Hr]|].
  split; [exact PX'|]. split; [exact PM'|]. split; [exact Hdisp'|exact HMax'].
Qed.

End Step.
