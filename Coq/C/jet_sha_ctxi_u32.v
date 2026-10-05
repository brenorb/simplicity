(** The [sha256_u32be] transition of a local SHA-256 context. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_exec C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_u32be_exec.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_ctx_abs C.jet_sha_ctxi.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Section Step.
Variables (bx bm : block).
Hypothesis Hmx : bm <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgm : GC <> bm.
Hypothesis Hcx : GM <> bx.
Hypothesis Hcm : GM <> bm.

Theorem ctxi_u32be (Hmodel : memcpy_model) m l regs (x : int64) c ovf :
  ctxi m bx bm l regs c ovf ->
  let vn := Int64.repr 4 in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_u32be)
      [Vptr bx (Ptrofs.repr 0); Vlong x] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctxi m' bx bm (fst (absorb_i l regs (c_be32_bytes x))) (snd (absorb_i l regs (c_be32_bytes x)))
      (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bm ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & PM & Hdisp & HMax).
  pose proof (eval_sha256_u32be Hmodel m bx 0 bm 0 l regs c x ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hmx Hgx Hgm Hr HOut HCnt HMod HOvf HBlk (ctxi_regs_access bx bm Hmx Hgx Hgm Hcx Hcm _ _ _ _ _ HA) Hdisp HMax
    (ctxi_block_perm bx bm Hmx Hgx Hgm Hcx Hcm _ _ _ _ _ HA) ltac:(exists 0; reflexivity)) as HU.
  cbv zeta in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  destruct (ctxi_step bx bm Hmx Hgx Hgm Hcx Hcm m m' l regs c ovf (c_be32_bytes x) 4 ovf' HA
    ltac:(change Int64.max_unsigned with 18446744073709551615; lia)
    eq_refl HOut' HCnt' HOvf' HBlk' HReg' HMem' HPerm') as [HA' HL'].
  exists m'. split; [exact HUc|]. split; [exact HA'|]. split; [exact HL'|].
  split; [exact HPerm'|exact HVal'].
Qed.

End Step.
