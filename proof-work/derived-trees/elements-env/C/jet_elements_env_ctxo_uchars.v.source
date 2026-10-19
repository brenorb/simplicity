(** [sha256_uchars] for a context whose output is an arbitrary writable
    location ([ctxo]): the context absorbs a readable byte range.  Derived
    from the accepted [eval_sha256_uchars]; conditional on [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_u32be_exec.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_uchar_exec.
Require Import C.jet_sha_ctx_abs C.jet_elements_env_ctxo.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Ltac ctxo_side_u :=
  first [eassumption | reflexivity
        | (change Int64.max_unsigned with 18446744073709551615; lia)
        | (change Ptrofs.max_unsigned with 18446744073709551615; lia)
        | lia | (exists 0; reflexivity)].

Section More.
Variable Hmodel : memcpy_model.
Variables (bx bo : block) (obase : Z).
Hypothesis Hox : bo <> bx.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgo : GC <> bo.
Hypothesis Hcx : GM <> bx.
Hypothesis Hco : GM <> bo.
Hypothesis Hob : 0 <= obase /\ obase + 32 <= Ptrofs.max_unsigned.

Theorem ctxo_uchars m ba oa l regs (bs : list int) c ovf :
  ctxo m bx bo obase l regs c ovf -> ba <> bx -> ba <> bo ->
  Ptrofs.unsigned oa + Z.of_nat (length bs) <= Ptrofs.max_unsigned ->
  (forall i, (i < length bs)%nat ->
     Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa + Z.of_nat i) = Some (Vint (nth i bs Int.zero))) ->
  let vn := Int64.repr (Z.of_nat (length bs)) in
  let ovf' := uc_overflow ovf c vn in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_uchars)
      [Vptr bx (Ptrofs.repr 0); Vptr ba oa; Vlong vn] E0 m' (Vint (bit_int (negb ovf'))) /\
    ctxo m' bx bo obase (fst (absorb_i l regs bs)) (snd (absorb_i l regs bs)) (Int64.add c vn) ovf' /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HA Hax Hao HaM HBs vn ovf'.
  pose proof HA as (HOut & HCnt & HOvf & HBlk & HRegs & HMod & HLen & Hr & PX & Hdisp & HMax).
  destruct Hob as [Hob1 Hob2].
  pose proof (Ptrofs.unsigned_range oa) as HoaR.
  assert (PW : Mem.range_perm m bx (0 + 8) (0 + 81) Cur Writable).
  { intros ofs Hr0. eapply Mem.perm_implies; [apply PX; lia|constructor]. }
  pose proof (eval_sha256_uchars Hmodel m bx 0 bo obase ba oa l regs bs c ovf
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    Hob1 Hob2 Hox Hax Hao Hgx Hgo HaM Hr HOut HCnt HMod HOvf HBlk HRegs HBs Hdisp HMax PW
    ltac:(exists 0; reflexivity)) as HU.
  cbv zeta in HU.
  destruct HU as (m' & HUc & HOut' & HCnt' & HOvf' & HBlk' & HReg' & HMem' & HPerm' & HVal').
  exists m'. split; [exact HUc|]. split.
  { eapply ctxo_step with (m := m) (n := Z.of_nat (length bs)); try eassumption; try reflexivity.
    change Int64.max_unsigned with 18446744073709551615.
    change Ptrofs.max_unsigned with 18446744073709551615 in HaM. lia. }
  split; [|split; [exact HPerm'|exact HVal']].
  intros ch b ofs Hv H1 H2. apply HMem'; [exact Hv|left; exact H1|exact H2].
Qed.
End More.
