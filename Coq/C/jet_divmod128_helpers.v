(** Compose the two actual 96/64 helper calls used by DivMod128_64.
    Public function entry, reader/writer calls and canonical equality are separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Events.
Require Import C.jets C.jet_exec C.jet_divmod96_value C.jet_divmod96_layout.
Import Values Mem Ctypes ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_divmod128_helpers m bqh qoh bql qol br ro ah am al b :
  Int64.modulus <= 2 * Int64.unsigned b -> Int64.unsigned ah < Int64.unsigned b ->
  Int64.unsigned am < divmod96_radix -> Int64.unsigned al < divmod96_radix ->
  Mem.valid_access m Mint64 bqh (Ptrofs.unsigned qoh) Writable ->
  Mem.valid_access m Mint64 bql (Ptrofs.unsigned qol) Writable ->
  Mem.valid_access m Mint64 br (Ptrofs.unsigned ro) Writable ->
  (bqh <> bql \/ Ptrofs.unsigned qoh + 8 <= Ptrofs.unsigned qol \/
    Ptrofs.unsigned qol + 8 <= Ptrofs.unsigned qoh) ->
  (bqh <> br \/ Ptrofs.unsigned qoh + 8 <= Ptrofs.unsigned ro \/
    Ptrofs.unsigned ro + 8 <= Ptrofs.unsigned qoh) ->
  (bql <> br \/ Ptrofs.unsigned qol + 8 <= Ptrofs.unsigned ro \/
    Ptrofs.unsigned ro + 8 <= Ptrofs.unsigned qol) ->
  exists m1 mf qh ql r1 rf,
    Clight2.eval_funcall ge0 m (Internal f_div_mod_96_64)
      [Vptr bqh qoh; Vptr br ro; Vlong ah; Vlong am; Vlong b] E0 m1 Vundef /\
    Mem.load Mint64 m1 br (Ptrofs.unsigned ro) = Some (Vlong r1) /\
    Clight2.eval_funcall ge0 m1 (Internal f_div_mod_96_64)
      [Vptr bql qol; Vptr br ro; Vlong r1; Vlong al; Vlong b] E0 mf Vundef /\
    Mem.load Mint64 mf bqh (Ptrofs.unsigned qoh) = Some (Vlong qh) /\
    Mem.load Mint64 mf bql (Ptrofs.unsigned qol) = Some (Vlong ql) /\
    Mem.load Mint64 mf br (Ptrofs.unsigned ro) = Some (Vlong rf) /\
    0 <= Int64.unsigned qh < divmod96_radix /\
    0 <= Int64.unsigned ql < divmod96_radix /\
    0 <= Int64.unsigned rf < Int64.unsigned b /\
    (Int64.unsigned ah * divmod96_radix + Int64.unsigned am) * divmod96_radix + Int64.unsigned al =
      (Int64.unsigned qh * divmod96_radix + Int64.unsigned ql) * Int64.unsigned b + Int64.unsigned rf /\
    (forall chunk bb addr,
      (bb <> bqh \/ addr + size_chunk chunk <= Ptrofs.unsigned qoh \/ Ptrofs.unsigned qoh + 8 <= addr) ->
      (bb <> bql \/ addr + size_chunk chunk <= Ptrofs.unsigned qol \/ Ptrofs.unsigned qol + 8 <= addr) ->
      (bb <> br \/ addr + size_chunk chunk <= Ptrofs.unsigned ro \/ Ptrofs.unsigned ro + 8 <= addr) ->
      Mem.load chunk mf bb addr = Mem.load chunk m bb addr) /\
    (forall bb addr kind p, Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros Hnorm Hah Ham Hal HPH HPL HPR HsepHL HsepHR HsepLR.
  destruct (eval_divmod96_layout m bqh qoh br ro ah am b Hnorm Hah Ham HPH HPR HsepHR)
    as (m1 & qh & r1 & Hcall1 & HQH & HR1 & HQh & Hr1 & Hbalance1 & Hloads1 & Hperms1 & Hnext1).
  assert (HPL1 : Mem.valid_access m1 Mint64 bql (Ptrofs.unsigned qol) Writable).
  { destruct HPL as [HP Halign]. split; [|exact Halign].
    intros addr Haddr. apply Hperms1. apply HP. exact Haddr. }
  assert (HPR1 : Mem.valid_access m1 Mint64 br (Ptrofs.unsigned ro) Writable).
  { destruct HPR as [HP Halign]. split; [|exact Halign].
    intros addr Haddr. apply Hperms1. apply HP. exact Haddr. }
  destruct (eval_divmod96_layout m1 bql qol br ro r1 al b Hnorm (proj2 Hr1) Hal HPL1 HPR1 HsepLR)
    as (mf & ql & rf & Hcall2 & HQL & HRF & HQl & Hrf & Hbalance2 & Hloads2 & Hperms2 & Hnext2).
  assert (HQHf : Mem.load Mint64 mf bqh (Ptrofs.unsigned qoh) = Some (Vlong qh)).
  { rewrite Hloads2; [exact HQH|exact HsepHL|exact HsepHR]. }
  assert (Hbalance : (Int64.unsigned ah * divmod96_radix + Int64.unsigned am) * divmod96_radix +
      Int64.unsigned al = (Int64.unsigned qh * divmod96_radix + Int64.unsigned ql) * Int64.unsigned b +
      Int64.unsigned rf) by nia.
  exists m1, mf, qh, ql, r1, rf.
  do 10 (split; [assumption|]). split.
  - intros chunk bb addr HoutH HoutL HoutR.
    rewrite Hloads2 by assumption. apply Hloads1; assumption.
  - split.
    + intros bb addr kind p HP. apply Hperms2, Hperms1; exact HP.
    + rewrite Hnext2. exact Hnext1.
Qed.
