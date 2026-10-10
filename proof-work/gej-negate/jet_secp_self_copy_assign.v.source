(** Derived actual by-copy assignment at identical addresses. No successful
    store, execution or preservation fact is an initial premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Ctypes Clight.
Require Import C.jet_secp_self_copy.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma assign_loc_owned_self_copy ce ty m b ofs :
  access_mode ty = By_copy ->
  0 <= sizeof ce ty ->
  (sizeof ce ty > 0 -> (alignof_blockcopy ce ty | Ptrofs.unsigned ofs)) ->
  Mem.range_perm m b (Ptrofs.unsigned ofs)
    (Ptrofs.unsigned ofs + sizeof ce ty) Cur Writable ->
  exists mf,
    assign_loc ce ty m b ofs Full (Values.Vptr b ofs) mf /\
    Mem.unchanged_on (fun _ _ => True) m mf.
Proof.
  intros HMode HSize HAlign HWritable.
  assert (HReadable : Mem.range_perm m b (Ptrofs.unsigned ofs)
    (Ptrofs.unsigned ofs + sizeof ce ty) Cur Readable).
  { intros i HI. eapply Mem.perm_implies; [apply HWritable; exact HI|constructor]. }
  destruct (Mem.range_perm_loadbytes m b (Ptrofs.unsigned ofs)
    (sizeof ce ty) HReadable) as [bytes HLoad].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLoad) as HLength.
  assert (HBytesWritable : Mem.range_perm m b (Ptrofs.unsigned ofs)
    (Ptrofs.unsigned ofs + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLength, Z2Nat.id by exact HSize; exact HWritable. }
  destruct (Mem.range_perm_storebytes m b (Ptrofs.unsigned ofs) bytes HBytesWritable)
    as [mf HStore].
  exists mf; split.
  - eapply assign_loc_copy with (b' := b) (ofs' := ofs) (bytes := bytes).
    + exact HMode.
    + exact HAlign.
    + exact HAlign.
    + right; left; reflexivity.
    + exact HLoad.
    + exact HStore.
  - eapply self_copy_storebytes_unchanged; eassumption.
Qed.
Print Assumptions assign_loc_owned_self_copy.
